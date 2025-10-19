#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <sstream>
#include <iomanip>
#include <cstdint>
#include <cctype>

using namespace std;

// Key and tables (must match the encryption program)
unsigned long long Key = 0x133457799BBCDFF1ULL;

static const int PC1[56] = {
	57,49,41,33,25,17,9,
	1,58,50,42,34,26,18,
	10,2,59,51,43,35,27,
	19,11,3,60,52,44,36,
	63,55,47,39,31,23,15,
	7,62,54,46,38,30,22,
	14,6,61,53,45,37,29,
	21,13,5,28,20,12,4
};

static const int PC2[48] = {
	14,17,11,24,1,5,
	3,28,15,6,21,10,
	23,19,12,4,26,8,
	16,7,27,20,13,2,
	41,52,31,37,47,55,
	30,40,51,45,33,48,
	44,49,39,56,34,53,
	46,42,50,36,29,32
};

static const int SHIFTS[16] = {1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1};

static const int E_TABLE[48] = {
	32,1,2,3,4,5,
	4,5,6,7,8,9,
	8,9,10,11,12,13,
	12,13,14,15,16,17,
	16,17,18,19,20,21,
	20,21,22,23,24,25,
	24,25,26,27,28,29,
	28,29,30,31,32,1
};

static const int P_TABLE[32] = {
	16,7,20,21,29,12,28,17,
	1,15,23,26,5,18,31,10,
	2,8,24,14,32,27,3,9,
	19,13,30,6,22,11,4,25
};

static const int IP[64] = {
	58,50,42,34,26,18,10,2,
	60,52,44,36,28,20,12,4,
	62,54,46,38,30,22,14,6,
	64,56,48,40,32,24,16,8,
	57,49,41,33,25,17,9,1,
	59,51,43,35,27,19,11,3,
	61,53,45,37,29,21,13,5,
	63,55,47,39,31,23,15,7
};

static const int IP_INV[64] = {
	40,8,48,16,56,24,64,32,
	39,7,47,15,55,23,63,31,
	38,6,46,14,54,22,62,30,
	37,5,45,13,53,21,61,29,
	36,4,44,12,52,20,60,28,
	35,3,43,11,51,19,59,27,
	34,2,42,10,50,18,58,26,
	33,1,41,9,49,17,57,25
};

// Helpers (1-based vectors)
static vector<int> ull_to_bits_msb(unsigned long long v, int n) {
	vector<int> out(n+1);
	for (int i = 1; i <= n; ++i) {
		int shift = n - i;
		out[i] = ((v >> shift) & 1ULL) ? 1 : 0;
	}
	return out;
}

static vector<int> apply_permutation(const vector<int>& in, const int* table, int tlen) {
	vector<int> out(tlen+1);
	for (int i = 0; i < tlen; ++i) out[i+1] = in[ table[i] ];
	return out;
}

static void odd_even_transform(vector<int>& b) {
	int n = (int)b.size()-1;
	for (int j = 1; j <= n; ++j) {
		if (j <= 28) b[j] = (j % 2 == 0) ? 1 : 0;
		else b[j] = (j % 2 == 1) ? 1 : 0;
	}
}

static void rot_left(vector<int>& v, int shifts) {
	int n = (int)v.size()-1;
	if (n == 0) return;
	shifts %= n;
	if (shifts == 0) return;
	vector<int> tmp(n+1);
	for (int i = 1; i <= n; ++i) {
		int src = ((i + shifts - 1) % n) + 1;
		tmp[i] = v[src];
	}
	v = tmp;
}

static void sbox_substitution(const vector<int>& in48, vector<int>& out32) {
	for (int i = 0; i < 8; ++i) {
		int base = i*6;
		int val = 0;
		for (int b = 0; b < 6; ++b) val = (val << 1) | in48[base + b + 1];
		int nibble = ((val * (i+1)) ^ (val >> 2)) & 0xF;
		for (int b = 0; b < 4; ++b) out32[i*4 + b + 1] = ((nibble >> (3 - b)) & 1);
	}
}

static vector<int> feistel_f(const vector<int>& R32, const vector<int>& K48) {
	vector<int> Rexp = apply_permutation(R32, E_TABLE, 48);
	vector<int> tmp(48+1);
	for (int i = 1; i <= 48; ++i) tmp[i] = Rexp[i] ^ K48[i];
	vector<int> sbout(32+1);
	sbox_substitution(tmp, sbout);
	vector<int> pout = apply_permutation(sbout, P_TABLE, 32);
	return pout;
}

static vector<int> des_block_operation(const vector<int>& block64, const vector<vector<int>>& roundKeys) {
	vector<int> ip = apply_permutation(block64, IP, 64);
	vector<int> L(33), R(33);
	for (int i = 1; i <= 32; ++i) { L[i] = ip[i]; R[i] = ip[32 + i]; }
	for (int r = 0; r < 16; ++r) {
		vector<int> f = feistel_f(R, roundKeys[r]);
		vector<int> newR(33);
		for (int i = 1; i <= 32; ++i) newR[i] = L[i] ^ f[i];
		L = R;
		R = newR;
	}
	vector<int> preout(65);
	for (int i = 1; i <= 32; ++i) { preout[i] = R[i]; preout[32 + i] = L[i]; }
	vector<int> out = apply_permutation(preout, IP_INV, 64);
	return out;
}

// bytes <-> bits (MSB first)
static vector<int> bytes_to_bits_msb(const vector<uint8_t>& bytes, size_t start) {
	vector<int> bits(64+1);
	for (int i = 0; i < 8; ++i) {
		uint8_t b = bytes[start + i];
		for (int bit = 0; bit < 8; ++bit) bits[i*8 + bit + 1] = ((b >> (7 - bit)) & 1) ? 1 : 0;
	}
	return bits;
}

static vector<uint8_t> bits64_to_bytes(const vector<int>& bits) {
	vector<uint8_t> out(8,0);
	for (int i = 0; i < 8; ++i) {
		uint8_t b = 0;
		for (int bit = 0; bit < 8; ++bit) b = (b << 1) | (bits[i*8 + bit + 1] & 1);
		out[i] = b;
	}
	return out;
}

int main() {
	// 1) Generate round keys exactly the same as encryption
	vector<int> key64 = ull_to_bits_msb(Key, 64);
	vector<int> key56 = apply_permutation(key64, PC1, 56);
	odd_even_transform(key56);
	vector<int> C(29), D(29);
	for (int i = 1; i <= 28; ++i) { C[i] = key56[i]; D[i] = key56[28 + i]; }

	vector<vector<int>> roundKeysBits;
	for (int round = 0; round < 16; ++round) {
		rot_left(C, SHIFTS[round]);
		rot_left(D, SHIFTS[round]);
		vector<int> CD(57);
		for (int i = 1; i <= 28; ++i) CD[i] = C[i];
		for (int i = 1; i <= 28; ++i) CD[28 + i] = D[i];
		vector<int> K = apply_permutation(CD, PC2, 48);
		roundKeysBits.push_back(K);
	}

	// reverse keys for decryption: feeding reversed keys into same block operation performs decryption
	vector<vector<int>> roundKeysRev = roundKeysBits;
	reverse(roundKeysRev.begin(), roundKeysRev.end());

	// 2) Read ciphertext.txt (hex)
	ifstream infile("ciphertext.txt");
	if (!infile) { cerr << "Cannot open ciphertext.txt\n"; return 1; }
	string all; string line;
	while (getline(infile, line)) {
		// accept only hex digits (ignore whitespace, "0x", labels, etc.)
		for (char c : line) {
			if (isxdigit(static_cast<unsigned char>(c))) all.push_back(c);
		}
	}
	infile.close();

	if (all.empty()) {
		cerr << "ciphertext.txt is empty or contains no hex digits\n";
		// still attempt to create an empty decrypted file below
	}

	// if odd number of hex chars, prepend '0' so pairs are valid
	if (all.size() % 2 != 0) {
		cerr << "Warning: odd-length hex input detected; prepending '0' to parse\n";
		all.insert(all.begin(), '0');
	}

	vector<uint8_t> cipher_bytes;
	cipher_bytes.reserve(all.size()/2);
	for (size_t i = 0; i + 1 < all.size(); i += 2) {
		string bytehex = all.substr(i,2);
		uint8_t b = static_cast<uint8_t>(strtoul(bytehex.c_str(), nullptr, 16));
		cipher_bytes.push_back(b);
	}

	// if ciphertext not multiple of 8 bytes, truncate to nearest lower multiple and warn
	if (cipher_bytes.empty()) {
		cerr << "No cipher bytes parsed; will produce empty decrypted.txt\n";
	}
	if (cipher_bytes.size() % 8 != 0) {
		size_t keep = (cipher_bytes.size() / 8) * 8;
		cerr << "Warning: ciphertext size (" << cipher_bytes.size()
		     << " bytes) not multiple of 8; truncating to " << keep << " bytes\n";
		cipher_bytes.resize(keep);
	}

	// CBC IV = 8 zero bytes (same as encryption)
	vector<uint8_t> iv(8,0), prev_cipher = iv;
	vector<uint8_t> plain_bytes;
	plain_bytes.reserve(cipher_bytes.size());

	for (size_t pos = 0; pos < cipher_bytes.size(); pos += 8) {
		// convert cipher block to bits
		vector<int> cbits = bytes_to_bits_msb(cipher_bytes, pos);
		// decrypt block by running block operation with reversed round keys
		vector<int> dbits = des_block_operation(cbits, roundKeysRev);
		// convert to bytes
		vector<uint8_t> pblock = bits64_to_bytes(dbits);
		// XOR with prev_cipher (CBC)
		for (int i = 0; i < 8; ++i) {
			uint8_t pb = pblock[i] ^ prev_cipher[i];
			plain_bytes.push_back(pb);
		}
		// update prev_cipher to current cipher block
		for (int i = 0; i < 8; ++i) prev_cipher[i] = cipher_bytes[pos + i];
	}

	// remove PKCS#7 padding if valid, otherwise write full plaintext and warn
	if (plain_bytes.empty()) {
		cerr << "No plaintext produced; writing empty decrypted.txt\n";
	} else {
		uint8_t pad = plain_bytes.back();
		bool padding_ok = true;
		if (pad < 1 || pad > 8 || plain_bytes.size() < pad) padding_ok = false;
		else {
			for (size_t i = plain_bytes.size() - pad; i < plain_bytes.size(); ++i) {
				if (plain_bytes[i] != pad) { padding_ok = false; break; }
			}
		}
		if (padding_ok) {
			plain_bytes.resize(plain_bytes.size() - pad);
		} else {
			cerr << "Warning: invalid PKCS#7 padding detected; writing full plaintext without removing padding\n";
		}
	}

	// write decrypted bytes to file (always attempt)
	// 1) write raw binary (exact recovered bytes) for verification/debugging
	{
		ofstream bout("decrypted_raw.bin", ios::binary);
		if (bout) {
			if (!plain_bytes.empty()) bout.write(reinterpret_cast<const char*>(plain_bytes.data()), (streamsize)plain_bytes.size());
			bout.flush();
			bout.close();
		} else {
			cerr << "Warning: cannot open decrypted_raw.bin for writing\n";
		}
	}

	// 2) produce cleaned human-readable text and write to decrypted.txt
	// Keep printable ASCII and common whitespace; replace other bytes with '?'
	string cleaned;
	cleaned.reserve(plain_bytes.size());
	for (uint8_t b : plain_bytes) {
		if (b == '\n' || b == '\r' || b == '\t' || (b >= 32 && b <= 126)) cleaned.push_back(static_cast<char>(b));
		else cleaned.push_back('?'); // or continue to drop non-printable: continue;
	}
	ofstream tout("decrypted.txt"); // text mode
	if (!tout) { cerr << "Cannot open decrypted.txt for writing\n"; return 1; }
	tout << cleaned;
	tout.flush();
	tout.close();

	cout << "Decryption complete. Recovered plaintext written to decrypted.txt\n";
	return 0;
}
