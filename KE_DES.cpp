#include <bitset>
#include <iostream>
#include <vector>
#include <iomanip>
#include <sstream>
#include <cstdint>
#include <fstream>
#include <chrono>

using namespace std;

//Key in hexadecimal format
unsigned long long Key = 0x133457799BBCDFF1ULL;

// PC-1 table (56 positions) - standard DES PC-1 (1-based positions)
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

// PC-2 table (48 positions) - standard DES PC-2 (1-based positions on 56-bit input)
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

// Left rotation schedule for 16 rounds (standard DES)
static const int SHIFTS[16] = {1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1};

// Initial Permutation (IP)
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

// Inverse IP
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

// Expansion table E (32 -> 48)
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

// P permutation (32)
static const int P_TABLE[32] = {
	16,7,20,21,29,12,28,17,
	1,15,23,26,5,18,31,10,
	2,8,24,14,32,27,3,9,
	19,13,30,6,22,11,4,25
};

static vector<int> ull_to_bits_msb(unsigned long long v, int n) {
	vector<int> out(n+1); // 1-based
	for (int i = 1; i <= n; ++i) {
		int shift = n - i;
		out[i] = ( (v >> shift) & 1ULL ) ? 1 : 0;
	}
	return out;
}

static vector<int> apply_permutation(const vector<int>& in, const int* table, int tlen) {
	vector<int> out(tlen+1);
	for (int i = 0; i < tlen; ++i) {
		out[i+1] = in[ table[i] ];
	}
	return out;
}

static void odd_even_transform(vector<int>& b) {
	// produce C0 = 0,1,0,1,... for positions 1..28
	// and    D0 = 1,0,1,0,... for positions 29..56
	int n = (int)b.size()-1;
	for (int j = 1; j <= n; ++j) {
		if (j <= 28) {
			// first half: odd positions = 0, even = 1 -> 0,1,0,1,...
			b[j] = (j % 2 == 0) ? 1 : 0;
		} else {
			// second half: odd positions = 1, even = 0 -> 1,0,1,0,...
			b[j] = (j % 2 == 1) ? 1 : 0;
		}
	}
}

static void rot_left(vector<int>& v, int shifts) {
	// v is 1-based indexed
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

static string bits_to_hex_string(const vector<int>& bits) {
	// bits is 1-based MSB-first; produce hex string
	int n = (int)bits.size()-1;
	unsigned long long val = 0;
	for (int i = 1; i <= n; ++i) {
		val = (val << 1) | (bits[i] & 1);
	}
	int hex_digits = (n + 3) / 4;
	stringstream ss;
	ss << hex << uppercase << setw(hex_digits) << setfill('0') << val;
	return ss.str();
}

// Convert 8 bytes (MSB first) to 1-based 64-bit vector
static vector<int> bytes_to_bits_msb(const vector<uint8_t>& bytes, int start) {
	// start index in bytes vector (0-based); expects at least 8 bytes available
	vector<int> bits(64+1);
	for (int i = 0; i < 8; ++i) {
		uint8_t b = bytes[start + i];
		for (int bit = 0; bit < 8; ++bit) {
			int pos = i*8 + bit; // 0..63
			// MSB-first: bit 0 is highest bit of byte
			bits[pos+1] = ( (b >> (7 - bit)) & 1 ) ? 1 : 0;
		}
	}
	return bits;
}

static vector<uint8_t> bits64_to_bytes(const vector<int>& bits) {
	vector<uint8_t> out(8, 0);
	for (int i = 0; i < 8; ++i) {
		uint8_t b = 0;
		for (int bit = 0; bit < 8; ++bit) {
			int pos = i*8 + bit; // 0..63
			b = (b << 1) | (bits[pos+1] & 1);
		}
		out[i] = b;
	}
	return out;
}

// Simplified S-box substitution: maps each 6-bit value to 4-bit deterministically.
// This keeps the implementation concise; you can replace this with standard DES S-boxes if desired.
static void sbox_substitution(const vector<int>& in48, vector<int>& out32) {
	// in48: 1-based 48 bits; out32 will be 1-based 32 bits
	for (int i = 0; i < 8; ++i) {
		int base = i*6;
		int val = 0;
		for (int b = 0; b < 6; ++b) val = (val << 1) | in48[base + b + 1];
		// deterministic mapping: mix and reduce to 4 bits
		int nibble = ((val * (i+1)) ^ (val >> 2)) & 0xF;
		// put nibble into out32
		for (int b = 0; b < 4; ++b) {
			out32[i*4 + b + 1] = ( (nibble >> (3 - b)) & 1 );
		}
	}
}

// Feistel function f: takes 32-bit R (1-based) and 48-bit subkey (1-based), returns 32-bit vector (1-based)
static vector<int> feistel_f(const vector<int>& R32, const vector<int>& K48) {
	// expand R from 32->48
	vector<int> Rexp = apply_permutation(R32, E_TABLE, 48);
	// XOR with key
	vector<int> tmp(48+1);
	for (int i = 1; i <= 48; ++i) tmp[i] = Rexp[i] ^ K48[i];
	// S-box substitution (simplified)
	vector<int> sbout(32+1);
	sbox_substitution(tmp, sbout);
	// P permutation
	vector<int> pout = apply_permutation(sbout, P_TABLE, 32);
	return pout;
}

// DES-like encrypt single 64-bit block (1-based vector) with provided 16 round keys (each 1-based 48 bits)
static vector<int> des_encrypt_block(const vector<int>& block64, const vector<vector<int>>& roundKeys) {
	// Apply IP
	vector<int> ip = apply_permutation(block64, IP, 64);
	// split L and R
	vector<int> L(32+1), R(32+1);
	for (int i = 1; i <= 32; ++i) { L[i] = ip[i]; R[i] = ip[32 + i]; }

	// 16 rounds
	for (int r = 0; r < 16; ++r) {
		vector<int> f = feistel_f(R, roundKeys[r]);
		vector<int> newR(32+1);
		for (int i = 1; i <= 32; ++i) newR[i] = L[i] ^ f[i];
		L = R;
		R = newR;
	}

	// preoutput is R||L (swap)
	vector<int> preout(64+1);
	for (int i = 1; i <= 32; ++i) {
		preout[i] = R[i];
		preout[32 + i] = L[i];
	}
	// apply IP_INV
	vector<int> out = apply_permutation(preout, IP_INV, 64);
	return out;
}

int main()
{
    //convert the key to 64-bits binary format (MSB-first)
    bitset<64> Key_Bin(Key);
    cout << "Key in binary format: " << Key_Bin << endl;

    // 1) Convert to MSB-first 1-based vector
    vector<int> key64 = ull_to_bits_msb(Key, 64);

    // start timing key generation (PC-1 .. round key generation)
    auto key_gen_start = chrono::high_resolution_clock::now();

    // 2) Apply PC-1 to obtain 56-bit key
    vector<int> key56 = apply_permutation(key64, PC1, 56);
    cout << "After PC-1 (56 bits): ";
    for (int i = 1; i <= 56; ++i) cout << key56[i];
    cout << endl;

    // 3) Apply Odd/Even transform on 56-bit block
    odd_even_transform(key56);
    cout << "After Odd/Even transform (56 bits): ";
    for (int i = 1; i <= 56; ++i) cout << key56[i];
    cout << endl;

    // 4) Split into C0 and D0 (28 bits each)
    vector<int> C(29), D(29); // 1-based sizes 28
    for (int i = 1; i <= 28; ++i) {
    	C[i] = key56[i];
    	D[i] = key56[28 + i];
    }
    cout << "C0: ";
    for (int i = 1; i <= 28; ++i) cout << C[i];
    cout << "\nD0: ";
    for (int i = 1; i <= 28; ++i) cout << D[i];
    cout << endl;

    // 5) Generate K1..K16 using left rotations and PC-2
    vector<string> roundKeysHex;
    vector<vector<int>> roundKeysBits; // store 1-based 48-bit keys
    for (int round = 0; round < 16; ++round) {
    	// left rotate according to schedule
    	rot_left(C, SHIFTS[round]);
    	rot_left(D, SHIFTS[round]);

    	// concatenate C||D into 56-bit
    	vector<int> CD(57);
    	for (int i = 1; i <= 28; ++i) CD[i] = C[i];
    	for (int i = 1; i <= 28; ++i) CD[28 + i] = D[i];

    	// apply PC-2 to get 48-bit key
    	vector<int> K = apply_permutation(CD, PC2, 48);

    	// store hex and bits
    	string hexk = bits_to_hex_string(K);
    	roundKeysHex.push_back(hexk);
    	roundKeysBits.push_back(K);

    	// print round info
    	cout << "K" << (round+1) << " (48 bits) = ";
    	for (int i = 1; i <= 48; ++i) cout << K[i];
    	cout << "  hex: 0x" << hexk << endl;

    	// print K1 generation time (time from key_gen_start to completion of K1)
    	if (round == 0) {
    		auto k1_end = chrono::high_resolution_clock::now();
    		auto k1_ns = chrono::duration_cast<chrono::nanoseconds>(k1_end - key_gen_start).count();
    		double k1_ms = double(k1_ns) / 1e6;
    		cout << fixed << setprecision(3) << "K1 generation time: " << k1_ms << " ms" << endl;
    		cout << defaultfloat;
    	}
    }

    // stop timing key generation (use nanoseconds for sub-millisecond precision)
    auto key_gen_end = chrono::high_resolution_clock::now();
    auto key_gen_ns = chrono::duration_cast<chrono::nanoseconds>(key_gen_end - key_gen_start).count();
    double key_gen_ms = double(key_gen_ns) / 1e6; // milliseconds with fractional part
    cout << fixed << setprecision(3) << "Key generation time: " << key_gen_ms << " ms" << endl;
    cout << defaultfloat; // restore default formatting

    // Optional: list keys summarized
    cout << "\nRound keys (hex):\n";
    for (int i = 0; i < (int)roundKeysHex.size(); ++i) {
    	cout << "K" << (i+1) << ": 0x" << roundKeysHex[i] << "\n";
    }

    // --- New: read plaintext.txt, pad, encrypt in CBC mode, write ciphertext.txt (hex) ---
    const string infile_name = "plaintext.txt";
    const string outfile_name = "ciphertext.txt";

    ifstream infile(infile_name, ios::binary);
    if (!infile) {
    	cerr << "Cannot open " << infile_name << " for reading.\n";
    	return 1;
    }
    vector<uint8_t> plain;
    infile.seekg(0, ios::end);
    size_t fsize = infile.tellg();
    infile.seekg(0, ios::beg);
    plain.resize(fsize);
    infile.read(reinterpret_cast<char*>(plain.data()), (streamsize)fsize);
    infile.close();

    // PKCS#7 padding to 8 bytes
    size_t pad_len = 8 - (plain.size() % 8);
    if (pad_len == 0) pad_len = 8;
    for (size_t i = 0; i < pad_len; ++i) plain.push_back((uint8_t)pad_len);

    // CBC IV = 8 zero bytes
    vector<uint8_t> iv(8, 0);
    vector<uint8_t> prev_cipher = iv;
    vector<uint8_t> cipher_bytes;

    for (size_t pos = 0; pos < plain.size(); pos += 8) {
    	// XOR plaintext block with prev_cipher
    	vector<uint8_t> block(8);
    	for (int i = 0; i < 8; ++i) block[i] = plain[pos + i] ^ prev_cipher[i];

    	// convert to bits
    	vector<int> block_bits = bytes_to_bits_msb(block, 0);

    	// encrypt block
    	vector<int> cipher_bits = des_encrypt_block(block_bits, roundKeysBits);

    	// convert back to bytes
    	vector<uint8_t> cbytes = bits64_to_bytes(cipher_bits);
    	// append to result
    	for (auto b : cbytes) cipher_bytes.push_back(b);
    	// update prev_cipher
    	prev_cipher = cbytes;
    }

    // write ciphertext as hex text file
    ofstream outfile(outfile_name);
    if (!outfile) {
    	cerr << "Cannot open " << outfile_name << " for writing.\n";
    	return 1;
    }
    // write hex
    outfile << hex << uppercase;
    for (size_t i = 0; i < cipher_bytes.size(); ++i) {
    	outfile << setw(2) << setfill('0') << (int)cipher_bytes[i];
    	if ((i+1) % 16 == 0) outfile << "\n";
    }
    outfile << dec << "\n";
    outfile.close();

    cout << "Encryption complete. Ciphertext written to " << outfile_name << " (hex format).\n";

    return 0;
}