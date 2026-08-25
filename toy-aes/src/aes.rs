// block cipher, column-major 4x4 matrix stored in an array
#[derive(Debug, Clone)]
pub struct Block([u8; 16]);
impl Block {
    // matrix is column-major here: matrix[col][row], matching the aes convention. Each entry is a byte.
    pub fn from_matrix(matrix: [[u8; 4]; 4]) -> Self {
        let mut arr = [0; 16];
        for i in 0..16 {
            arr[i] = matrix[i / 4][i % 4]
        }
        Block(arr)
    }

    pub fn from_text(text: &str) -> Self {
        if text.len() != 16 {
            panic!("text must be exactly {} chars", 16)
        }
        let arr = text.bytes().collect::<Vec<u8>>().try_into().unwrap();
        Block(arr)
    }

    pub fn from_bytes(bytes: &[u8; 16]) -> Self {
        Block(bytes.clone())
    }

    pub fn to_string(&self) -> String {
        self.0.iter().map(|c| *c as char).collect()
    }

    pub fn to_matrix(&self) -> [[u8; 4]; 4] {
        let mut new_matrix = [[0; 4]; 4];
        for i in 0..16 {
            new_matrix[i / 4][i % 4] = self.0[i];
        }
        new_matrix
    }

    // add round key with xor operation - a.k.a Rijndael galois field addition
    pub fn add_round_key(&mut self, round_key: &Block) {
        for i in 0..16 {
            self.0[i] = self.0[i] ^ round_key.0[i]
        }
    }

    // apply non-linear function with sbox substitution
    pub fn sub_bytes(&mut self) {
        for i in 0..16 {
            self.0[i] = S_BOX_MAP[self.0[i] as usize]
        }
    }
    pub fn inv_sub_bytes(&mut self) {
        for i in 0..16 {
            self.0[i] = S_BOX_MAP_INV[self.0[i] as usize]
        }
    }

    // diffusion (shift rows + mix columns)
    pub fn shift_rows(&mut self) {
        // note: self is storing the matrix column major
        // row 0 doesn't move

        for i in 1..4 {
            let row_i = [self.0[i], self.0[4 + i], self.0[8 + i], self.0[12 + i]];
            // row 1 shifts 1 time, row 2 shifts 2 times, row 3 shifts 3 times
            self.0[i] = row_i[i];
            self.0[4 + i] = row_i[(1 + i) % 4];
            self.0[8 + i] = row_i[(2 + i) % 4];
            self.0[12 + i] = row_i[(3 + i) % 4];
        }
    }

    pub fn inv_shift_rows(&mut self) {
        // note: self is storing the matrix column major
        // row 0 doesn't move

        for i in 1..4 {
            let row_i = [self.0[i], self.0[4 + i], self.0[8 + i], self.0[12 + i]];
            // row 1 shifts 1 time, row 2 shifts 2 times, row 3 shifts 3 times
            self.0[i] = row_i[(-(i as i32)).rem_euclid(4) as usize];
            self.0[4 + i] = row_i[(1 - (i as i32)).rem_euclid(4) as usize];
            self.0[8 + i] = row_i[(2 - (i as i32)).rem_euclid(4) as usize];
            self.0[12 + i] = row_i[(3 - (i as i32)).rem_euclid(4) as usize];
        }
    }

    pub fn mix_columns(&mut self) {
        for i in 0..4 {
            //  column-major, iterate over columns (contiguously)
            let base = i * 4;
            let a = [
                self.0[base],
                self.0[base + 1],
                self.0[base + 2],
                self.0[base + 3],
            ];

            // https://en.wikipedia.org/wiki/Rijndael_MixColumns#Matrix_representation
            // self.0[base] = galois_mul2(b0) ^ galois_mul3(b1) ^ b2 ^ b3;
            // self.0[base + 1] = b0 ^ galois_mul2(b1) ^ galois_mul3(b2) ^ b3;
            // self.0[base + 2] = b0 ^ b1 ^ galois_mul2(b2) ^ galois_mul3(b3);
            // self.0[base + 3] = galois_mul3(b0) ^ b1 ^ b2 ^ galois_mul2(b3);

            // Optimization from Sec 4.1.2 in The Design of Rijndael
            let t = a[0] ^ a[1] ^ a[2] ^ a[3];
            // a[0] ^ (a[0] ^ a[1] ^ a[2] ^ a[3]) ^ 2a[0] ^ 2a[1] = 2*a0 ^ 3*a1 ^ a2 ^ a3 (as x ^ x = 0)
            self.0[base] = a[0] ^ t ^ galois_mul2(a[0] ^ a[1]);
            self.0[base + 1] = a[1] ^ t ^ galois_mul2(a[1] ^ a[2]);
            self.0[base + 2] = a[2] ^ t ^ galois_mul2(a[2] ^ a[3]);
            self.0[base + 3] = a[3] ^ t ^ galois_mul2(a[3] ^ a[0]);
        }
    }

    /// Inverse MixColumns transformation on a 4x4 AES state matrix.
    pub fn inv_mix_columns(&mut self) {
        for i in 0..4 {
            //  column-major, iterate over columns (contiguously)
            let base = i * 4;

            // https://en.wikipedia.org/wiki/Rijndael_MixColumns#InverseMixColumns
            // self.0[base] = galois_mul14(d0) ^ galois_mul11(d1) ^ galois_mul13(d2) ^ galois_mul9(d3);
            // self.0[base + 1] = galois_mul9(d0) ^ galois_mul14(d1) ^ galois_mul11(d2) ^ galois_mul13(d3);
            // self.0[base + 2] = galois_mul13(d0) ^ galois_mul9(d1) ^ galois_mul14(d2) ^ galois_mul11(d3);
            // self.0[base + 3] = galois_mul11(d0) ^ galois_mul13(d1) ^ galois_mul9(d2) ^ galois_mul14(d3);

            // Optimization from Sec 4.1.3 in The Design of Rijndael
            // preprocessing step + then apply mixcolumns
            // as mixcolumn polynomial c(x) and inv_mixcolumn polynomial d(x) are related by d(x) = (04x^2 + 05)c(x) mod x^4 + 1
            let u = galois_mul2(galois_mul2(self.0[base] ^ self.0[base + 2]));
            let v = galois_mul2(galois_mul2(self.0[base + 1] ^ self.0[base + 3]));
            // u ^ a[0] = 4a[0] ^ 4a[2] ^ a[0] = 5a[0] + 4a[2] (matching 04x^2 + 05, only need to multiply by the mix columns polynomial)
            self.0[base] = u ^ self.0[base];
            self.0[base + 1] = v ^ self.0[base + 1];
            self.0[base + 2] = u ^ self.0[base + 2];
            self.0[base + 3] = v ^ self.0[base + 3];
        }
        self.mix_columns();
    }

    // https://github.com/francisrstokes/githublog/blob/main/2022/6/15/rolling-your-own-crypto-aes.md#operations-and-transformations
    pub fn encrypt(&mut self, key: &[u8]) {
        // generate round keys
        let round_keys = expand_keys(key);

        // round 1
        self.add_round_key(&round_keys[0]);

        // rounds 2 to last - 1
        for i in 1..(round_keys.len() - 1) {
            self.sub_bytes();
            self.shift_rows();
            self.mix_columns();
            self.add_round_key(&round_keys[i]);
        }

        // last round
        self.sub_bytes();
        self.shift_rows();
        self.add_round_key(&round_keys[10]);
    }

    pub fn decrypt(&mut self, key: &[u8]) {
        // generate round keys
        let round_keys = expand_keys(key);

        // last round
        self.add_round_key(&round_keys[round_keys.len() - 1]);
        self.inv_shift_rows();
        self.inv_sub_bytes();

        // rounds last - 1 to 2
        for i in (1..(round_keys.len() - 1)).rev() {
            self.add_round_key(&round_keys[i]);
            self.inv_mix_columns();
            self.inv_shift_rows();
            self.inv_sub_bytes();
        }

        // round 1
        self.add_round_key(&round_keys[0]);
    }
}

// for simplicity we return a Vec that can be of size AES_ROUNDS_128=11, AES_ROUNDS_192=13 or  AES_ROUNDS_256=15
pub fn expand_keys(key: &[u8]) -> Vec<Block> {
    let keylen = key.len();
    assert!(keylen == 16 || keylen == 24 || keylen == 32);

    #[allow(non_snake_case)]
    let N = keylen / 4;
    let aes_rounds = if N == 4 {
        11
    } else if N == 6 {
        13
    } else {
        15
    };

    // Round constants https://en.wikipedia.org/wiki/AES_key_schedule#Round_constants
    let r_con = [
        0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36, 0x6C, 0xD8, 0xAB, 0x4D,
        0x9A, 0x2F, 0x5E, 0xBC, 0x63, 0xC6, 0x97, 0x35, 0x6A, 0xD4, 0xB3, 0x7D, 0xFA, 0xEF, 0xC5,
        0x91, 0x39,
    ];

    // https://en.wikipedia.org/wiki/AES_key_schedule#The_key_schedule
    // `words` stores all 32 bits words for all generated keys contiguously
    // each key is N words long
    let mut words: Vec<[u8; 4]> = Vec::new();
    // add the base key (from wikipedia: if i < N => Ki)
    for i in 0..N {
        words.push([key[i * 4], key[i * 4 + 1], key[i * 4 + 2], key[i * 4 + 3]]);
    }

    // iteratively generate key words from the base key
    for i in N..N * aes_rounds {
        let mut word = words[i - 1];
        // round key is complete (from wikipedia: i >= N && i mod N == 0)
        if i % N == 0 {
            // apply the transformation on the 32 bit word
            // 1. rotate word (RotWord)
            // 2. substitute word (SubWord)
            // 3. Xor with round constant (Rcon), note this only affects the first byte as other rcon value are 0.
            word = [
                S_BOX_MAP[word[1] as usize] ^ r_con[i / N],
                S_BOX_MAP[word[2] as usize],
                S_BOX_MAP[word[3] as usize],
                S_BOX_MAP[word[0] as usize],
            ];
        }

        // inject non-linearity every 4th word in AES-256 (N=8) (from wikipedia: i >= N && N > 6 && i mod N == 4)
        if N > 6 && i % N == 4 {
            word = [
                S_BOX_MAP[word[0] as usize],
                S_BOX_MAP[word[1] as usize],
                S_BOX_MAP[word[2] as usize],
                S_BOX_MAP[word[3] as usize],
            ]
        }

        // xor with word[i-N] applies to all cases
        let prev_key_word = words[i - N];
        word = [
            word[0] ^ prev_key_word[0],
            word[1] ^ prev_key_word[1],
            word[2] ^ prev_key_word[2],
            word[3] ^ prev_key_word[3],
        ];
        words.push(word);
    }

    // return array of size 11, 13 or 15 depending on key size
    words
        .into_iter()
        .flatten()
        .collect::<Vec<u8>>()
        .chunks(16)
        .map(|c| Block::from_bytes(c.try_into().unwrap()))
        .collect()
}

/// Multiply by 2 in GF(2^8) using the AES reduction polynomial (x^8 + x^4 + x^3 + x + 1).
#[inline]
fn galois_mul2(x: u8) -> u8 {
    let hi_bit_set = x & 0x80 != 0;
    let mut result = x << 1;
    if hi_bit_set {
        result ^= 0x1B;
    }
    result
}

// x belongs to [0:255] => y = S_BOX_MAP[X]
const S_BOX_MAP: [u8; 256] = [
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
    0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
    0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
    0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
    0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
    0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
    0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
    0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
    0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
    0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
    0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
    0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
    0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
    0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
    0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
    0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16,
];
const S_BOX_MAP_INV: [u8; 256] = [
    0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB,
    0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB,
    0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E,
    0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25,
    0x72, 0xF8, 0xF6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xD4, 0xA4, 0x5C, 0xCC, 0x5D, 0x65, 0xB6, 0x92,
    0x6C, 0x70, 0x48, 0x50, 0xFD, 0xED, 0xB9, 0xDA, 0x5E, 0x15, 0x46, 0x57, 0xA7, 0x8D, 0x9D, 0x84,
    0x90, 0xD8, 0xAB, 0x00, 0x8C, 0xBC, 0xD3, 0x0A, 0xF7, 0xE4, 0x58, 0x05, 0xB8, 0xB3, 0x45, 0x06,
    0xD0, 0x2C, 0x1E, 0x8F, 0xCA, 0x3F, 0x0F, 0x02, 0xC1, 0xAF, 0xBD, 0x03, 0x01, 0x13, 0x8A, 0x6B,
    0x3A, 0x91, 0x11, 0x41, 0x4F, 0x67, 0xDC, 0xEA, 0x97, 0xF2, 0xCF, 0xCE, 0xF0, 0xB4, 0xE6, 0x73,
    0x96, 0xAC, 0x74, 0x22, 0xE7, 0xAD, 0x35, 0x85, 0xE2, 0xF9, 0x37, 0xE8, 0x1C, 0x75, 0xDF, 0x6E,
    0x47, 0xF1, 0x1A, 0x71, 0x1D, 0x29, 0xC5, 0x89, 0x6F, 0xB7, 0x62, 0x0E, 0xAA, 0x18, 0xBE, 0x1B,
    0xFC, 0x56, 0x3E, 0x4B, 0xC6, 0xD2, 0x79, 0x20, 0x9A, 0xDB, 0xC0, 0xFE, 0x78, 0xCD, 0x5A, 0xF4,
    0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F,
    0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF,
    0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D,
];
