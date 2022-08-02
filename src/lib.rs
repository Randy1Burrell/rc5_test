//!
//! #RC5
//!
//! This is a library that implements the RC5 encryption algorithm for 32 bits
//! word size.
//!
//!
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::{cmp, io::Cursor};

//------------------------------------------------------------------------------
// Traits here should move to another file is the library grows.
//------------------------------------------------------------------------------
trait ArithExt<T> {
    /**
     * Subtraction operator with standard overflow semantics
     */
    fn overflow_sub(self, val: T) -> T;
}

impl ArithExt<u32> for u32 {
    fn overflow_sub(self, val: u32) -> u32 {
        let (res, _) = self.overflowing_sub(val);
        res
    }
}

//------------------------------------------------------------------------------
// Helper functions starts here and should move to another file is the library
// grows.
//------------------------------------------------------------------------------
/// `calculate_constants` calculate and returns the constants Q and P used in
/// RC5 to help generate sudo random integers for the shuffled `key_table`.
fn calculate_constants(word: u32) -> (u32, u64) {
    match word {
        16 => (0xB7E1, 0x9E37),
        32 => (0xB7E15163, 0x9E3779B9),
        // Only 16, 32 an 64 bit words are allowed for now.
        _ => panic!("Crash and burn"),
    }
}

/// `align_key` generates and return the size of the setup `key_table` and the
/// `key_table` based on the length of the current `key`.
fn align_key(mut key: Vec<u8>, word_bit: u32) -> (u32, Vec<u64>) {
    let table_size: u32;
    let key_len = key.len();

    if key_len == 0 {
        table_size = 1;
    } else if key_len as u32 % word_bit != 0 {
        // Increase the size of the key to accommodate the word size being used
        // and fill it with zero and place holders.
        (0..(word_bit - key_len as u32 % word_bit)).for_each(|_i| key.push(0x0));
        let key_len = key.len();
        table_size = key_len as u32 / word_bit;
    } else {
        table_size = key_len as u32 / word_bit;
    }

    // Create a new key table and fill it will sudo random integer base on the
    // key
    let mut table: Vec<u64> = vec![0; table_size as usize];
    let shift: u64 = 8;
    (0..key_len).rev().for_each(|i| {
        table[(i as u32 / word_bit) as usize] =
            (table[(i as u32 / word_bit) as usize] << shift) + u64::from(key[i])
    });
    (table_size, table)
}

/// `extend_key` extends the `key_table` and calculated the sudo random integers
/// based on the magic constants `P` and `Q`, then returns the new key_table.
fn extend_key(word: u32, rounds: u32, modulo: u64) -> Vec<u64> {
    let (p_const, q_const) = calculate_constants(word);
    (0..2 * (rounds + 1))
        .map(|index| (p_const as u64 + index as u64 * q_const) % modulo)
        .collect()
}

/// `shuffle` generated sudo random integers for the `key_table` as a final
/// values to be used in ciphers.
fn shuffle(
    table_size: u32,
    round_1x2: u32,
    word: u32,
    mut key_table: Vec<u64>,
    mut aligned_table: Vec<u64>,
) -> Vec<u64> {
    // Temporary indexer variables.
    let (mut i, mut j, mut a, mut b): (usize, usize, usize, usize) = (0, 0, 0, 0);

    // Generate sudo random integers based in the aligned table
    for _x in 0..(3 * cmp::max(table_size, round_1x2)) {
        key_table[i] = shift_left(key_table[i] + a as u64 + b as u64, 3, word as u64);
        a = key_table[i] as usize;
        aligned_table[j] = shift_left(
            aligned_table[j] + a as u64 + b as u64,
            (a + b) as u64,
            word as u64,
        );
        b = aligned_table[j] as usize;
        i = (i + 1) % round_1x2 as usize;
        j = (j + 1) % table_size as usize;
    }
    key_table
}

/// `calculate_mask` calculates mask size and number of bytes in word.
fn calculate_mask(word: u64, shift: u64) -> (u64, u64) {
    let base: u64 = 2;
    let mask = base.pow(word as u32) - 1;
    let bit_shift = shift % word;

    (bit_shift, mask)
}

/// `shift_left` shifts a byte left.
fn shift_left(val: u64, shift: u64, word: u64) -> u64 {
    let (bit_shift, mask) = calculate_mask(word, shift);
    ((val << bit_shift) & mask) | ((val & mask) >> (word - bit_shift))
}

/// `set_up_key_table` sets up all the necessary steps. for encryption to
/// happen.
fn set_up_key_table(word: u32, rounds: u32, key: Vec<u8>) -> (Vec<u64>, u64) {
    let base: u64 = 2;
    let modulo = base.pow(word as u32) as u64;
    let (c, table) = align_key(key, word / 8);
    let key_table: Vec<u64> = extend_key(word, rounds, modulo);
    (shuffle(c, 2 * (rounds + 1), word, key_table, table), modulo)
}

/// `encode` returns a cipher text for a given key and plaintext.
pub fn encode(key: Vec<u8>, plaintext: Vec<u8>, word: u32, rounds: u32) -> Vec<u8> {
    let bits = (word / 8) as usize;
    // lsv and rsv stands for right and left sides of vector
    let mut lsv = Cursor::new(plaintext[..bits].to_vec());
    let mut rsv = Cursor::new(plaintext[bits..].to_vec());

    let (key_table, modulo) = set_up_key_table(word, rounds, key);

    let mut a = lsv.read_u32::<LittleEndian>().unwrap() as u64;
    let mut b = rsv.read_u32::<LittleEndian>().unwrap() as u64;

    a = (a + key_table[0]) % modulo;
    b = (b + key_table[1]) % modulo;

    // Make magic happen
    (1..rounds + 1).for_each(|round| {
        a = (shift_left(a ^ b, b, word as u64) + key_table[(2 * round) as usize]) % modulo;
        b = (shift_left(a ^ b, a, word as u64) + key_table[(2 * round + 1) as usize]) % modulo;
    });

    // Converts a, b back to byte array stored in LittleEndian form
    let mut wrt = vec![];
    wrt.write_u32::<LittleEndian>(a as u32).unwrap();
    wrt.write_u32::<LittleEndian>(b as u32).unwrap();
    wrt
}

/// `decode` decodes a cipher text
pub fn decode(key: Vec<u8>, ciphertext: Vec<u8>, word: u32, rounds: u32) -> Vec<u8> {
    // Setup key table of sudo random bits
    let bits = (word / 8) as usize;
    let (key_table, _) = set_up_key_table(word, rounds, key);

    // Get right and left side of vector
    let mut lsv = Cursor::new(ciphertext[..bits].to_vec());
    let mut rsv = Cursor::new(ciphertext[bits..].to_vec());

    // Generate integer from bytes
    let mut a = lsv.read_u32::<LittleEndian>().unwrap();
    let mut b = rsv.read_u32::<LittleEndian>().unwrap();

    // Where the magic happens in the cipher
    (1..(rounds + 1)).rev().for_each(|round| {
        b = b
            .overflow_sub(key_table[(2 * round + 1) as usize] as u32)
            .rotate_right(a)
            ^ a;
        a = a
            .overflow_sub(key_table[(2 * round) as usize] as u32)
            .rotate_right(b as u32)
            ^ b;
    });

    b = b.overflow_sub(key_table[1] as u32);
    a = a.overflow_sub(key_table[0] as u32);

    let mut wrt = vec![];
    wrt.write_u32::<LittleEndian>(a as u32).unwrap();
    wrt.write_u32::<LittleEndian>(b as u32).unwrap();
    wrt
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encode_y() {
        let key: Vec<u8> = vec![
            0x78, 0x33, 0x48, 0xE7, 0x5A, 0xEB, 0x0F, 0x2F, 0xD7, 0xB1, 0x69, 0xBB, 0x8D, 0xC1,
            0x67, 0x87,
        ];
        let pt: Vec<u8> = vec![0xF7, 0xC0, 0x13, 0xAC, 0x5B, 0x2B, 0x89, 0x52];
        let ct: Vec<u8> = vec![0x2F, 0x42, 0xB3, 0xB7, 0x03, 0x69, 0xFC, 0x92];
        let res = encode(key, pt, 32, 12);
        assert_eq!(&ct[..], &res[..]);
    }

    #[test]
    fn encode_a() {
        let key = vec![
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
            0x0E, 0x0F,
        ];
        let pt: Vec<u8> = vec![0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77];
        let ct: Vec<u8> = vec![0x2D, 0xDC, 0x14, 0x9B, 0xCF, 0x08, 0x8B, 0x9E];
        let res = encode(key, pt, 32, 12);
        assert_eq!(&ct[..], &res[..]);
    }

    #[test]
    fn encode_b() {
        let key = vec![
            0x2B, 0xD6, 0x45, 0x9F, 0x82, 0xC5, 0xB3, 0x00, 0x95, 0x2C, 0x49, 0x10, 0x48, 0x81,
            0xFF, 0x48,
        ];
        let pt = vec![0xEA, 0x02, 0x47, 0x14, 0xAD, 0x5C, 0x4D, 0x84];
        let ct = vec![0x11, 0xE4, 0x3B, 0x86, 0xD2, 0x31, 0xEA, 0x64];
        let res = encode(key, pt, 32, 12);
        assert_eq!(&ct[..], &res[..]);
    }

    #[test]
    fn decode_a() {
        let key = vec![
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
            0x0E, 0x0F,
        ];
        let pt = vec![0x96, 0x95, 0x0D, 0xDA, 0x65, 0x4A, 0x3D, 0x62];
        let ct = vec![0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77];
        let res = decode(key, ct, 32, 12);
        assert_eq!(&pt[..], &res[..]);
    }

    #[test]
    fn decode_b() {
        let key = vec![
            0x2B, 0xD6, 0x45, 0x9F, 0x82, 0xC5, 0xB3, 0x00, 0x95, 0x2C, 0x49, 0x10, 0x48, 0x81,
            0xFF, 0x48,
        ];
        let pt = vec![0x63, 0x8B, 0x3A, 0x5E, 0xF7, 0x2B, 0x66, 0x3F];
        let ct = vec![0xEA, 0x02, 0x47, 0x14, 0xAD, 0x5C, 0x4D, 0x84];
        let res = decode(key, ct, 32, 12);
        assert_eq!(&pt[..], &res[..]);
    }
}

fn main() {
    let key = vec![
        0x2B, 0xD6, 0x45, 0x9F, 0x82, 0xC5, 0xB3, 0x00, 0x95, 0x2C, 0x49, 0x10, 0x48, 0x81, 0xFF,
        0x48,
    ];
    let pt = vec![0x63, 0x8B, 0x3A, 0x5E, 0xF7, 0x2B, 0x66, 0x3F];
    let ct = vec![0xEA, 0x02, 0x47, 0x14, 0xAD, 0x5C, 0x4D, 0x84];
    let res = decode(key, ct, 32, 12);
    assert_eq!(&pt[..], &res[..]);
}
