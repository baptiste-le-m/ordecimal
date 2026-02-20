//! Encoding logic for decimalInfinite format
//!
//! Based on the paper "decimalInfinite: All Decimals In Bits" by Ghislain Fourny
//! and the reference `JSONiq` implementation.

use crate::decimal::SpecialValue;
use crate::gamma::BitWriter;
use crate::significand::encode_significand;

/// Return the single encoded byte for a special value (Figure 11 of the paper).
///
/// Callers wrap this in a [`Vec`] only when constructing a [`Decimal`](crate::decimal::Decimal); keeping
/// this as a plain [`u8`] avoids a heap allocation on every special-value path.
#[must_use]
pub const fn encode_special_byte(value: SpecialValue) -> u8 {
    match value {
        SpecialValue::NegativeInfinity => 0b0000_0000, // 00
        SpecialValue::NegativeZero => 0b0100_0000,     // 01
        SpecialValue::PositiveZero => 0b1000_0000,     // 10
        SpecialValue::PositiveInfinity => 0b1100_0000, // 11
        SpecialValue::NaN => 0b1110_0000,              // 111
    }
}

/// Encode from semantic parts (for internal use during parsing)
pub fn encode_from_parts(
    positive: bool,
    exponent_positive: bool,
    exponent: u64,
    significand: &[u8],
) -> Vec<u8> {
    // Estimate capacity: sign(2 bits) + gamma(~2*log2(exp+2)+1) + significand(4 + 10*ceil((n-1)/3))
    let significand_len = significand.len();
    let exponent_bits = if exponent == 0 {
        3
    } else {
        2 * (64 - (exponent + 2).leading_zeros()) as usize + 1
    };
    let significand_bits = if significand_len <= 1 {
        4
    } else {
        4 + (significand_len - 1).div_ceil(3) * 10
    };
    let total_bits = 2 + exponent_bits + significand_bits;
    let estimated_bytes = total_bits.div_ceil(8);

    let mut writer = BitWriter::with_capacity(estimated_bytes);

    // S: Encode overall sign (2 bits)
    // 00 = negative (s = -1)
    // 10 = positive (s = 1)
    writer.write_bit(positive); // 1 for positive, 0 for negative
    writer.write_bit(false); // Second bit is always 0 for regular decimals

    // TE: Encode exponent sign and exponent together
    // Negate when s and t have OPPOSITE signs
    let negate = positive != exponent_positive;

    // Build the gamma code for (exponent + 2)
    let offset_exp = exponent + 2;
    let n = bit_length(offset_exp);

    // Modified gamma code: (N-1) ones, then 0, then the remaining N-1 bits of binary
    // (N-1) ones followed by 0
    for _ in 0..(n - 1) {
        writer.write_bit(!negate); // Write 1 if not negating, 0 if negating
    }
    writer.write_bit(negate); // Write 0 if not negating, 1 if negating

    // Remaining N-1 bits (skip leading 1 bit)
    for i in (0..(n - 1)).rev() {
        let bit = (offset_exp >> i) & 1 == 1;
        writer.write_bit(if negate { !bit } else { bit });
    }

    // M: Encode significand directly into the writer
    // For negative decimals, encode (10 - m) instead of m
    encode_significand(&mut writer, significand, !positive);

    writer.into_bytes()
}

/// Calculate the number of bits needed to represent a value in binary
#[inline]
const fn bit_length(n: u64) -> usize {
    if n == 0 {
        1
    } else {
        64 - n.leading_zeros() as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn format_binary(bytes: &[u8]) -> String {
        bytes
            .iter()
            .map(|b| format!("{:08b}", b))
            .collect::<Vec<_>>()
            .join(" ")
    }

    #[test]
    fn test_encode_zero() {
        let encoded = encode_special_byte(SpecialValue::PositiveZero);
        assert_eq!(encoded & 0xC0, 0x80); // Should start with 10
    }

    #[test]
    fn test_encode_positive_infinity() {
        let encoded = encode_special_byte(SpecialValue::PositiveInfinity);
        assert_eq!(encoded & 0xC0, 0xC0); // Should start with 11
    }

    #[test]
    fn test_paper_examples() {
        // Test all four examples from the paper (Figure 9, page 5)

        // 1) -103.2 = -1.032 × 10^2
        // s=-1, t=+1 (positive exponent), e=2
        // Expected: 00 001 11 1000 1111001000
        let e1 = encode_from_parts(false, true, 2, &[1, 0, 3, 2]);
        println!("-103.2: {}", format_binary(&e1));
        // Sign should be 00
        assert_eq!(e1[0] & 0b1100_0000, 0b0000_0000);

        // 2) -0.0405 = -4.05 × 10^-2
        // s=-1, t=-1 (negative exponent), e=2
        // Expected: 00 110 00 0101 1110110110
        let e2 = encode_from_parts(false, false, 2, &[4, 0, 5]);
        println!("-0.0405: {}", format_binary(&e2));
        // Sign should be 00
        assert_eq!(e2[0] & 0b1100_0000, 0b0000_0000);

        // 3) 0.707106 = 7.07106 × 10^-1
        // s=+1, t=-1 (negative exponent), e=1
        // Expected: 10 01 0 0111 0001000111 0001111000
        let e3 = encode_from_parts(true, false, 1, &[7, 0, 7, 1, 0, 6]);
        println!("0.707106: {}", format_binary(&e3));
        // Sign should be 10
        assert_eq!(e3[0] & 0b1100_0000, 0b1000_0000);

        // 4) 4005012345 = 4.005012345 × 10^9
        // s=+1, t=+1 (positive exponent), e=9
        // Expected: 10 1110 011 0100 0000000101 0000001100 0101011001
        let e4 = encode_from_parts(true, true, 9, &[4, 0, 0, 5, 0, 1, 2, 3, 4, 5]);
        println!("4005012345: {}", format_binary(&e4));
        // Sign should be 10
        assert_eq!(e4[0] & 0b1100_0000, 0b1000_0000);
    }

    #[test]
    fn test_small_integers_from_paper() {
        // From Figure 10 of the paper
        // 1 = 1.0 × 10^0 → 10 100 0001
        let e1 = encode_from_parts(true, true, 0, &[1]);
        println!("1: {}", format_binary(&e1));

        // -1 = -1.0 × 10^0 → 00 011 1001
        let em1 = encode_from_parts(false, true, 0, &[1]);
        println!("-1: {}", format_binary(&em1));
    }
}
