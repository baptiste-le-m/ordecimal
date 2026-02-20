//! Decoding logic for decimalInfinite format
//!
//! Based on the paper "decimalInfinite: All Decimals In Bits" by Ghislain Fourny

use crate::decimal::SpecialValue;
use crate::error::{DecodeError, DecodeResult};
use crate::gamma::BitReader;
use crate::significand::decode_significand;

/// Decoded decimal with semantic fields (for when field access is needed)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedDecimal {
    pub positive: bool,
    pub exponent_positive: bool,
    pub exponent: u64,
    pub significand: Vec<u8>,
}

/// Represents either a decoded regular decimal or a special value
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodedValue {
    Regular(DecodedDecimal),
    Special(SpecialValue),
}

/// Decode bytes to semantic parts
///
/// # Errors
///
/// Returns [`DecodeError`] if the bytes are empty or contain an invalid encoding.
pub fn decode_to_parts(bytes: &[u8]) -> DecodeResult<DecodedValue> {
    if bytes.is_empty() {
        return Err(DecodeError::UnexpectedEndOfInput);
    }

    let mut reader = BitReader::new(bytes);

    // Read first two bits (sign)
    let sign_bit1 = reader.read_bit()?;
    let sign_bit2 = reader.read_bit()?;

    match (sign_bit1, sign_bit2) {
        // 00 = negative or -INF
        (false, false) => {
            if !reader.has_bits() || is_all_zeros_from_position(&reader) {
                return Ok(DecodedValue::Special(SpecialValue::NegativeInfinity));
            }
            decode_regular(&mut reader, false)
        }
        // 01 = negative zero
        (false, true) => Ok(DecodedValue::Special(SpecialValue::NegativeZero)),
        // 10 = positive zero or positive number
        (true, false) => {
            if !reader.has_bits() || is_all_zeros_from_position(&reader) {
                return Ok(DecodedValue::Special(SpecialValue::PositiveZero));
            }
            decode_regular(&mut reader, true)
        }
        // 11 = +INF or NaN
        (true, true) => {
            if !reader.has_bits() {
                return Ok(DecodedValue::Special(SpecialValue::PositiveInfinity));
            }
            let third_bit = reader.read_bit()?;
            if third_bit {
                // 111 = NaN
                Ok(DecodedValue::Special(SpecialValue::NaN))
            } else {
                // 110 = +INF
                Ok(DecodedValue::Special(SpecialValue::PositiveInfinity))
            }
        }
    }
}

fn is_all_zeros_from_position(reader: &BitReader) -> bool {
    let pos = reader.position();
    let bytes = reader.bytes();
    let byte_idx = pos / 8;
    let bit_offset = pos % 8;

    if byte_idx >= bytes.len() {
        return true;
    }

    // Check remaining bits in current byte
    let mask = (1u8 << (8 - bit_offset)) - 1;
    if bytes[byte_idx] & mask != 0 {
        return false;
    }

    // Check remaining bytes
    bytes[byte_idx + 1..].iter().all(|&b| b == 0)
}

/// Decode a regular (non-special) decimal number
fn decode_regular(reader: &mut BitReader, positive: bool) -> DecodeResult<DecodedValue> {
    // TE: Read exponent sign and exponent together
    // First, read the leading bit to determine if gamma is negated
    let first_bit = reader.read_bit()?;

    // Count how many identical bits follow (including first_bit, we start at 1)
    let mut count = 1usize;
    while reader.has_bits() {
        match reader.peek_bit() {
            Ok(bit) if bit == first_bit => {
                reader.read_bit()?;
                count += 1;
            }
            _ => break,
        }
    }

    // Read the terminating bit (opposite of the repeated bits)
    let terminating_bit = reader.read_bit()?;
    if terminating_bit == first_bit {
        return Err(DecodeError::InvalidGammaCode);
    }

    // Read the remaining `count` bits in one batch
    let remaining_value = reader.read_bits(count)?;

    // Reconstruct the gamma code bits
    // The gamma code was: (count) identical bits, 1 opposite bit, (count) data bits
    // Total length: 2*count + 1 bits

    // Determine if gamma was negated
    // If first_bit is 0, gamma was negated (leading 0s instead of 1s)
    let negated = !first_bit;

    // If negated, we need to flip the remaining value bits
    let remaining_value = if negated {
        let mask = (1u64 << count) - 1;
        (!remaining_value) & mask
    } else {
        remaining_value
    };

    // Reconstruct the binary value: prepend a 1 to the remaining bits
    let binary_value = (1u64 << count) | remaining_value;

    // Subtract offset of 2 to get exponent
    if binary_value < 2 {
        return Err(DecodeError::InvalidGammaCode);
    }
    let exponent = binary_value - 2;

    // Determine exponent sign based on overall sign and whether gamma was negated
    // From the encoding logic:
    // - negate when s != t
    // So: negated = (s != t)
    // If s=+1 (positive) and negated, then t=-1 (negative exponent)
    // If s=+1 (positive) and !negated, then t=+1 (positive exponent)
    // If s=-1 (negative) and negated, then t=+1 (positive exponent)
    // If s=-1 (negative) and !negated, then t=-1 (negative exponent)
    let exponent_positive = if positive {
        !negated // positive decimal: negated means negative exponent
    } else {
        negated // negative decimal: negated means positive exponent
    };

    // Check for invalid: exponent 0 with negative sign
    if exponent == 0 && !exponent_positive {
        return Err(DecodeError::ZeroWithNegativeExponent);
    }

    // M: Decode significand
    // For negative decimals, we encoded (10 - m), so we need to decode with complement
    let significand = decode_significand(reader, !positive)?;

    // Create the decoded decimal
    let decoded = DecodedDecimal {
        positive,
        exponent_positive,
        exponent,
        significand,
    };

    Ok(DecodedValue::Regular(decoded))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoder::encode_from_parts;

    #[test]
    fn test_decode_zero() {
        let bytes = vec![0b1000_0000]; // 10
        let decoded = decode_to_parts(&bytes).unwrap();
        assert_eq!(decoded, DecodedValue::Special(SpecialValue::PositiveZero));
    }

    #[test]
    fn test_decode_negative_infinity() {
        let bytes = vec![0b0000_0000]; // 00
        let decoded = decode_to_parts(&bytes).unwrap();
        assert_eq!(
            decoded,
            DecodedValue::Special(SpecialValue::NegativeInfinity)
        );
    }

    #[test]
    fn test_roundtrip_simple() {
        // Test roundtrip for 7.07106 × 10^-1
        let encoded = encode_from_parts(true, false, 1, &[7, 0, 7, 1, 0, 6]);
        let decoded = decode_to_parts(&encoded).unwrap();

        if let DecodedValue::Regular(dec) = decoded {
            assert!(dec.positive);
            assert!(!dec.exponent_positive);
            assert_eq!(dec.exponent, 1);
            // Significand may have trailing zeros from padding
            assert!(dec.significand.starts_with(&[7, 0, 7, 1, 0, 6]));
        } else {
            panic!("Expected regular decimal");
        }
    }

    #[test]
    fn test_roundtrip_positive_integer() {
        // Test roundtrip for 1 = 1.0 × 10^0
        let encoded = encode_from_parts(true, true, 0, &[1]);
        println!("Encoded 1: {:08b}", encoded[0]);
        let decoded = decode_to_parts(&encoded).unwrap();

        if let DecodedValue::Regular(dec) = decoded {
            assert!(dec.positive);
            assert!(dec.exponent_positive);
            assert_eq!(dec.exponent, 0);
            assert_eq!(dec.significand[0], 1);
        } else {
            panic!("Expected regular decimal");
        }
    }
}
