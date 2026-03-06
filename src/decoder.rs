//! Decoding logic for decimalInfinite format
//!
//! Based on the paper "decimalInfinite: All Decimals In Bits" by Ghislain Fourny

use crate::error::{DecodeError, DecodeResult};
use crate::gamma::BitReader;
use crate::significand::{decode_significand, decode_significand_to_buf};

/// Decoded decimal with semantic fields (for when field access is needed)
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DecodedDecimal {
    pub positive: bool,
    pub exponent_positive: bool,
    pub exponent: u64,
    pub significand: Vec<u8>,
}

/// Decode bytes to semantic parts.
///
/// Returns a [`DecodedDecimal`] for regular numbers, or an error for
/// invalid encodings (including the now-removed special value byte patterns
/// `0x00`, `0x40`, `0xC0`, `0xE0`).
///
/// The only valid single-byte encoding is `0x80` (positive zero), which is
/// handled by callers before reaching this function.
///
/// # Errors
///
/// Returns [`DecodeError`] if the bytes are empty or contain an invalid encoding.
pub(crate) fn decode_to_parts(bytes: &[u8]) -> DecodeResult<DecodedDecimal> {
    if bytes.is_empty() {
        return Err(DecodeError::UnexpectedEndOfInput);
    }

    let mut reader = BitReader::new(bytes);

    // Read first two bits (sign)
    let sign_bit1 = reader.read_bit()?;
    let sign_bit2 = reader.read_bit()?;

    match (sign_bit1, sign_bit2) {
        // 00 = negative number (was also -INF when all-zeros — now rejected)
        (false, false) => {
            if !reader.has_bits() || is_all_zeros_from_position(&reader) {
                return Err(DecodeError::InvalidSpecialValue);
            }
            decode_regular(&mut reader, false)
        }
        // 01 = was NegativeZero — now rejected
        (false, true) => Err(DecodeError::InvalidSpecialValue),
        // 10 = positive zero or positive number
        (true, false) => {
            if !reader.has_bits() || is_all_zeros_from_position(&reader) {
                // Positive zero — valid, but callers handle single-byte 0x80 directly.
                // Multi-byte all-zeros after "10" is also positive zero (padded).
                return Err(DecodeError::InvalidSpecialValue);
            }
            decode_regular(&mut reader, true)
        }
        // 11 = was +INF or NaN — now rejected
        (true, true) => Err(DecodeError::InvalidSpecialValue),
    }
}

/// Lightweight decoded parts that borrows significand from a caller-provided buffer.
/// Used internally by Display / `to_plain_string` to avoid heap allocation.
pub(crate) struct DecodedParts {
    pub positive: bool,
    pub exponent_positive: bool,
    pub exponent: u64,
    pub sig_len: usize,
}

/// Decode bytes into [`DecodedParts`], writing significand digits into `sig_buf`.
///
/// Returns `Ok(parts)` for regular numbers.
///
/// # Errors
///
/// Returns [`DecodeError`] for invalid encodings, including removed special value patterns.
pub(crate) fn decode_to_buf(bytes: &[u8], sig_buf: &mut [u8]) -> DecodeResult<DecodedParts> {
    if bytes.is_empty() {
        return Err(DecodeError::UnexpectedEndOfInput);
    }

    let mut reader = BitReader::new(bytes);
    let sign_bit1 = reader.read_bit()?;
    let sign_bit2 = reader.read_bit()?;

    match (sign_bit1, sign_bit2) {
        (false, false) => {
            if !reader.has_bits() || is_all_zeros_from_position(&reader) {
                return Err(DecodeError::InvalidSpecialValue);
            }
            decode_regular_to_buf(&mut reader, false, sig_buf)
        }
        (false, true) => Err(DecodeError::InvalidSpecialValue),
        (true, false) => {
            if !reader.has_bits() || is_all_zeros_from_position(&reader) {
                return Err(DecodeError::InvalidSpecialValue);
            }
            decode_regular_to_buf(&mut reader, true, sig_buf)
        }
        (true, true) => Err(DecodeError::InvalidSpecialValue),
    }
}

/// Decode exponent + significand for a regular number, writing significand to `sig_buf`.
fn decode_regular_to_buf(
    reader: &mut BitReader,
    positive: bool,
    sig_buf: &mut [u8],
) -> DecodeResult<DecodedParts> {
    let first_bit = reader.read_bit()?;
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

    let terminating_bit = reader.read_bit()?;
    if terminating_bit == first_bit {
        return Err(DecodeError::InvalidGammaCode);
    }

    let remaining_value = reader.read_bits(count)?;
    let negated = !first_bit;
    let remaining_value = if negated {
        let mask = (1u64 << count) - 1;
        (!remaining_value) & mask
    } else {
        remaining_value
    };

    let binary_value = (1u64 << count) | remaining_value;
    if binary_value < 2 {
        return Err(DecodeError::InvalidGammaCode);
    }
    let exponent = binary_value - 2;

    let exponent_positive = if positive { !negated } else { negated };
    if exponent == 0 && !exponent_positive {
        return Err(DecodeError::ZeroWithNegativeExponent);
    }

    let sig_len = decode_significand_to_buf(reader, !positive, sig_buf)?;

    Ok(DecodedParts {
        positive,
        exponent_positive,
        exponent,
        sig_len,
    })
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
fn decode_regular(reader: &mut BitReader, positive: bool) -> DecodeResult<DecodedDecimal> {
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

    // The gamma code reconstructs a value via `(1u64 << count) | data`,
    // so count must be < 64 to avoid shift overflow.
    if count >= 64 {
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

    Ok(decoded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoder::encode_from_parts;

    #[test]
    fn test_decode_zero_bytes_rejected() {
        // 0x80 (positive zero) is now handled by the caller, not the decoder.
        // Single byte 0x80 has sign bits "10" and then all zeros → InvalidSpecialValue
        let bytes = vec![0b1000_0000]; // 10
        assert!(decode_to_parts(&bytes).is_err());
    }

    #[test]
    fn test_decode_negative_infinity_rejected() {
        let bytes = vec![0b0000_0000]; // 00
        assert!(decode_to_parts(&bytes).is_err());
    }

    #[test]
    fn test_decode_negative_zero_rejected() {
        let bytes = vec![0b0100_0000]; // 01
        assert!(decode_to_parts(&bytes).is_err());
    }

    #[test]
    fn test_decode_positive_infinity_rejected() {
        let bytes = vec![0b1100_0000]; // 11
        assert!(decode_to_parts(&bytes).is_err());
    }

    #[test]
    fn test_decode_nan_rejected() {
        let bytes = vec![0b1110_0000]; // 111
        assert!(decode_to_parts(&bytes).is_err());
    }

    #[test]
    fn test_roundtrip_simple() {
        // Test roundtrip for 7.07106 × 10^-1
        let encoded = encode_from_parts(true, false, 1, &[7, 0, 7, 1, 0, 6]);
        let decoded = decode_to_parts(&encoded).unwrap();

        assert!(decoded.positive);
        assert!(!decoded.exponent_positive);
        assert_eq!(decoded.exponent, 1);
        // Significand may have trailing zeros from padding
        assert!(decoded.significand.starts_with(&[7, 0, 7, 1, 0, 6]));
    }

    #[test]
    fn test_roundtrip_positive_integer() {
        // Test roundtrip for 1 = 1.0 × 10^0
        let encoded = encode_from_parts(true, true, 0, &[1]);
        println!("Encoded 1: {:08b}", encoded[0]);
        let decoded = decode_to_parts(&encoded).unwrap();

        assert!(decoded.positive);
        assert!(decoded.exponent_positive);
        assert_eq!(decoded.exponent, 0);
        assert_eq!(decoded.significand[0], 1);
    }
}
