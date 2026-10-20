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
    let mut reader = BitReader::new(bytes);
    let header = decode_header(&mut reader)?;

    // M: Decode significand
    // For negative decimals, we encoded (10 - m), so we need to decode with complement
    let significand = decode_significand(&mut reader, !header.positive)?;

    Ok(DecodedDecimal {
        positive: header.positive,
        exponent_positive: header.exponent_positive,
        exponent: header.exponent,
        significand,
    })
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
    let mut reader = BitReader::new(bytes);
    let header = decode_header(&mut reader)?;
    let sig_len = decode_significand_to_buf(&mut reader, !header.positive, sig_buf)?;

    Ok(DecodedParts {
        positive: header.positive,
        exponent_positive: header.exponent_positive,
        exponent: header.exponent,
        sig_len,
    })
}

/// The S and TE fields of a regular number: everything before the significand.
struct Header {
    positive: bool,
    exponent_positive: bool,
    exponent: u64,
}

/// Read the sign and exponent, leaving `reader` at the start of the significand.
///
/// Inlined so each of the two callers keeps the single-path code they had
/// before sharing it (≈15% on `to_plain_string` otherwise).
#[inline(always)]
fn decode_header(reader: &mut BitReader) -> DecodeResult<Header> {
    if !reader.has_bits() {
        return Err(DecodeError::UnexpectedEndOfInput);
    }

    // Read first two bits (sign)
    let sign_bit1 = reader.read_bit()?;
    let sign_bit2 = reader.read_bit()?;

    let positive = match (sign_bit1, sign_bit2) {
        // 00 = negative number (was also -INF when all-zeros — now rejected)
        (false, false) => {
            if !reader.has_bits() || is_all_zeros_from_position(reader) {
                return Err(DecodeError::InvalidSpecialValue);
            }
            false
        }
        // 01 = was NegativeZero — now rejected
        (false, true) => return Err(DecodeError::InvalidSpecialValue),
        // 10 = positive zero or positive number
        (true, false) => {
            if !reader.has_bits() || is_all_zeros_from_position(reader) {
                // Positive zero is the single byte 0x80, which callers handle
                // before decoding; followed by more zero bytes it is a second
                // byte form of zero.
                return Err(DecodeError::NonCanonical);
            }
            true
        }
        // 11 = was +INF or NaN — now rejected
        (true, true) => return Err(DecodeError::InvalidSpecialValue),
    };

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

    Ok(Header {
        positive,
        exponent_positive,
        exponent,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoder::encode_from_parts;

    #[test]
    fn test_decode_zero_bytes_rejected() {
        // 0x80 (positive zero) is now handled by the caller, not the decoder.
        // Single byte 0x80 has sign bits "10" and then all zeros → NonCanonical
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
    fn test_non_canonical_encodings_rejected() {
        // Eq/Ord/Hash compare raw bytes, so a second byte form of a value would
        // compare unequal to the canonical one and could sort out of place.
        let one = encode_from_parts(true, true, 0, &[1]);
        assert_eq!(one, [0xA0, 0x80]);
        // 39 bits: a single padding bit, so one extra byte is not a declet.
        let ten_digits = encode_from_parts(true, true, 0, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 1]);
        assert_eq!(ten_digits.len(), 5);
        let minus_one_and_half = encode_from_parts(false, true, 0, &[1, 5]);

        let with = |base: &[u8], edit: fn(&mut Vec<u8>)| {
            let mut bytes = base.to_vec();
            edit(&mut bytes);
            bytes
        };
        let cases = [
            ("zero plus a zero byte", vec![0x80, 0x00]),
            ("non-zero padding", with(&one, |b| b[1] |= 0x01)),
            ("trailing zero declet", with(&one, |b| b.push(0))),
            ("extra zero byte", with(&ten_digits, |b| b.push(0))),
            ("negative, trailing zero declet", {
                with(&minus_one_and_half, |b| b.extend([0, 0]))
            }),
            ("negative, non-zero padding", {
                with(&minus_one_and_half, |b| *b.last_mut().unwrap() |= 0x01)
            }),
        ];
        for base in [&one, &ten_digits, &minus_one_and_half] {
            assert!(decode_to_parts(base).is_ok(), "canonical {base:02X?}");
        }
        for (name, bytes) in cases {
            assert_eq!(
                decode_to_parts(&bytes).err(),
                Some(DecodeError::NonCanonical),
                "{name}: {bytes:02X?}"
            );
            let mut buf = [0u8; 64];
            assert_eq!(
                decode_to_buf(&bytes, &mut buf).err(),
                Some(DecodeError::NonCanonical),
                "{name}: {bytes:02X?} (decode_to_buf)"
            );
        }
    }

    #[test]
    fn test_decode_to_buf_rejects_64_bit_gamma_run() {
        // Sign `10`, then a run of exactly 64 ones: rebuilding the exponent
        // would shift a u64 by 64. decode_to_parts refused this already, but
        // decode_to_buf (behind Display) panicked in debug builds.
        let mut bytes = vec![0xBF];
        bytes.extend([0xFF; 7]);
        bytes.push(0xC0);
        bytes.extend([0x00; 9]);
        bytes.push(0x10);
        assert_eq!(
            decode_to_parts(&bytes).err(),
            Some(DecodeError::InvalidGammaCode)
        );
        let mut buf = [0u8; 64];
        assert_eq!(
            decode_to_buf(&bytes, &mut buf).err(),
            Some(DecodeError::InvalidGammaCode)
        );
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
