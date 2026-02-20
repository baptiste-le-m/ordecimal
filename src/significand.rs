use crate::error::{DecodeError, DecodeResult};
use crate::gamma::{BitReader, BitWriter};

/// Encode the significand directly into the provided [`BitWriter`].
///
/// Uses tetrade (4 bits) for the first digit and declets (10 bits per 3 digits)
/// for remaining digits. If `negative` is true, encodes `10 - m` instead of `m`.
///
/// Writing directly to the caller's [`BitWriter`] avoids an intermediate allocation
/// and prevents padding bits from leaking into the output.
pub fn encode_significand(writer: &mut BitWriter, digits: &[u8], negative: bool) {
    if digits.is_empty() {
        return;
    }

    if negative {
        encode_complemented_digits(writer, digits);
    } else {
        encode_digits_to_writer(writer, digits);
    }
}

/// Encode digits that need 10-complement without allocating a Vec.
///
/// Performs the complement arithmetic inline while encoding each group.
fn encode_complemented_digits(writer: &mut BitWriter, digits: &[u8]) {
    // Compute 10 - m inline:
    // The complement of d0.d1d2d3... is computed by subtracting from 10.000...
    // First digit: (10 - d0) if no borrow propagates from fractional part,
    // otherwise (9 - d0). We need to compute the borrow chain from right to left.
    //
    // To avoid allocation, we precompute whether there's a borrow propagating
    // up to each position. A borrow occurs at position i if all digits from
    // position i+1 to the end are zero (meaning no borrow is absorbed).
    //
    // Actually, the simpler approach: the complement of d0.d1d2...dn is:
    //   - Last non-zero digit dk: complement is (10 - dk)
    //   - All digits di between first and last non-zero: complement is (9 - di)
    //   - First digit d0: complement is (9 - d0) if there was any non-zero digit after,
    //     otherwise (10 - d0)
    //   - Trailing zeros after last non-zero digit remain 0
    //
    // This is standard decimal subtraction from 10.000...

    // Find the last non-zero digit position
    let last_nonzero = digits.iter().rposition(|&d| d != 0).unwrap_or(0);

    // Encode first digit (tetrade)
    let first_complemented = if last_nonzero == 0 {
        10 - digits[0]
    } else {
        9 - digits[0]
    };
    writer.write_bits(u64::from(first_complemented), 4);

    // Encode remaining digits in groups of 3 (declets)
    let mut pos = 1;
    while pos < digits.len() {
        let mut declet_value = 0u16;
        for i in 0..3 {
            let idx = pos + i;
            let digit = if idx < digits.len() {
                let d = digits[idx];
                match idx.cmp(&last_nonzero) {
                    std::cmp::Ordering::Less => 9 - d,
                    std::cmp::Ordering::Equal => 10 - d,
                    std::cmp::Ordering::Greater => 0, // trailing zeros remain 0
                }
            } else {
                0 // padding
            };
            declet_value = declet_value * 10 + u16::from(digit);
        }
        writer.write_bits(u64::from(declet_value), 10);
        pos += 3;
    }
}

/// Helper function to encode digits directly to a [`BitWriter`]
#[inline]
fn encode_digits_to_writer(writer: &mut BitWriter, digits: &[u8]) {
    // Encode first digit as tetrade (4 bits)
    writer.write_bits(u64::from(digits[0]), 4);

    // Encode remaining digits in groups of 3 (declets)
    let mut pos = 1;
    while pos < digits.len() {
        let mut declet_value = 0u16;

        // Process up to 3 digits
        for i in 0..3 {
            if pos + i < digits.len() {
                let digit = digits[pos + i];
                declet_value = declet_value * 10 + u16::from(digit);
            } else {
                // Pad with zeros
                declet_value *= 10;
            }
        }

        // Write 10 bits
        writer.write_bits(u64::from(declet_value), 10);
        pos += 3;
    }
}

/// Compute 10 - m in-place, overwriting `digits`.
///
/// For example: [1, 0, 3, 2] (1.032) → [8, 9, 6, 8] (8.968)
fn compute_complement_in_place(digits: &mut [u8]) {
    let mut borrow = 0u8;

    // Start from the last digit (rightmost)
    for i in (0..digits.len()).rev() {
        let minuend = if i == 0 { 10u8 } else { 0u8 };
        let sub = digits[i] + borrow;
        if minuend < sub {
            digits[i] = minuend + 10 - sub;
            borrow = 1;
        } else {
            digits[i] = minuend - sub;
            borrow = 0;
        }
    }
}

/// Decode the significand from tetrade and declets
///
/// If negative is true, decodes as 10 - m (reverses the complement applied during encoding)
///
/// # Errors
///
/// Returns [`DecodeError`] if the reader runs out of bits or encounters
/// invalid tetrade/declet values.
pub fn decode_significand(reader: &mut BitReader, negative: bool) -> DecodeResult<Vec<u8>> {
    // Read first digit (tetrade - 4 bits)
    if !reader.has_bits() {
        return Err(DecodeError::UnexpectedEndOfInput);
    }

    // Pre-allocate: 1 tetrade digit + 3 digits per declet
    let remaining = reader.remaining_bits();
    let num_declets = remaining.saturating_sub(4) / 10;
    let mut digits = Vec::with_capacity(1 + num_declets * 3);

    #[allow(clippy::cast_possible_truncation)]
    let first_tetrade = reader.read_bits(4)? as u8;
    if first_tetrade > 9 {
        return Err(DecodeError::InvalidTetrade(first_tetrade));
    }

    digits.push(first_tetrade);

    // Read remaining digits as declets (10 bits each)
    while reader.remaining_bits() >= 10 {
        #[allow(clippy::cast_possible_truncation)]
        let declet = reader.read_bits(10)? as u16;
        if declet > 999 {
            return Err(DecodeError::InvalidDeclet(declet));
        }

        // Convert declet to 3 digits
        #[allow(clippy::cast_possible_truncation)]
        let d1 = (declet / 100) as u8;
        #[allow(clippy::cast_possible_truncation)]
        let d2 = ((declet / 10) % 10) as u8;
        #[allow(clippy::cast_possible_truncation)]
        let d3 = (declet % 10) as u8;

        digits.push(d1);
        digits.push(d2);
        digits.push(d3);
    }

    // For negative numbers, reverse the complement in-place: original = 10 - encoded
    if negative {
        compute_complement_in_place(&mut digits);
    }

    // Validate significand is in range [1, 10)
    if digits.is_empty() {
        return Err(DecodeError::InvalidSignificand(
            "empty significand".to_string(),
        ));
    }

    // First digit must be 1-9
    if digits[0] == 0 || digits[0] > 9 {
        return Err(DecodeError::InvalidSignificand(format!(
            "first digit is {}",
            digits[0]
        )));
    }

    Ok(digits)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Remove trailing zeros from significand
    fn strip_trailing_zeros(digits: &[u8]) -> &[u8] {
        let mut end = digits.len();
        while end > 1 && digits[end - 1] == 0 {
            end -= 1;
        }
        &digits[..end]
    }

    /// Helper: encode significand into bytes using a fresh BitWriter
    fn encode_sig_to_bytes(digits: &[u8], negative: bool) -> Vec<u8> {
        let mut writer = BitWriter::new();
        encode_significand(&mut writer, digits, negative);
        writer.into_bytes()
    }

    #[test]
    fn test_encode_decode_positive() {
        let digits = vec![1, 0, 3, 2];
        let encoded = encode_sig_to_bytes(&digits, false);

        let mut reader = BitReader::new(&encoded);
        let decoded = decode_significand(&mut reader, false).unwrap();

        assert_eq!(decoded, digits);
    }

    #[test]
    fn test_encode_decode_negative() {
        // For -1.032, we encode 10 - 1.032 = 8.968
        let digits = vec![1, 0, 3, 2];
        let encoded = encode_sig_to_bytes(&digits, true);

        let mut reader = BitReader::new(&encoded);
        let decoded = decode_significand(&mut reader, true).unwrap();

        assert_eq!(decoded, digits);
    }

    #[test]
    fn test_significand_from_paper() {
        // From paper: 7.07106 -> 7 071 060
        let digits = vec![7, 0, 7, 1, 0, 6];
        let encoded = encode_sig_to_bytes(&digits, false);

        let mut reader = BitReader::new(&encoded);
        let decoded = decode_significand(&mut reader, false).unwrap();

        // Decoded might have extra trailing zeros due to padding
        assert_eq!(&decoded[..6], &digits[..]);
    }

    #[test]
    fn test_strip_trailing() {
        let digits = vec![1, 2, 3, 0, 0, 0];
        let stripped = strip_trailing_zeros(&digits);
        assert_eq!(stripped, &[1, 2, 3]);

        let digits2 = vec![1, 0, 0];
        let stripped2 = strip_trailing_zeros(&digits2);
        assert_eq!(stripped2, &[1]);
    }
}
