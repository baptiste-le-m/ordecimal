use crate::decoder::{decode_to_buf, decode_to_parts, DecodedParts};
use crate::encoder::{encode_from_parts, POSITIVE_ZERO_BYTE};
use crate::error::{DecodeError, EncodeError, EncodeResult};
use std::cmp::Ordering;
use std::fmt;
use std::fmt::Write as _;
use std::hash::{Hash, Hasher};
use std::str::FromStr;

/// Represents a decimal number in pre-encoded STEM format.
///
/// This struct stores the decimal as encoded bytes, providing:
/// - Zero-copy access via `as_bytes()`
/// - Direct byte comparison for Ord (order-preserving)
/// - Smaller memory footprint than storing semantic fields
///
/// All values are finite, non-NaN decimals.  Special values (±∞, NaN, −0)
/// are **not** representable; attempts to create them via parsing or
/// conversion return an error.
#[derive(Debug, Clone)]
pub struct Decimal {
    bytes: Vec<u8>,
}

impl Decimal {
    /// Create from pre-encoded bytes without validation
    #[must_use]
    pub const fn from_bytes_unchecked(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }

    /// Create from pre-encoded bytes with validation.
    ///
    /// # Errors
    ///
    /// Returns [`DecodeError`] if the bytes do not represent a valid encoding.
    /// Byte patterns that previously encoded special values (±∞, NaN, −0) are
    /// now rejected.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
        // Single-byte 0x80 is positive zero — the only valid single-byte encoding.
        if bytes == [POSITIVE_ZERO_BYTE] {
            return Ok(Self {
                bytes: bytes.to_vec(),
            });
        }
        // Validate by attempting to decode
        decode_to_parts(bytes)?;
        Ok(Self {
            bytes: bytes.to_vec(),
        })
    }

    /// Get the encoded bytes (zero-copy)
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Consume and return the encoded bytes
    #[must_use]
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Check if this is zero
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.bytes.len() == 1 && self.bytes[0] == POSITIVE_ZERO_BYTE
    }

    /// Create zero (positive zero)
    #[must_use]
    pub fn zero() -> Self {
        Self {
            bytes: vec![POSITIVE_ZERO_BYTE],
        }
    }

    /// Parse a decimal from string and encode immediately (internal helper)
    #[allow(clippy::too_many_lines)]
    fn parse_and_encode(s: &str) -> EncodeResult<Self> {
        let s = s.trim();

        // Reject special value strings
        if s.eq_ignore_ascii_case("inf")
            || s.eq_ignore_ascii_case("+inf")
            || s.eq_ignore_ascii_case("infinity")
            || s.eq_ignore_ascii_case("+infinity")
            || s.eq_ignore_ascii_case("-inf")
            || s.eq_ignore_ascii_case("-infinity")
            || s.eq_ignore_ascii_case("nan")
        {
            return Err(EncodeError::InvalidFormat(
                "special values (infinity, NaN) are not supported".to_string(),
            ));
        }

        // Check for negative
        #[allow(clippy::option_if_let_else)]
        let (positive, s) = if let Some(stripped) = s.strip_prefix('-') {
            (false, stripped)
        } else if let Some(stripped) = s.strip_prefix('+') {
            (true, stripped)
        } else {
            (true, s)
        };

        // Reject empty or digit-free inputs (e.g. "", ".", "+", "-")
        if s.is_empty() || !s.bytes().any(|b| b.is_ascii_digit()) {
            return Err(EncodeError::InvalidFormat(
                "input contains no digits".to_string(),
            ));
        }

        // Handle scientific notation: split on 'e' or 'E'
        // e.g. "1.5e10" → coefficient "1.5", sci_exp = +10
        //      "3E-4"   → coefficient "3",   sci_exp = -4
        let (coeff_str, sci_exp): (&str, i64) =
            if let Some(e_pos) = s.bytes().position(|b| b == b'e' || b == b'E') {
                let coeff = &s[..e_pos];
                let exp_str = &s[e_pos + 1..];
                if exp_str.is_empty() || coeff.is_empty() {
                    return Err(EncodeError::InvalidFormat(
                        "invalid scientific notation".to_string(),
                    ));
                }
                let exp: i64 = exp_str.parse().map_err(|_| {
                    EncodeError::InvalidFormat(format!("invalid exponent: {exp_str}"))
                })?;
                (coeff, exp)
            } else {
                (s, 0)
            };

        // Handle zero — map both +0 and -0 to positive zero
        if coeff_str == "0"
            || coeff_str == "0.0"
            || coeff_str.bytes().all(|b| b == b'0' || b == b'.')
        {
            return Ok(Self::zero());
        }

        // Parse the coefficient - split without allocation
        let (integer_part, fractional_part) = match coeff_str.find('.') {
            Some(pos) => {
                let (int, rest) = coeff_str.split_at(pos);
                if rest[1..].contains('.') {
                    return Err(EncodeError::InvalidFormat(
                        "multiple decimal points".to_string(),
                    ));
                }
                (int, &rest[1..])
            }
            None => (coeff_str, ""),
        };

        // Validate all characters are digits (no intermediate String allocation)
        for b in integer_part.bytes().chain(fractional_part.bytes()) {
            if !b.is_ascii_digit() {
                return Err(EncodeError::InvalidFormat(format!(
                    "invalid digit: {}",
                    b as char
                )));
            }
        }

        // Count leading zeros in the concatenated digit stream (integer_part ++ fractional_part)
        let leading_zeros = integer_part
            .bytes()
            .chain(fractional_part.bytes())
            .take_while(|&b| b == b'0')
            .count();

        // Count trailing zeros in the concatenated digit stream
        let total_len = integer_part.len() + fractional_part.len();
        let trailing_zeros = fractional_part
            .bytes()
            .rev()
            .chain(integer_part.bytes().rev())
            .take_while(|&b| b == b'0')
            .count();

        let significant_len = total_len - leading_zeros - trailing_zeros;
        if significant_len == 0 {
            // All digits were zero — map to positive zero regardless of sign
            return Ok(Self::zero());
        }

        // Calculate the raw exponent from the position of the decimal point
        // relative to the first significant digit, then adjust by sci_exp.
        let decimal_point_position = integer_part.trim_start_matches('0').len();

        // raw_exp is the exponent in scientific notation:
        //   coefficient = d0.d1d2... × 10^raw_exp
        // For integer part with significant digits: raw_exp = len(integer_significant) - 1
        // For purely fractional (0.00x...): raw_exp = -(leading_zeros_in_frac + 1)
        let raw_exp: i64 = if decimal_point_position > 0 {
            (decimal_point_position as i64) - 1
        } else {
            let frac_leading_zeros =
                fractional_part.len() - fractional_part.trim_start_matches('0').len();
            -((frac_leading_zeros as i64) + 1)
        };

        // Apply the scientific notation exponent offset
        let final_exp = raw_exp + sci_exp;

        #[allow(clippy::cast_sign_loss)]
        let (exponent, exponent_positive) = if final_exp >= 0 {
            (final_exp as u64, true)
        } else {
            (final_exp.unsigned_abs(), false)
        };

        // Encode significand using a stack buffer when possible (covers all
        // DynamoDB numbers ≤ 38 digits), falling back to a Vec for very large
        // arbitrary-precision values.
        let sig_iter = integer_part
            .bytes()
            .chain(fractional_part.bytes())
            .skip(leading_zeros)
            .take(significant_len)
            .map(|b| b - b'0');

        let bytes = if significant_len <= 64 {
            let mut buf = [0u8; 64];
            for (i, d) in sig_iter.enumerate() {
                buf[i] = d;
            }
            encode_from_parts(
                positive,
                exponent_positive,
                exponent,
                &buf[..significant_len],
            )
        } else {
            let significand: Vec<u8> = sig_iter.collect();
            encode_from_parts(positive, exponent_positive, exponent, &significand)
        };

        Ok(Self { bytes })
    }
}

impl FromStr for Decimal {
    type Err = EncodeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse_and_encode(s)
    }
}

/// Maximum exponent magnitude for plain positional output in
/// [`Decimal::to_plain_string`].  Beyond this threshold the method falls back
/// to scientific notation (`"1.23e500"`) to avoid unbounded memory allocation.
/// 1000 is generous: DynamoDB supports at most 10^125, and IEEE decimal128
/// goes up to 10^6144.
const MAX_PLAIN_EXPONENT: u64 = 1000;

impl Decimal {
    /// Produce a decimal string that can round-trip through [`FromStr`].
    ///
    /// For moderate exponents (magnitude ≤ 1000) the output is a plain
    /// positional string (`"123"`, `"0.005"`).  For extreme exponents the
    /// method falls back to scientific notation (`"1e100200000000"`) to
    /// prevent unbounded memory allocation.
    pub fn to_plain_string(&self) -> String {
        // Fast path: zero (single byte)
        if self.is_zero() {
            return "0".to_string();
        }

        // Try decoding to a stack buffer first (no heap allocation for ≤1536
        // significant digits, which covers all practical use cases).
        let mut sig_buf = [0u8; 1536];
        match decode_to_buf(&self.bytes, &mut sig_buf) {
            Ok(parts) => {
                let sig_end = sig_buf[..parts.sig_len]
                    .iter()
                    .rposition(|&x| x != 0)
                    .map_or(1, |p| p + 1);
                for b in &mut sig_buf[..sig_end] {
                    *b += b'0';
                }
                // SAFETY: digit values 0–9 + b'0' = b'0'..=b'9', valid ASCII
                let sig = unsafe { std::str::from_utf8_unchecked(&sig_buf[..sig_end]) };
                Self::format_plain_or_scientific(sig, &parts)
            }
            // Stack buffer too small — fall back to heap-based decode
            Err(_) => self.to_plain_string_heap(),
        }
    }

    /// Heap-based fallback for `to_plain_string` when the significand exceeds
    /// the 1536-byte stack buffer.
    fn to_plain_string_heap(&self) -> String {
        let decoded = match decode_to_parts(&self.bytes) {
            Ok(d) => d,
            Err(_) => return "<invalid>".to_string(),
        };

        let sig_end = decoded
            .significand
            .iter()
            .rposition(|&x| x != 0)
            .map_or(1, |p| p + 1);
        let mut sig_vec: Vec<u8> = decoded.significand[..sig_end].to_vec();
        for b in &mut sig_vec {
            *b += b'0';
        }
        // SAFETY: digit values 0–9 + b'0' = b'0'..=b'9', valid ASCII
        let sig = unsafe { std::str::from_utf8_unchecked(&sig_vec) };

        let parts = DecodedParts {
            positive: decoded.positive,
            exponent_positive: decoded.exponent_positive,
            exponent: decoded.exponent,
            sig_len: decoded.significand.len(),
        };
        Self::format_plain_or_scientific(sig, &parts)
    }

    /// Core formatting logic shared by stack-buffer and heap-buffer paths.
    fn format_plain_or_scientific(sig: &str, parts: &DecodedParts) -> String {
        let mut out = String::with_capacity(sig.len() + 8);
        if !parts.positive {
            out.push('-');
        }

        // For extreme exponents, fall back to scientific notation to avoid
        // allocating a string with billions of zero-padding characters.
        if parts.exponent > MAX_PLAIN_EXPONENT {
            return Self::format_scientific(&mut out, sig, parts);
        }

        if parts.exponent_positive || parts.exponent == 0 {
            let int_digits = parts.exponent as usize + 1;

            if int_digits >= sig.len() {
                // All significand digits in integer part; pad with trailing zeros
                out.push_str(sig);
                const ZEROS: &str = "0000000000000000000000000000000000000000";
                let mut remaining = int_digits - sig.len();
                while remaining > 0 {
                    let chunk = remaining.min(ZEROS.len());
                    out.push_str(&ZEROS[..chunk]);
                    remaining -= chunk;
                }
            } else {
                // Split: some digits before the point, some after
                out.push_str(&sig[..int_digits]);
                out.push('.');
                out.push_str(&sig[int_digits..]);
            }
        } else {
            // Negative exponent: number < 1 → "0." + (exponent-1) leading zeros + sig
            out.push_str("0.");
            const ZEROS: &str = "0000000000000000000000000000000000000000";
            let mut remaining = parts.exponent as usize - 1;
            while remaining > 0 {
                let chunk = remaining.min(ZEROS.len());
                out.push_str(&ZEROS[..chunk]);
                remaining -= chunk;
            }
            out.push_str(sig);
        }

        out
    }

    /// Produce a scientific-notation string (`"1.23e5"`, `"-4.56e-3"`)
    /// that can round-trip through [`FromStr`].
    ///
    /// Unlike [`to_plain_string`](Self::to_plain_string), this method **always**
    /// uses `e`-notation, regardless of exponent magnitude. Zero is returned
    /// as `"0e0"`.
    pub fn to_scientific_string(&self) -> String {
        // Fast path: zero
        if self.is_zero() {
            return "0e0".to_string();
        }

        let decoded = match decode_to_parts(&self.bytes) {
            Ok(d) => d,
            Err(_) => return "<invalid>".to_string(),
        };

        let sig_end = decoded
            .significand
            .iter()
            .rposition(|&x| x != 0)
            .map_or(1, |p| p + 1);

        let mut sig_vec: Vec<u8> = decoded.significand[..sig_end].to_vec();

        for b in &mut sig_vec {
            *b += b'0';
        }
        let sig = unsafe { std::str::from_utf8_unchecked(&sig_vec) };

        let parts = DecodedParts {
            positive: decoded.positive,
            exponent_positive: decoded.exponent_positive,
            exponent: decoded.exponent,
            sig_len: decoded.significand.len(),
        };
        let mut out = String::with_capacity(sig.len() + 8);
        if !parts.positive {
            out.push('-');
        }
        Self::format_scientific(&mut out, sig, &parts)
    }

    /// Format as `d.dddeSIGNexp` into the already-sign-prefixed `out` buffer.
    fn format_scientific(out: &mut String, sig: &str, parts: &DecodedParts) -> String {
        out.push_str(&sig[..1]);
        if sig.len() > 1 {
            out.push('.');
            out.push_str(&sig[1..]);
        }
        out.push('e');
        if !parts.exponent_positive {
            out.push('-');
        }
        // Format exponent without pulling in `write!` / `format!`
        let mut exp_buf = [0u8; 20];
        let (start, end) = fmt_u64(parts.exponent, &mut exp_buf);
        // SAFETY: digits are b'0'..=b'9', valid ASCII
        out.push_str(unsafe { std::str::from_utf8_unchecked(&exp_buf[start..end]) });
        std::mem::take(out)
    }
}

/// Format a `u64` into a stack buffer as ASCII decimal.
/// Returns `(start, end)` indices into `buf` for the formatted slice.
#[inline]
fn fmt_u64(mut n: u64, buf: &mut [u8; 20]) -> (usize, usize) {
    if n == 0 {
        buf[19] = b'0';
        return (19, 20);
    }
    let mut pos = 20usize;
    while n > 0 {
        pos -= 1;
        #[allow(clippy::cast_possible_truncation)]
        {
            buf[pos] = b'0' + (n % 10) as u8;
        }
        n /= 10;
    }
    (pos, 20)
}

impl fmt::Display for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Fast path: zero (single byte — no decode needed)
        if self.is_zero() {
            return f.write_str("0");
        }

        // Decode to stack buffer — no heap allocation for significand
        let mut sig_buf = [0u8; 1536];
        let parts = match decode_to_buf(&self.bytes, &mut sig_buf) {
            Ok(p) => p,
            Err(_) => return f.write_str("<invalid>"),
        };

        // Strip trailing zeros from significand padding
        let sig_end = sig_buf[..parts.sig_len]
            .iter()
            .rposition(|&x| x != 0)
            .map_or(1, |p| p + 1);

        // Convert digit values to ASCII in-place
        for b in &mut sig_buf[..sig_end] {
            *b += b'0';
        }

        // Write sign
        if !parts.positive {
            f.write_str("-")?;
        }

        // SAFETY: digit values 0–9 + b'0' = b'0'..=b'9', all valid ASCII/UTF-8
        let sig_str = unsafe { std::str::from_utf8_unchecked(&sig_buf[..sig_end]) };

        // Write "d.ddd" — first digit, decimal point, remaining digits
        f.write_str(&sig_str[..1])?;
        f.write_str(".")?;
        if sig_end > 1 {
            f.write_str(&sig_str[1..])?;
        } else {
            f.write_str("0")?;
        }

        // Write " × 10^"
        f.write_str(" \u{00d7} 10^")?;
        if !parts.exponent_positive {
            f.write_str("-")?;
        }

        // Format exponent without write! macro overhead
        let mut exp_buf = [0u8; 20];
        let (start, end) = fmt_u64(parts.exponent, &mut exp_buf);
        // SAFETY: digits are b'0'..=b'9', valid ASCII
        f.write_str(unsafe { std::str::from_utf8_unchecked(&exp_buf[start..end]) })
    }
}

impl PartialEq for Decimal {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl Eq for Decimal {}

impl PartialOrd for Decimal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Decimal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.bytes.cmp(&other.bytes)
    }
}

impl Hash for Decimal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}

impl Default for Decimal {
    /// Returns positive zero.
    fn default() -> Self {
        Self::zero()
    }
}

/// Extract decimal digits from a `u64` into a stack buffer.
///
/// Returns the number of digits written. Digits are stored most-significant
/// first in `buf[0..len]`. Zero produces a single digit `0`.
///
/// Uses native `u64` arithmetic (faster than `u128` division on most platforms).
fn u64_to_digits(mut value: u64, buf: &mut [u8; 20]) -> usize {
    if value == 0 {
        buf[0] = 0;
        return 1;
    }

    let mut pos = 20;
    while value > 0 {
        pos -= 1;
        #[allow(clippy::cast_possible_truncation)]
        {
            buf[pos] = (value % 10) as u8;
        }
        value /= 10;
    }

    let len = 20 - pos;
    buf.copy_within(pos..20, 0);
    len
}

/// Extract decimal digits from a `u128` into a stack buffer.
///
/// Returns the number of digits written. Digits are stored most-significant
/// first in `buf[0..len]`. Zero produces a single digit `0`.
fn u128_to_digits(mut value: u128, buf: &mut [u8; 39]) -> usize {
    if value == 0 {
        buf[0] = 0;
        return 1;
    }

    // Extract digits in reverse order
    let mut pos = 39;
    while value > 0 {
        pos -= 1;
        #[allow(clippy::cast_possible_truncation)]
        {
            buf[pos] = (value % 10) as u8;
        }
        value /= 10;
    }

    // Shift digits to the front of the buffer
    let len = 39 - pos;
    buf.copy_within(pos..39, 0);
    len
}

/// Build a [`Decimal`] from a `u64` magnitude and a sign flag.
///
/// Uses native `u64` division (faster than `u128`) and a 20-byte stack buffer.
fn from_u64_with_sign(value: u64, positive: bool) -> Decimal {
    if value == 0 {
        return Decimal::zero();
    }

    let mut buf = [0u8; 20];
    let len = u64_to_digits(value, &mut buf);
    let digits = &buf[..len];

    #[allow(clippy::cast_possible_truncation)]
    let exponent = (len - 1) as u64;

    let sig_end = digits.iter().rposition(|&d| d != 0).map_or(1, |p| p + 1);
    let significand = &digits[..sig_end];

    let bytes = encode_from_parts(positive, true, exponent, significand);
    Decimal { bytes }
}

/// Core conversion: build a [`Decimal`] from an unsigned `u128` magnitude and a sign flag.
///
/// Uses a `[u8; 39]` stack buffer for digit extraction — no heap allocation
/// beyond the final encoded [`Vec<u8>`].
fn from_unsigned_with_sign(value: u128, positive: bool) -> Decimal {
    if value == 0 {
        return Decimal::zero();
    }

    let mut buf = [0u8; 39];
    let len = u128_to_digits(value, &mut buf);
    let digits = &buf[..len];

    // exponent = number_of_digits - 1, always non-negative for integers
    #[allow(clippy::cast_possible_truncation)]
    let exponent = (len - 1) as u64;

    // Strip trailing zeros from the significand (they're encoded in the exponent)
    let sig_end = digits.iter().rposition(|&d| d != 0).map_or(1, |p| p + 1);
    let significand = &digits[..sig_end];

    let bytes = encode_from_parts(positive, true, exponent, significand);
    Decimal { bytes }
}

impl From<u64> for Decimal {
    fn from(value: u64) -> Self {
        from_u64_with_sign(value, true)
    }
}

impl From<i64> for Decimal {
    fn from(value: i64) -> Self {
        #[allow(clippy::cast_sign_loss)]
        if value >= 0 {
            from_u64_with_sign(value as u64, true)
        } else if value == i64::MIN {
            // i64::MIN.unsigned_abs() doesn't fit in i64, use u64 directly
            from_u64_with_sign(value.unsigned_abs(), false)
        } else {
            from_u64_with_sign((-value) as u64, false)
        }
    }
}

impl From<u128> for Decimal {
    fn from(value: u128) -> Self {
        from_unsigned_with_sign(value, true)
    }
}

impl From<i128> for Decimal {
    fn from(value: i128) -> Self {
        #[allow(clippy::cast_sign_loss)]
        let (positive, magnitude) = if value >= 0 {
            (true, value as u128)
        } else {
            // i128::MIN: -(i128::MIN as i128) overflows, but
            // (i128::MIN as u128) == 2^127 which is the correct magnitude
            (false, value.unsigned_abs())
        };
        from_unsigned_with_sign(magnitude, positive)
    }
}

// Smaller unsigned types — widen to u64
impl From<u8> for Decimal {
    fn from(value: u8) -> Self {
        Self::from(u64::from(value))
    }
}

impl From<u16> for Decimal {
    fn from(value: u16) -> Self {
        Self::from(u64::from(value))
    }
}

impl From<u32> for Decimal {
    fn from(value: u32) -> Self {
        Self::from(u64::from(value))
    }
}

// Smaller signed types — widen to i64
impl From<i8> for Decimal {
    fn from(value: i8) -> Self {
        Self::from(i64::from(value))
    }
}

impl From<i16> for Decimal {
    fn from(value: i16) -> Self {
        Self::from(i64::from(value))
    }
}

impl From<i32> for Decimal {
    fn from(value: i32) -> Self {
        Self::from(i64::from(value))
    }
}

/// Fixed-capacity stack buffer that implements `fmt::Write`.
///
/// Used by the `TryFrom<f64>` / `TryFrom<f32>` impls to format a float into
/// a string without heap allocation.  25 bytes is enough for any `f64`
/// in scientific notation: sign (1) + leading digit (1) + decimal point (1) +
/// up to 16 fractional digits + `e` (1) + exponent sign (1) + exponent
/// digits (up to 3) = 24 bytes maximum.
struct StackBuf {
    buf: [u8; 25],
    len: usize,
}

impl StackBuf {
    const fn new() -> Self {
        Self {
            buf: [0; 25],
            len: 0,
        }
    }

    fn as_str(&self) -> &str {
        // Safety: fmt::Write for str only writes valid UTF-8
        unsafe { std::str::from_utf8_unchecked(&self.buf[..self.len]) }
    }
}

impl fmt::Write for StackBuf {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let bytes = s.as_bytes();
        let new_len = self.len + bytes.len();
        if new_len > self.buf.len() {
            return Err(fmt::Error);
        }
        self.buf[self.len..new_len].copy_from_slice(bytes);
        self.len = new_len;
        Ok(())
    }
}

impl TryFrom<f64> for Decimal {
    type Error = EncodeError;

    /// Try to convert an [`f64`] to a [`Decimal`](Self).
    ///
    /// Returns `Err` for NaN, +∞, and −∞. Negative zero is mapped to
    /// positive zero.
    fn try_from(value: f64) -> Result<Self, Self::Error> {
        if value.is_nan() {
            return Err(EncodeError::InvalidFormat(
                "NaN is not representable".to_string(),
            ));
        }
        if value.is_infinite() {
            return Err(EncodeError::InvalidFormat(
                "infinity is not representable".to_string(),
            ));
        }
        if value == 0.0 {
            return Ok(Self::zero());
        }

        let mut buf = StackBuf::new();
        // Use scientific (LowerExp) notation so the output is always compact.
        // Rust's `{:e}` produces the shortest roundtrip representation in
        // scientific form (e.g. "1.5e0", "-2.3e-223"), which is guaranteed
        // to fit in 25 bytes for any finite, non-zero f64.
        write!(buf, "{value:e}").expect("f64 scientific notation should fit in 25 bytes");
        // Delegate to FromStr — the string is already validated decimal
        buf.as_str().parse()
    }
}

impl TryFrom<f32> for Decimal {
    type Error = EncodeError;

    fn try_from(value: f32) -> Result<Self, Self::Error> {
        Self::try_from(f64::from(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_positive() {
        let d: Decimal = "123.456".parse().unwrap();
        let decoded = decode_to_parts(d.as_bytes()).unwrap();
        assert!(decoded.positive);
        assert!(decoded.exponent_positive);
        assert_eq!(decoded.exponent, 2);
        // Significand may have trailing zeros from declet padding
        assert!(decoded.significand.starts_with(&[1, 2, 3, 4, 5, 6]));
    }

    #[test]
    fn test_parse_negative() {
        let d: Decimal = "-103.2".parse().unwrap();
        let decoded = decode_to_parts(d.as_bytes()).unwrap();
        assert!(!decoded.positive);
        assert!(decoded.exponent_positive);
        assert_eq!(decoded.exponent, 2);
        // Significand may have trailing zeros from declet padding
        assert!(decoded.significand.starts_with(&[1, 0, 3, 2]));
    }

    #[test]
    fn test_parse_small() {
        let d: Decimal = "0.0405".parse().unwrap();
        let decoded = decode_to_parts(d.as_bytes()).unwrap();
        assert!(decoded.positive);
        assert!(!decoded.exponent_positive);
        assert_eq!(decoded.exponent, 2);
        // Significand may have trailing zeros from declet padding
        assert!(decoded.significand.starts_with(&[4, 0, 5]));
    }

    #[test]
    fn test_parse_zero() {
        let d: Decimal = "0".parse().unwrap();
        assert!(d.is_zero());
    }

    #[test]
    fn test_parse_negative_zero_becomes_positive_zero() {
        let d: Decimal = "-0".parse().unwrap();
        assert!(d.is_zero());
        assert_eq!(d.as_bytes(), Decimal::zero().as_bytes());
    }

    #[test]
    fn test_parse_negative_zero_variants() {
        // All forms of -0 should map to positive zero
        for input in &["-0", "-0.0", "-0.00", "-0e5", "-0.0e-3"] {
            let d: Decimal = input.parse().unwrap();
            assert!(d.is_zero(), "{input} should be zero");
            assert_eq!(
                d.as_bytes(),
                Decimal::zero().as_bytes(),
                "{input} should be positive zero bytes"
            );
        }
    }

    #[test]
    fn test_parse_inf_rejected() {
        assert!("inf".parse::<Decimal>().is_err());
        assert!("+inf".parse::<Decimal>().is_err());
        assert!("-inf".parse::<Decimal>().is_err());
        assert!("infinity".parse::<Decimal>().is_err());
        assert!("+infinity".parse::<Decimal>().is_err());
        assert!("-infinity".parse::<Decimal>().is_err());
        assert!("INF".parse::<Decimal>().is_err());
        assert!("Inf".parse::<Decimal>().is_err());
        assert!("+INFINITY".parse::<Decimal>().is_err());
        assert!("-Infinity".parse::<Decimal>().is_err());
    }

    #[test]
    fn test_parse_nan_rejected() {
        assert!("nan".parse::<Decimal>().is_err());
        assert!("NaN".parse::<Decimal>().is_err());
        assert!("NAN".parse::<Decimal>().is_err());
    }

    #[test]
    fn test_multiple_decimal_points() {
        // Should fail with multiple decimal points
        assert!("123.456.789".parse::<Decimal>().is_err());
        assert!("1.2.3".parse::<Decimal>().is_err());
    }

    #[test]
    fn test_reject_empty_and_bare_inputs() {
        // Empty string
        assert!("".parse::<Decimal>().is_err(), "empty string should fail");
        // Bare sign
        assert!("+".parse::<Decimal>().is_err(), "bare '+' should fail");
        assert!("-".parse::<Decimal>().is_err(), "bare '-' should fail");
        // Bare dot
        assert!(".".parse::<Decimal>().is_err(), "bare '.' should fail");
        // Sign + dot
        assert!("-.".parse::<Decimal>().is_err(), "'-.' should fail");
        assert!("+.".parse::<Decimal>().is_err(), "'+.' should fail");
        // Whitespace only
        assert!("   ".parse::<Decimal>().is_err(), "whitespace should fail");
    }

    // =========================================================================
    // From<integer> tests
    // =========================================================================

    #[test]
    fn test_from_u64_matches_parse() {
        let cases: &[u64] = &[0, 1, 9, 10, 42, 100, 999, 1000, 123456789, u64::MAX];
        for &n in cases {
            let from_int = Decimal::from(n);
            let from_str: Decimal = n.to_string().parse().unwrap();
            assert_eq!(
                from_int.as_bytes(),
                from_str.as_bytes(),
                "From<u64> mismatch for {n}"
            );
        }
    }

    #[test]
    fn test_from_i64_matches_parse() {
        let cases: &[i64] = &[
            i64::MIN,
            -123456789,
            -1000,
            -42,
            -1,
            0,
            1,
            42,
            1000,
            123456789,
            i64::MAX,
        ];
        for &n in cases {
            let from_int = Decimal::from(n);
            let from_str: Decimal = n.to_string().parse().unwrap();
            assert_eq!(
                from_int.as_bytes(),
                from_str.as_bytes(),
                "From<i64> mismatch for {n}"
            );
        }
    }

    #[test]
    fn test_from_i128_extremes() {
        let cases: &[i128] = &[i128::MIN, -1, 0, 1, i128::MAX];
        for &n in cases {
            let from_int = Decimal::from(n);
            let from_str: Decimal = n.to_string().parse().unwrap();
            assert_eq!(
                from_int.as_bytes(),
                from_str.as_bytes(),
                "From<i128> mismatch for {n}"
            );
        }
    }

    #[test]
    fn test_from_u128_max() {
        let from_int = Decimal::from(u128::MAX);
        let from_str: Decimal = u128::MAX.to_string().parse().unwrap();
        assert_eq!(from_int.as_bytes(), from_str.as_bytes());
    }

    #[test]
    fn test_from_small_types() {
        // Verify widening impls produce the same encoding
        assert_eq!(
            Decimal::from(42u8).as_bytes(),
            Decimal::from(42u64).as_bytes()
        );
        assert_eq!(
            Decimal::from(42u16).as_bytes(),
            Decimal::from(42u64).as_bytes()
        );
        assert_eq!(
            Decimal::from(42u32).as_bytes(),
            Decimal::from(42u64).as_bytes()
        );
        assert_eq!(
            Decimal::from(-7i8).as_bytes(),
            Decimal::from(-7i64).as_bytes()
        );
        assert_eq!(
            Decimal::from(-7i16).as_bytes(),
            Decimal::from(-7i64).as_bytes()
        );
        assert_eq!(
            Decimal::from(-7i32).as_bytes(),
            Decimal::from(-7i64).as_bytes()
        );
    }

    #[test]
    fn test_from_u64_order_preserved() {
        let values: Vec<u64> = vec![0, 1, 2, 9, 10, 99, 100, 999, 1000, u64::MAX];
        let decimals: Vec<Decimal> = values.iter().map(|&v| Decimal::from(v)).collect();
        for i in 1..decimals.len() {
            assert!(
                decimals[i - 1] < decimals[i],
                "Order not preserved: {} < {} failed",
                values[i - 1],
                values[i]
            );
        }
    }

    #[test]
    fn test_from_zero_is_positive_zero() {
        let d = Decimal::from(0u64);
        assert!(d.is_zero());
        assert_eq!(d.as_bytes(), Decimal::zero().as_bytes());
    }

    // =========================================================================
    // TryFrom<f64> / TryFrom<f32> tests
    // =========================================================================

    #[test]
    fn test_try_from_f64_matches_parse() {
        let cases: &[f64] = &[1.0, -1.0, 0.5, -0.5, 42.0, 123.456, 0.001, 1e10, 1e-10];
        for &v in cases {
            let from_float = Decimal::try_from(v).unwrap();
            let from_str: Decimal = v.to_string().parse().unwrap();
            assert_eq!(
                from_float.as_bytes(),
                from_str.as_bytes(),
                "TryFrom<f64> mismatch for {v}"
            );
        }
    }

    #[test]
    fn test_try_from_f64_special_values_rejected() {
        assert!(Decimal::try_from(f64::NAN).is_err());
        assert!(Decimal::try_from(f64::INFINITY).is_err());
        assert!(Decimal::try_from(f64::NEG_INFINITY).is_err());
    }

    #[test]
    fn test_try_from_f64_zero() {
        assert!(Decimal::try_from(0.0_f64).unwrap().is_zero());
        // -0.0 maps to positive zero
        let neg_zero = Decimal::try_from(-0.0_f64).unwrap();
        assert!(neg_zero.is_zero());
        assert_eq!(neg_zero.as_bytes(), Decimal::zero().as_bytes());
    }

    #[test]
    fn test_try_from_f64_order_preserved() {
        let values: Vec<f64> = vec![-1000.0, -1.0, -0.001, 0.001, 1.0, 1000.0];
        let decimals: Vec<Decimal> = values
            .iter()
            .map(|&v| Decimal::try_from(v).unwrap())
            .collect();
        for i in 1..decimals.len() {
            assert!(
                decimals[i - 1] < decimals[i],
                "Order not preserved: {} < {} failed",
                values[i - 1],
                values[i]
            );
        }
    }

    #[test]
    fn test_try_from_f32_matches_f64_widening() {
        let v = 2.72_f32;
        let from_f32 = Decimal::try_from(v).unwrap();
        let from_f64 = Decimal::try_from(f64::from(v)).unwrap();
        assert_eq!(from_f32.as_bytes(), from_f64.as_bytes());
    }

    // =========================================================================
    // Hash tests
    // =========================================================================

    #[test]
    fn test_hash_equal_values() {
        use std::collections::hash_map::DefaultHasher;

        let a: Decimal = "42".parse().unwrap();
        let b: Decimal = "42".parse().unwrap();

        let hash_a = {
            let mut h = DefaultHasher::new();
            a.hash(&mut h);
            h.finish()
        };
        let hash_b = {
            let mut h = DefaultHasher::new();
            b.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash_a, hash_b);
    }

    #[test]
    fn test_hash_in_hashset() {
        use std::collections::HashSet;

        let mut set = HashSet::new();
        set.insert("42".parse::<Decimal>().unwrap());
        set.insert("42".parse::<Decimal>().unwrap()); // duplicate
        set.insert("-7".parse::<Decimal>().unwrap());
        set.insert("0".parse::<Decimal>().unwrap());

        assert_eq!(set.len(), 3, "HashSet should deduplicate equal values");
    }

    // =========================================================================
    // Default tests
    // =========================================================================

    #[test]
    fn test_default_is_zero() {
        let d = Decimal::default();
        assert!(d.is_zero());
        assert_eq!(d, Decimal::zero());
    }

    // =========================================================================
    // Scientific notation tests
    // =========================================================================

    #[test]
    fn test_scientific_notation_basic() {
        // 1e10 = 10000000000
        let a: Decimal = "1e10".parse().unwrap();
        let b: Decimal = "10000000000".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_scientific_notation_uppercase() {
        let a: Decimal = "1E10".parse().unwrap();
        let b: Decimal = "10000000000".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_scientific_notation_with_decimal() {
        // 1.5e3 = 1500
        let a: Decimal = "1.5e3".parse().unwrap();
        let b: Decimal = "1500".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_scientific_notation_negative_exponent() {
        // 1.5e-3 = 0.0015
        let a: Decimal = "1.5e-3".parse().unwrap();
        let b: Decimal = "0.0015".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_scientific_notation_positive_exponent_sign() {
        // 1.5e+3 = 1500
        let a: Decimal = "1.5e+3".parse().unwrap();
        let b: Decimal = "1500".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_scientific_notation_negative_value() {
        // -2.5e4 = -25000
        let a: Decimal = "-2.5e4".parse().unwrap();
        let b: Decimal = "-25000".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_scientific_notation_zero_exponent() {
        // 42e0 = 42
        let a: Decimal = "42e0".parse().unwrap();
        let b: Decimal = "42".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_scientific_notation_zero_coefficient() {
        let a: Decimal = "0e10".parse().unwrap();
        assert!(a.is_zero());
    }

    #[test]
    fn test_scientific_notation_small_to_large() {
        // 3.14e-2 = 0.0314
        let a: Decimal = "3.14e-2".parse().unwrap();
        let b: Decimal = "0.0314".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn test_scientific_notation_order_preserved() {
        let values: Vec<Decimal> = vec![
            "-1e10".parse().unwrap(),
            "-1e2".parse().unwrap(),
            "1e-10".parse().unwrap(),
            "1e0".parse().unwrap(),
            "1e2".parse().unwrap(),
            "1e10".parse().unwrap(),
        ];
        for i in 1..values.len() {
            assert!(
                values[i - 1] < values[i],
                "order broken: {} should be < {}",
                i - 1,
                i
            );
        }
    }

    #[test]
    fn test_scientific_notation_invalid() {
        // Empty exponent
        assert!("1e".parse::<Decimal>().is_err());
        // Empty coefficient
        assert!("e10".parse::<Decimal>().is_err());
        // Non-numeric exponent
        assert!("1ex".parse::<Decimal>().is_err());
    }

    #[test]
    fn test_scientific_notation_dynamodb_style() {
        // DynamoDB sends numbers like "1E-130" (min positive) and "9.9999999999999999999999999999999999999E+125"
        let min_pos: Decimal = "1E-130".parse().unwrap();
        let max_pos: Decimal = "9.9999999999999999999999999999999999999E+125"
            .parse()
            .unwrap();
        assert!(min_pos < max_pos);

        // Verify min positive is greater than zero
        assert!(Decimal::zero() < min_pos);
    }

    // Regression tests for fuzz-discovered OOM in to_plain_string (extreme exponents)
    #[test]
    fn to_plain_string_extreme_exponent_no_oom() {
        // These inputs previously caused to_plain_string to allocate billions
        // of zero-padding bytes.  Now it falls back to scientific notation.
        let cases = ["1E100200000000", "15.001001080E01084888800", "1e-999999999"];
        for input in &cases {
            let d: Decimal = input.parse().unwrap();
            let plain = d.to_plain_string();
            // Must be compact (scientific notation), not positional
            assert!(
                plain.len() < 10_000,
                "to_plain_string too large ({} bytes) for input {input:?}",
                plain.len(),
            );
            // Must roundtrip
            let d2: Decimal = plain.parse().unwrap();
            assert_eq!(
                d.as_bytes(),
                d2.as_bytes(),
                "roundtrip failed for {input:?}"
            );
        }
    }

    #[test]
    fn to_plain_string_uses_positional_for_moderate_exponents() {
        // Exponents within the threshold should still produce plain positional output
        let d: Decimal = "1e5".parse().unwrap();
        assert_eq!(d.to_plain_string(), "100000");

        let d: Decimal = "1.23e10".parse().unwrap();
        assert_eq!(d.to_plain_string(), "12300000000");

        let d: Decimal = "0.00123".parse().unwrap();
        assert_eq!(d.to_plain_string(), "0.00123");
    }

    #[test]
    fn to_plain_string_scientific_roundtrip() {
        // Large positive exponent
        let d: Decimal = "1.5e5000".parse().unwrap();
        let plain = d.to_plain_string();
        assert!(
            plain.contains('e'),
            "expected scientific notation, got {plain:?}"
        );
        let d2: Decimal = plain.parse().unwrap();
        assert_eq!(d.as_bytes(), d2.as_bytes());

        // Large negative exponent
        let d: Decimal = "1.5e-5000".parse().unwrap();
        let plain = d.to_plain_string();
        assert!(
            plain.contains('e'),
            "expected scientific notation, got {plain:?}"
        );
        let d2: Decimal = plain.parse().unwrap();
        assert_eq!(d.as_bytes(), d2.as_bytes());

        // Negative number with large exponent
        let d: Decimal = "-3.14e9999".parse().unwrap();
        let plain = d.to_plain_string();
        assert!(plain.starts_with('-'), "expected negative sign");
        assert!(
            plain.contains('e'),
            "expected scientific notation, got {plain:?}"
        );
        let d2: Decimal = plain.parse().unwrap();
        assert_eq!(d.as_bytes(), d2.as_bytes());
    }

    #[test]
    fn test_from_bytes_rejects_old_special_values() {
        // -inf
        assert!(Decimal::from_bytes(&[0x00]).is_err());
        // -0
        assert!(Decimal::from_bytes(&[0x40]).is_err());
        // +inf
        assert!(Decimal::from_bytes(&[0xC0]).is_err());
        // NaN
        assert!(Decimal::from_bytes(&[0xE0]).is_err());
    }

    #[test]
    fn test_from_bytes_accepts_zero() {
        let d = Decimal::from_bytes(&[0x80]).unwrap();
        assert!(d.is_zero());
    }
}
