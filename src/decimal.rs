use crate::decoder::{decode_to_parts, DecodedDecimal, DecodedValue};
use crate::encoder::{encode_from_parts, encode_special_byte};
use crate::error::{DecodeError, EncodeError, EncodeResult};
use std::cmp::Ordering;
use std::fmt;
use std::fmt::Write as _;
use std::str::FromStr;

/// Special decimal values
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecialValue {
    NegativeInfinity,
    NegativeZero,
    PositiveZero,
    PositiveInfinity,
    NaN,
}

/// Represents a decimal number in pre-encoded STEM format
///
/// This struct stores the decimal as encoded bytes, providing:
/// - Zero-copy access via `as_bytes()`
/// - Direct byte comparison for Ord (order-preserving)
/// - Smaller memory footprint than storing semantic fields
///
/// To access semantic fields (sign, exponent, significand), use `decode()`.
///
/// # NaN semantics
///
/// Unlike IEEE 754 floating-point, [`Decimal`] treats NaN as a concrete value:
/// - `NaN == NaN` is **true** (reflexive equality)
/// - NaN has a defined sort position: it is **greater than** all other values,
///   including positive infinity
///
/// This is intentional for use as database sort keys, where
/// every value must have a deterministic, total ordering. Code that expects
/// IEEE 754 NaN behavior (`NaN != NaN`, unordered comparisons) should not
/// rely on [`Decimal`]'s [`Eq`] and [`Ord`] implementations for NaN values.
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

    /// Create from pre-encoded bytes with validation
    ///
    /// # Errors
    ///
    /// Returns [`DecodeError`] if the bytes do not represent a valid encoding.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DecodeError> {
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

    /// Decode to get semantic fields (positive, exponent, significand).
    ///
    /// Returns `None` for special values (±0, ±∞, NaN) since they have no
    /// exponent or significand. Use [`is_zero()`](Self::is_zero),
    /// [`is_nan()`](Self::is_nan), and [`is_infinity()`](Self::is_infinity)
    /// to identify special values before decoding.
    #[must_use]
    pub fn decode(&self) -> Option<DecodedDecimal> {
        match decode_to_parts(&self.bytes).ok()? {
            DecodedValue::Regular(d) => Some(d),
            DecodedValue::Special(_) => None,
        }
    }

    /// Check if this is zero (either +0 or -0)
    #[must_use]
    pub fn is_zero(&self) -> bool {
        self.bytes.len() == 1 && (self.bytes[0] == 0x80 || self.bytes[0] == 0x40)
    }

    /// Check if this is NaN
    #[must_use]
    pub fn is_nan(&self) -> bool {
        self.bytes.len() == 1 && self.bytes[0] == 0b1110_0000
    }

    /// Check if this is infinity (either + or -)
    #[must_use]
    pub fn is_infinity(&self) -> bool {
        self.is_pos_infinity() || self.is_neg_infinity()
    }

    /// Check if this is positive infinity
    #[must_use]
    pub fn is_pos_infinity(&self) -> bool {
        self.bytes.len() == 1 && self.bytes[0] == 0xC0
    }

    /// Check if this is negative infinity
    #[must_use]
    pub fn is_neg_infinity(&self) -> bool {
        self.bytes.len() == 1 && self.bytes[0] == 0x00
    }

    /// Check if this is a finite number (not infinity or NaN)
    #[must_use]
    pub fn is_finite(&self) -> bool {
        !self.is_infinity() && !self.is_nan()
    }

    /// Create positive infinity
    #[must_use]
    pub fn infinity() -> Self {
        Self {
            bytes: vec![encode_special_byte(SpecialValue::PositiveInfinity)],
        }
    }

    /// Create negative infinity
    #[must_use]
    pub fn neg_infinity() -> Self {
        Self {
            bytes: vec![encode_special_byte(SpecialValue::NegativeInfinity)],
        }
    }

    /// Create NaN
    #[must_use]
    pub fn nan() -> Self {
        Self {
            bytes: vec![encode_special_byte(SpecialValue::NaN)],
        }
    }

    /// Create zero (positive zero)
    #[must_use]
    pub fn zero() -> Self {
        Self {
            bytes: vec![encode_special_byte(SpecialValue::PositiveZero)],
        }
    }

    /// Parse a decimal from string and encode immediately (internal helper)
    #[allow(clippy::too_many_lines)]
    fn parse_and_encode(s: &str) -> EncodeResult<Self> {
        let s = s.trim();

        // Handle special values (case-insensitive without allocation)
        if s.eq_ignore_ascii_case("inf")
            || s.eq_ignore_ascii_case("+inf")
            || s.eq_ignore_ascii_case("infinity")
            || s.eq_ignore_ascii_case("+infinity")
        {
            return Ok(Self::infinity());
        }
        if s.eq_ignore_ascii_case("-inf") || s.eq_ignore_ascii_case("-infinity") {
            return Ok(Self::neg_infinity());
        }
        if s.eq_ignore_ascii_case("nan") {
            return Ok(Self::nan());
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

        // Handle zero
        if s == "0" || s == "0.0" || s.bytes().all(|b| b == b'0' || b == b'.') {
            return if positive {
                Ok(Self::zero())
            } else {
                Ok(Self {
                    bytes: vec![encode_special_byte(SpecialValue::NegativeZero)],
                })
            };
        }

        // Parse the number - split without allocation
        let (integer_part, fractional_part) = match s.find('.') {
            Some(pos) => {
                let (int, rest) = s.split_at(pos);
                if rest[1..].contains('.') {
                    return Err(EncodeError::InvalidFormat(
                        "multiple decimal points".to_string(),
                    ));
                }
                (int, &rest[1..])
            }
            None => (s, ""),
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
            return if positive {
                Ok(Self::zero())
            } else {
                Ok(Self {
                    bytes: vec![encode_special_byte(SpecialValue::NegativeZero)],
                })
            };
        }

        // Calculate exponent from the position of the decimal point relative to
        // the first significant digit
        let decimal_point_position = integer_part.trim_start_matches('0').len();

        #[allow(clippy::cast_possible_truncation)]
        let (exponent, exponent_positive) = if decimal_point_position > 0 {
            // Number >= 1: exponent = number_of_integer_significant_digits - 1
            ((decimal_point_position - 1) as u64, true)
        } else {
            // Number < 1 (0.xxx): exponent = leading_zeros_in_fractional + 1
            let frac_leading_zeros =
                fractional_part.len() - fractional_part.trim_start_matches('0').len();
            ((frac_leading_zeros + 1) as u64, false)
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

impl fmt::Display for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match decode_to_parts(&self.bytes) {
            Ok(DecodedValue::Regular(d)) => {
                if !d.positive {
                    f.write_str("-")?;
                }

                // First significand digit + decimal point
                write!(f, "{}.", d.significand[0])?;

                // Remaining significand digits — written char-by-char to avoid allocation
                for &digit in &d.significand[1..] {
                    write!(f, "{digit}")?;
                }

                f.write_str(" × 10^")?;

                if !d.exponent_positive {
                    f.write_str("-")?;
                }

                write!(f, "{}", d.exponent)
            }
            Ok(DecodedValue::Special(s)) => {
                let name = match s {
                    SpecialValue::NegativeInfinity => "-∞",
                    SpecialValue::NegativeZero => "-0",
                    SpecialValue::PositiveZero => "0",
                    SpecialValue::PositiveInfinity => "∞",
                    SpecialValue::NaN => "NaN",
                };
                f.write_str(name)
            }
            Err(_) => f.write_str("<invalid>"),
        }
    }
}

impl PartialEq for Decimal {
    fn eq(&self, other: &Self) -> bool {
        // Special case: +0 and -0 are equal
        if self.is_zero() && other.is_zero() {
            return true;
        }
        // Otherwise compare bytes
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
        // Special case: +0 and -0 are equal (must be consistent with PartialEq)
        if self.is_zero() && other.is_zero() {
            return Ordering::Equal;
        }
        // Direct byte comparison for order preservation
        self.bytes.cmp(&other.bytes)
    }
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

/// Core conversion: build a [`Decimal`] from an unsigned magnitude and a sign flag.
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
        from_unsigned_with_sign(u128::from(value), true)
    }
}

impl From<i64> for Decimal {
    fn from(value: i64) -> Self {
        // Handle i64::MIN without overflow: cast to i128 first, then negate
        #[allow(clippy::cast_sign_loss)]
        let (positive, magnitude) = if value >= 0 {
            (true, value as u128)
        } else {
            (false, (-i128::from(value)) as u128)
        };
        from_unsigned_with_sign(magnitude, positive)
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
/// Used by the `From<f64>` / `From<f32>` impls to format a float into
/// a string without heap allocation. 25 bytes is enough for any `f64`
/// (sign + up to 17 significant digits + decimal point + 'e' + exponent).
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

impl From<f64> for Decimal {
    /// Convert an [`f64`] to a [`Decimal`](Self) using the shortest roundtrip representation.
    ///
    /// Special float values map directly: `f64::NAN` → `Decimal::nan()`,
    /// `f64::INFINITY` → `Decimal::infinity()`, etc. Negative zero is preserved.
    ///
    /// Uses a stack buffer for formatting — no heap allocation beyond the
    /// final encoded `Vec<u8>`.
    fn from(value: f64) -> Self {
        if value.is_nan() {
            return Self::nan();
        }
        if value.is_infinite() {
            return if value.is_sign_positive() {
                Self::infinity()
            } else {
                Self::neg_infinity()
            };
        }
        if value == 0.0 {
            return if value.is_sign_positive() {
                Self::zero()
            } else {
                Self {
                    bytes: vec![encode_special_byte(SpecialValue::NegativeZero)],
                }
            };
        }

        let mut buf = StackBuf::new();
        // Rust's f64 Display produces the shortest roundtrip representation
        write!(buf, "{value}").expect("f64 Display should fit in 25 bytes");
        // Delegate to FromStr — the string is already validated decimal
        buf.as_str()
            .parse()
            .expect("f64 Display output should always be a valid decimal")
    }
}

impl From<f32> for Decimal {
    fn from(value: f32) -> Self {
        Self::from(f64::from(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_positive() {
        let d: Decimal = "123.456".parse().unwrap();
        let decoded = d.decode().unwrap();
        assert!(decoded.positive);
        assert!(decoded.exponent_positive);
        assert_eq!(decoded.exponent, 2);
        // Significand may have trailing zeros from declet padding
        assert!(decoded.significand.starts_with(&[1, 2, 3, 4, 5, 6]));
    }

    #[test]
    fn test_parse_negative() {
        let d: Decimal = "-103.2".parse().unwrap();
        let decoded = d.decode().unwrap();
        assert!(!decoded.positive);
        assert!(decoded.exponent_positive);
        assert_eq!(decoded.exponent, 2);
        // Significand may have trailing zeros from declet padding
        assert!(decoded.significand.starts_with(&[1, 0, 3, 2]));
    }

    #[test]
    fn test_parse_small() {
        let d: Decimal = "0.0405".parse().unwrap();
        let decoded = d.decode().unwrap();
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
    fn test_parse_infinity() {
        let d: Decimal = "+inf".parse().unwrap();
        assert!(d.is_pos_infinity());
    }

    #[test]
    fn test_zero_equality() {
        let pos_zero: Decimal = "0".parse().unwrap();
        let neg_zero: Decimal = "-0".parse().unwrap();
        assert_eq!(pos_zero, neg_zero, "+0 should equal -0");
    }

    #[test]
    fn test_special_values_case_insensitive() {
        // Test case-insensitive parsing of special values
        assert!("INF".parse::<Decimal>().unwrap().is_pos_infinity());
        assert!("Inf".parse::<Decimal>().unwrap().is_pos_infinity());
        assert!("+INFINITY".parse::<Decimal>().unwrap().is_pos_infinity());
        assert!("-inf".parse::<Decimal>().unwrap().is_neg_infinity());
        assert!("-Infinity".parse::<Decimal>().unwrap().is_neg_infinity());
        assert!("NaN".parse::<Decimal>().unwrap().is_nan());
        assert!("nan".parse::<Decimal>().unwrap().is_nan());
        assert!("NAN".parse::<Decimal>().unwrap().is_nan());
    }

    #[test]
    fn test_multiple_decimal_points() {
        // Should fail with multiple decimal points
        assert!("123.456.789".parse::<Decimal>().is_err());
        assert!("1.2.3".parse::<Decimal>().is_err());
    }

    #[test]
    fn test_zero_ord_consistency() {
        // Ord must agree with PartialEq: +0 == -0 implies cmp == Equal
        let pos_zero: Decimal = "0".parse().unwrap();
        let neg_zero: Decimal = "-0".parse().unwrap();
        assert_eq!(
            pos_zero.cmp(&neg_zero),
            Ordering::Equal,
            "+0.cmp(-0) must be Equal to match PartialEq"
        );
        assert_eq!(
            neg_zero.cmp(&pos_zero),
            Ordering::Equal,
            "-0.cmp(+0) must be Equal to match PartialEq"
        );
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
    // From<f64> / From<f32> tests
    // =========================================================================

    #[test]
    fn test_from_f64_matches_parse() {
        let cases: &[f64] = &[1.0, -1.0, 0.5, -0.5, 42.0, 123.456, 0.001, 1e10, 1e-10];
        for &v in cases {
            let from_float = Decimal::from(v);
            let from_str: Decimal = v.to_string().parse().unwrap();
            assert_eq!(
                from_float.as_bytes(),
                from_str.as_bytes(),
                "From<f64> mismatch for {v}"
            );
        }
    }

    #[test]
    fn test_from_f64_special_values() {
        assert!(Decimal::from(f64::NAN).is_nan());
        assert!(Decimal::from(f64::INFINITY).is_pos_infinity());
        assert!(Decimal::from(f64::NEG_INFINITY).is_neg_infinity());
        assert!(Decimal::from(0.0_f64).is_zero());
        assert!(Decimal::from(-0.0_f64).is_zero());
    }

    #[test]
    fn test_from_f64_negative_zero_preserved() {
        let neg_zero = Decimal::from(-0.0_f64);
        let pos_zero = Decimal::from(0.0_f64);
        // Both are zero and compare equal
        assert_eq!(neg_zero, pos_zero);
        // But their underlying bytes differ (-0 = 0x40, +0 = 0x80)
        assert_ne!(neg_zero.as_bytes(), pos_zero.as_bytes());
    }

    #[test]
    fn test_from_f64_order_preserved() {
        let values: Vec<f64> = vec![-1000.0, -1.0, -0.001, 0.001, 1.0, 1000.0];
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
    fn test_from_f32_matches_f64_widening() {
        let v = 2.72_f32;
        let from_f32 = Decimal::from(v);
        let from_f64 = Decimal::from(f64::from(v));
        assert_eq!(from_f32.as_bytes(), from_f64.as_bytes());
    }
}
