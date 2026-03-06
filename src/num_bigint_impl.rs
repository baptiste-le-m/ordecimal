//! Optional [`num_bigint`] integration for [`Decimal`].
//!
//! Enabled via the `num_bigint` feature flag.
//!
//! Provides:
//! - [`From<BigInt>`](From) / [`From<BigUint>`](From) for [`Decimal`] — infallible,
//!   since every integer is representable in ordecimal.
//! - [`TryFrom<Decimal>`](TryFrom) for [`BigInt`] / [`BigUint`] — fallible,
//!   because ordecimal values can have fractional parts (and `BigUint` rejects
//!   negative values).

use crate::decoder::decode_to_parts;
use crate::Decimal;
use num_bigint::{BigInt, BigUint};
use thiserror::Error;

/// Error returned when a [`Decimal`] cannot be converted to a [`BigInt`] or [`BigUint`].
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum BigIntConversionError {
    /// The decimal value has a non-zero fractional part.
    #[error("value {0} is not an integer")]
    NotAnInteger(String),

    /// The decimal value is negative (only for [`BigUint`] conversions).
    #[error("value {0} is negative and cannot be represented as BigUint")]
    Negative(String),
}

// ── From<BigInt/BigUint> for Decimal ───────────────────────────────────

/// Infallible conversion from [`BigInt`] to [`ordecimal::Decimal`](Decimal).
impl From<BigInt> for Decimal {
    fn from(value: BigInt) -> Self {
        value
            .to_string()
            .parse()
            .expect("BigInt Display output should always be a valid ordecimal input")
    }
}

/// Infallible conversion from a borrowed [`BigInt`] reference.
impl From<&BigInt> for Decimal {
    fn from(value: &BigInt) -> Self {
        value
            .to_string()
            .parse()
            .expect("BigInt Display output should always be a valid ordecimal input")
    }
}

/// Infallible conversion from [`BigUint`] to [`ordecimal::Decimal`](Decimal).
impl From<BigUint> for Decimal {
    fn from(value: BigUint) -> Self {
        value
            .to_string()
            .parse()
            .expect("BigUint Display output should always be a valid ordecimal input")
    }
}

/// Infallible conversion from a borrowed [`BigUint`] reference.
impl From<&BigUint> for Decimal {
    fn from(value: &BigUint) -> Self {
        value
            .to_string()
            .parse()
            .expect("BigUint Display output should always be a valid ordecimal input")
    }
}

// ── TryFrom<Decimal> for BigInt/BigUint ────────────────────────────────

/// Fallible conversion from [`ordecimal::Decimal`](Decimal) to [`BigInt`].
///
/// Fails if the decimal has a non-zero fractional part.
impl TryFrom<Decimal> for BigInt {
    type Error = BigIntConversionError;

    fn try_from(value: Decimal) -> Result<Self, Self::Error> {
        BigInt::try_from(&value)
    }
}

/// Fallible conversion from a borrowed [`ordecimal::Decimal`](Decimal) reference.
impl TryFrom<&Decimal> for BigInt {
    type Error = BigIntConversionError;

    fn try_from(value: &Decimal) -> Result<Self, Self::Error> {
        if value.is_zero() {
            return Ok(BigInt::from(0));
        }

        let decoded = decode_to_parts(value.as_bytes())
            .map_err(|_| BigIntConversionError::NotAnInteger(value.to_plain_string()))?;

        // Trim trailing zeros from the significand to get meaningful digits.
        let sig = match decoded.significand.iter().rposition(|&d| d != 0) {
            Some(pos) => &decoded.significand[..=pos],
            None => &decoded.significand[..1], // at least one digit
        };

        // Determine whether the value is an integer.
        // With a positive (or zero) exponent, the number of integer digits
        // is `exponent + 1`.  If that covers all significand digits the
        // value is an integer; the remaining positions are trailing zeros.
        // With a negative exponent the value is < 1, always fractional.
        if !decoded.exponent_positive && decoded.exponent > 0 {
            return Err(BigIntConversionError::NotAnInteger(value.to_plain_string()));
        }

        let int_digits = decoded.exponent as usize + 1;
        if int_digits < sig.len() {
            // Some significand digits fall after the decimal point → fractional.
            return Err(BigIntConversionError::NotAnInteger(value.to_plain_string()));
        }

        // Build the full digit string: significand digits + trailing zeros.
        let trailing_zeros = int_digits - sig.len();
        let mut digit_string = String::with_capacity(int_digits + 1);
        if !decoded.positive {
            digit_string.push('-');
        }
        for &d in sig {
            digit_string.push((d + b'0') as char);
        }
        for _ in 0..trailing_zeros {
            digit_string.push('0');
        }

        digit_string
            .parse::<BigInt>()
            .map_err(|_| BigIntConversionError::NotAnInteger(value.to_plain_string()))
    }
}

/// Fallible conversion from [`ordecimal::Decimal`](Decimal) to [`BigUint`].
///
/// Fails if the decimal has a non-zero fractional part or is negative.
impl TryFrom<Decimal> for BigUint {
    type Error = BigIntConversionError;

    fn try_from(value: Decimal) -> Result<Self, Self::Error> {
        BigUint::try_from(&value)
    }
}

/// Fallible conversion from a borrowed [`ordecimal::Decimal`](Decimal) reference.
impl TryFrom<&Decimal> for BigUint {
    type Error = BigIntConversionError;

    fn try_from(value: &Decimal) -> Result<Self, Self::Error> {
        if value.is_zero() {
            return Ok(BigUint::from(0_u64));
        }

        let decoded = decode_to_parts(value.as_bytes())
            .map_err(|_| BigIntConversionError::NotAnInteger(value.to_plain_string()))?;

        if !decoded.positive {
            return Err(BigIntConversionError::Negative(value.to_plain_string()));
        }

        // Trim trailing zeros from the significand to get meaningful digits.
        let sig = match decoded.significand.iter().rposition(|&d| d != 0) {
            Some(pos) => &decoded.significand[..=pos],
            None => &decoded.significand[..1],
        };

        // With a negative exponent the value is < 1, always fractional.
        if !decoded.exponent_positive && decoded.exponent > 0 {
            return Err(BigIntConversionError::NotAnInteger(value.to_plain_string()));
        }

        let int_digits = decoded.exponent as usize + 1;
        if int_digits < sig.len() {
            return Err(BigIntConversionError::NotAnInteger(value.to_plain_string()));
        }

        // Build the full digit string: significand digits + trailing zeros.
        let trailing_zeros = int_digits - sig.len();
        let mut digit_string = String::with_capacity(int_digits);
        for &d in sig {
            digit_string.push((d + b'0') as char);
        }
        for _ in 0..trailing_zeros {
            digit_string.push('0');
        }

        digit_string
            .parse::<BigUint>()
            .map_err(|_| BigIntConversionError::NotAnInteger(value.to_plain_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    // ── From<BigInt> for Decimal ────────────────────────────────────────

    #[test]
    fn from_bigint_positive() {
        let bi = BigInt::from(42);
        let od = Decimal::from(bi);
        let expected: Decimal = "42".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_bigint_negative() {
        let bi = BigInt::from(-42);
        let od = Decimal::from(bi);
        let expected: Decimal = "-42".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_bigint_zero() {
        let bi = BigInt::from(0);
        let od = Decimal::from(bi);
        assert_eq!(od, Decimal::zero());
    }

    #[test]
    fn from_bigint_very_large() {
        let s = "99999999999999999999999999999999999999999999999999";
        let bi = BigInt::from_str(s).unwrap();
        let od = Decimal::from(bi);
        let expected: Decimal = s.parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_bigint_ref() {
        let bi = BigInt::from(123);
        let od = Decimal::from(&bi);
        let expected: Decimal = "123".parse().unwrap();
        assert_eq!(od, expected);
    }

    // ── From<BigUint> for Decimal ──────────────────────────────────────

    #[test]
    fn from_biguint_positive() {
        let bu = BigUint::from(42_u64);
        let od = Decimal::from(bu);
        let expected: Decimal = "42".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_biguint_zero() {
        let bu = BigUint::from(0_u64);
        let od = Decimal::from(bu);
        assert_eq!(od, Decimal::zero());
    }

    #[test]
    fn from_biguint_ref() {
        let bu = BigUint::from(123_u64);
        let od = Decimal::from(&bu);
        let expected: Decimal = "123".parse().unwrap();
        assert_eq!(od, expected);
    }

    // ── TryFrom<Decimal> for BigInt ────────────────────────────────────

    #[test]
    fn try_into_bigint_positive() {
        let od: Decimal = "42".parse().unwrap();
        let bi = BigInt::try_from(&od).unwrap();
        assert_eq!(bi, BigInt::from(42));
    }

    #[test]
    fn try_into_bigint_negative() {
        let od: Decimal = "-42".parse().unwrap();
        let bi = BigInt::try_from(&od).unwrap();
        assert_eq!(bi, BigInt::from(-42));
    }

    #[test]
    fn try_into_bigint_zero() {
        let od = Decimal::zero();
        let bi = BigInt::try_from(&od).unwrap();
        assert_eq!(bi, BigInt::from(0));
    }

    #[test]
    fn try_into_bigint_fractional_rejected() {
        let od: Decimal = "42.5".parse().unwrap();
        let result = BigInt::try_from(&od);
        assert!(matches!(
            result,
            Err(BigIntConversionError::NotAnInteger(_))
        ));
    }

    #[test]
    fn try_into_bigint_very_large() {
        let s = "99999999999999999999999999999999999999999999999999";
        let od: Decimal = s.parse().unwrap();
        let bi = BigInt::try_from(&od).unwrap();
        assert_eq!(bi, BigInt::from_str(s).unwrap());
    }

    #[test]
    fn try_into_bigint_extreme_exponent() {
        // Exponent > MAX_PLAIN_EXPONENT (1000): to_plain_string() would return
        // scientific notation, but decode_to_parts avoids that entirely.
        let od: Decimal = "1e5000".parse().unwrap();
        let bi = BigInt::try_from(&od).unwrap();
        let expected = BigInt::from(10_u64).pow(5000);
        assert_eq!(bi, expected);
    }

    #[test]
    fn try_into_bigint_negative_extreme_exponent() {
        let od: Decimal = "-1e5000".parse().unwrap();
        let bi = BigInt::try_from(&od).unwrap();
        let expected = -BigInt::from(10_u64).pow(5000);
        assert_eq!(bi, expected);
    }

    #[test]
    fn try_into_bigint_extreme_negative_exponent_fractional_rejected() {
        // Negative extreme exponent: value is < 1, always fractional.
        let od: Decimal = "1.5e-5000".parse().unwrap();
        let result = BigInt::try_from(&od);
        assert!(matches!(
            result,
            Err(BigIntConversionError::NotAnInteger(_))
        ));
    }

    // ── TryFrom<Decimal> for BigUint ───────────────────────────────────

    #[test]
    fn try_into_biguint_positive() {
        let od: Decimal = "42".parse().unwrap();
        let bu = BigUint::try_from(&od).unwrap();
        assert_eq!(bu, BigUint::from(42_u64));
    }

    #[test]
    fn try_into_biguint_zero() {
        let od = Decimal::zero();
        let bu = BigUint::try_from(&od).unwrap();
        assert_eq!(bu, BigUint::from(0_u64));
    }

    #[test]
    fn try_into_biguint_negative_rejected() {
        let od: Decimal = "-1".parse().unwrap();
        let result = BigUint::try_from(&od);
        assert!(matches!(result, Err(BigIntConversionError::Negative(_))));
    }

    #[test]
    fn try_into_biguint_fractional_rejected() {
        let od: Decimal = "42.5".parse().unwrap();
        let result = BigUint::try_from(&od);
        assert!(matches!(
            result,
            Err(BigIntConversionError::NotAnInteger(_))
        ));
    }

    #[test]
    fn try_into_biguint_extreme_exponent() {
        let od: Decimal = "1e5000".parse().unwrap();
        let bu = BigUint::try_from(&od).unwrap();
        let expected = BigUint::from(10_u64).pow(5000);
        assert_eq!(bu, expected);
    }

    #[test]
    fn try_into_biguint_negative_extreme_exponent_rejected() {
        let od: Decimal = "-1e5000".parse().unwrap();
        let result = BigUint::try_from(&od);
        assert!(matches!(result, Err(BigIntConversionError::Negative(_))));
    }

    // ── Roundtrip ──────────────────────────────────────────────────────

    #[test]
    fn roundtrip_bigint() {
        let values = [
            "0",
            "1",
            "-1",
            "42",
            "-42",
            "999999999999999999999999999999",
        ];
        for s in &values {
            let bi_original = BigInt::from_str(s).unwrap();
            let od = Decimal::from(&bi_original);
            let bi_restored = BigInt::try_from(&od).unwrap();
            assert_eq!(bi_original, bi_restored, "roundtrip failed for {s}");
        }
    }

    #[test]
    fn roundtrip_bigint_extreme_exponent() {
        // 10^2000 roundtrips through ordecimal → BigInt.
        let bi_original = BigInt::from(10_u64).pow(2000);
        let od = Decimal::from(&bi_original);
        let bi_restored = BigInt::try_from(&od).unwrap();
        assert_eq!(bi_original, bi_restored);
    }

    #[test]
    fn roundtrip_biguint() {
        let values = ["0", "1", "42", "999999999999999999999999999999"];
        for s in &values {
            let bu_original = BigUint::from_str(s).unwrap();
            let od = Decimal::from(&bu_original);
            let bu_restored = BigUint::try_from(&od).unwrap();
            assert_eq!(bu_original, bu_restored, "roundtrip failed for {s}");
        }
    }

    #[test]
    fn roundtrip_biguint_extreme_exponent() {
        let bu_original = BigUint::from(10_u64).pow(2000);
        let od = Decimal::from(&bu_original);
        let bu_restored = BigUint::try_from(&od).unwrap();
        assert_eq!(bu_original, bu_restored);
    }

    // ── Order preservation ─────────────────────────────────────────────

    #[test]
    fn order_preserved_through_conversion() {
        let bigints: Vec<BigInt> = ["-1000", "-100", "-10", "-1", "0", "1", "10", "100", "1000"]
            .iter()
            .map(|s| BigInt::from_str(s).unwrap())
            .collect();

        let ordecimal_values: Vec<Decimal> = bigints.iter().map(Decimal::from).collect();

        for i in 1..ordecimal_values.len() {
            assert!(
                ordecimal_values[i - 1] < ordecimal_values[i],
                "order not preserved: {} < {} (ordecimal comparison failed)",
                bigints[i - 1],
                bigints[i]
            );
        }
    }
}
