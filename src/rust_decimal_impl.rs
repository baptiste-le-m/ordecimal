//! Optional [`rust_decimal`] integration for [`Decimal`].
//!
//! Enabled via the `rust_decimal` feature flag.
//!
//! Provides:
//! - [`From<rust_decimal::Decimal>`](From) for [`Decimal`] — infallible conversion
//!   (every `rust_decimal` value is representable in ordecimal).
//! - [`TryFrom<Decimal>`](TryFrom) for [`rust_decimal::Decimal`] — fallible conversion
//!   because ordecimal can represent values outside `rust_decimal`'s range
//!   (numbers exceeding 96-bit / 28-digit precision).

use crate::Decimal;
use thiserror::Error;

/// Error returned when an [`ordecimal::Decimal`](Decimal) cannot be converted
/// to a [`rust_decimal::Decimal`].
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum RustDecimalConversionError {
    /// The ordecimal value exceeds `rust_decimal`'s representable range
    /// (96-bit coefficient, scale 0–28).
    #[error("value {0} is outside rust_decimal::Decimal representable range")]
    OutOfRange(String),
}

/// Infallible conversion from [`rust_decimal::Decimal`] to [`ordecimal::Decimal`](Decimal).
///
/// Uses the string representation as an intermediate format. Every value
/// representable by `rust_decimal` is also representable by ordecimal.
impl From<rust_decimal::Decimal> for Decimal {
    fn from(value: rust_decimal::Decimal) -> Self {
        value
            .to_string()
            .parse()
            .expect("rust_decimal Display output should always be a valid ordecimal input")
    }
}

/// Fallible conversion from [`ordecimal::Decimal`](Decimal) to [`rust_decimal::Decimal`].
///
/// Fails if the ordecimal value exceeds `rust_decimal`'s 96-bit coefficient /
/// 28-digit precision.
impl TryFrom<Decimal> for rust_decimal::Decimal {
    type Error = RustDecimalConversionError;

    fn try_from(value: Decimal) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}

/// Fallible conversion from a borrowed [`ordecimal::Decimal`](Decimal) reference.
impl TryFrom<&Decimal> for rust_decimal::Decimal {
    type Error = RustDecimalConversionError;

    fn try_from(value: &Decimal) -> Result<Self, Self::Error> {
        let s = value.to_scientific_string();

        rust_decimal::Decimal::from_scientific(&s)
            .map_err(|_| RustDecimalConversionError::OutOfRange(s))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── From<rust_decimal::Decimal> for Decimal ─────────────────────────

    #[test]
    fn from_rust_decimal_positive_integer() {
        let rd = rust_decimal::Decimal::new(42, 0);
        let od = Decimal::from(rd);
        let expected: Decimal = "42".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_rust_decimal_negative_integer() {
        let rd = rust_decimal::Decimal::new(-42, 0);
        let od = Decimal::from(rd);
        let expected: Decimal = "-42".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_rust_decimal_positive_fraction() {
        let rd = rust_decimal::Decimal::new(123_456, 3); // 123.456
        let od = Decimal::from(rd);
        let expected: Decimal = "123.456".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_rust_decimal_negative_fraction() {
        let rd = rust_decimal::Decimal::new(-123_456, 3); // -123.456
        let od = Decimal::from(rd);
        let expected: Decimal = "-123.456".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_rust_decimal_zero() {
        let rd = rust_decimal::Decimal::ZERO;
        let od = Decimal::from(rd);
        assert_eq!(od, Decimal::zero());
    }

    #[test]
    fn from_rust_decimal_small_fraction() {
        let rd: rust_decimal::Decimal = "0.000001".parse().unwrap();
        let od = Decimal::from(rd);
        let expected: Decimal = "0.000001".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_rust_decimal_max() {
        let rd = rust_decimal::Decimal::MAX;
        let od = Decimal::from(rd);
        let expected: Decimal = rust_decimal::Decimal::MAX.to_string().parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_rust_decimal_min() {
        let rd = rust_decimal::Decimal::MIN;
        let od = Decimal::from(rd);
        let expected: Decimal = rust_decimal::Decimal::MIN.to_string().parse().unwrap();
        assert_eq!(od, expected);
    }

    // ── TryFrom<Decimal> for rust_decimal::Decimal ──────────────────────

    #[test]
    fn try_into_rust_decimal_positive() {
        let od: Decimal = "123.456".parse().unwrap();
        let rd = rust_decimal::Decimal::try_from(&od).unwrap();
        let expected = rust_decimal::Decimal::new(123_456, 3);
        assert_eq!(rd, expected);
    }

    #[test]
    fn try_into_rust_decimal_negative() {
        let od: Decimal = "-42.5".parse().unwrap();
        let rd = rust_decimal::Decimal::try_from(&od).unwrap();
        let expected = rust_decimal::Decimal::new(-425, 1);
        assert_eq!(rd, expected);
    }

    #[test]
    fn try_into_rust_decimal_zero() {
        let od = Decimal::zero();
        let rd = rust_decimal::Decimal::try_from(&od).unwrap();
        assert_eq!(rd, rust_decimal::Decimal::ZERO);
    }

    #[test]
    fn try_into_rust_decimal_out_of_range() {
        // rust_decimal::MAX is 79228162514264337593543950335 (96-bit coefficient).
        // A value above that should fail to convert.
        let od: Decimal = "79228162514264337593543950336".parse().unwrap();
        let result = rust_decimal::Decimal::try_from(&od);
        assert!(result.is_err());
    }

    // ── Roundtrip ───────────────────────────────────────────────────────

    #[test]
    fn roundtrip_through_ordecimal() {
        let values = [
            "0",
            "1",
            "-1",
            "123.456",
            "-123.456",
            "0.001",
            "-0.001",
            "99999999999999999999999999.99",
            "-99999999999999999999999999.99",
        ];

        for s in &values {
            let rd_original: rust_decimal::Decimal = s.parse().unwrap();
            let od = Decimal::from(rd_original);
            let rd_restored = rust_decimal::Decimal::try_from(&od).unwrap();
            assert_eq!(
                rd_original, rd_restored,
                "roundtrip failed for {s}: {rd_original} != {rd_restored}"
            );
        }
    }

    // ── Order preservation ──────────────────────────────────────────────

    #[test]
    fn order_preserved_through_conversion() {
        let rust_decimals: Vec<rust_decimal::Decimal> = [
            "-1000", "-100", "-10", "-1", "-0.5", "-0.001", "0", "0.001", "0.5", "1", "10", "100",
            "1000",
        ]
        .iter()
        .map(|s| s.parse().unwrap())
        .collect();

        let ordecimal_values: Vec<Decimal> =
            rust_decimals.iter().copied().map(Decimal::from).collect();

        for i in 1..ordecimal_values.len() {
            assert!(
                ordecimal_values[i - 1] < ordecimal_values[i],
                "order not preserved: {} < {} (ordecimal comparison failed)",
                rust_decimals[i - 1],
                rust_decimals[i]
            );
        }
    }

    // ── Scientific notation roundtrip ───────────────────────────────────

    #[test]
    fn try_into_rust_decimal_from_scientific_notation_input() {
        // ordecimal can be created from scientific notation strings.
        // Verify the TryFrom conversion still works (to_plain_string
        // expands these to positional notation for moderate exponents).
        let cases = [
            ("1.23e5", "123000"),
            ("9.99e20", "999000000000000000000"),
            ("-4.56e10", "-45600000000"),
            ("7.8e-5", "0.000078"),
        ];
        for (sci, plain) in &cases {
            let od: Decimal = sci.parse().unwrap();
            let rd = rust_decimal::Decimal::try_from(&od).unwrap();
            let expected: rust_decimal::Decimal = plain.parse().unwrap();
            assert_eq!(rd, expected, "conversion failed for {sci}");
        }
    }

    #[test]
    fn try_into_rust_decimal_extreme_exponent() {
        // to_plain_string emits scientific notation for exponents > 1000.
        // Verify that from_scientific is used and the conversion succeeds
        // when the value is still within rust_decimal's range.
        let od: Decimal = "1e1001".parse().unwrap();
        // This exceeds rust_decimal's range, so it should fail
        assert!(rust_decimal::Decimal::try_from(&od).is_err());
    }
}
