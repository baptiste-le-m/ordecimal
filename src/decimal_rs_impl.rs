//! Optional [`decimal_rs`] integration for [`Decimal`].
//!
//! Enabled via the `decimal_rs` feature flag.
//!
//! Provides:
//! - [`From<decimal_rs::Decimal>`](From) for [`Decimal`] — infallible conversion
//!   (every `decimal_rs` value is representable in ordecimal).
//! - [`TryFrom<Decimal>`](TryFrom) for [`decimal_rs::Decimal`] — fallible conversion
//!   because ordecimal can represent values outside `decimal_rs`'s range
//!   (numbers exceeding 38-digit precision).

use crate::Decimal;
use thiserror::Error;

/// Error returned when an [`ordecimal::Decimal`](Decimal) cannot be converted
/// to a [`decimal_rs::Decimal`].
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum DecimalRsConversionError {
    /// The ordecimal value exceeds `decimal_rs`'s representable range
    /// (38-digit precision, scale \[-126, 130\]).
    #[error("value {0} is outside decimal_rs::Decimal representable range")]
    OutOfRange(String),
}

/// Infallible conversion from [`decimal_rs::Decimal`] to [`ordecimal::Decimal`](Decimal).
///
/// Uses the string representation as an intermediate format. Every value
/// representable by `decimal_rs` is also representable by ordecimal.
impl From<decimal_rs::Decimal> for Decimal {
    fn from(value: decimal_rs::Decimal) -> Self {
        value
            .to_string()
            .parse()
            .expect("decimal_rs Display output should always be a valid ordecimal input")
    }
}

/// Infallible conversion from a borrowed [`decimal_rs::Decimal`] reference.
impl From<&decimal_rs::Decimal> for Decimal {
    fn from(value: &decimal_rs::Decimal) -> Self {
        value
            .to_string()
            .parse()
            .expect("decimal_rs Display output should always be a valid ordecimal input")
    }
}

/// Fallible conversion from [`ordecimal::Decimal`](Decimal) to [`decimal_rs::Decimal`].
///
/// Fails if the ordecimal value exceeds `decimal_rs`'s 38-digit precision
/// or scale limits.
impl TryFrom<Decimal> for decimal_rs::Decimal {
    type Error = DecimalRsConversionError;

    fn try_from(value: Decimal) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}

/// Fallible conversion from a borrowed [`ordecimal::Decimal`](Decimal) reference.
impl TryFrom<&Decimal> for decimal_rs::Decimal {
    type Error = DecimalRsConversionError;

    fn try_from(value: &Decimal) -> Result<Self, Self::Error> {
        let s = value.to_scientific_string();

        s.parse::<decimal_rs::Decimal>()
            .map_err(|_| DecimalRsConversionError::OutOfRange(s))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    // ── From<decimal_rs::Decimal> for Decimal ──────────────────────────

    #[test]
    fn from_decimal_rs_positive_integer() {
        let dr = decimal_rs::Decimal::from(42_i64);
        let od = Decimal::from(dr);
        let expected: Decimal = "42".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_decimal_rs_negative_integer() {
        let dr = decimal_rs::Decimal::from(-42_i64);
        let od = Decimal::from(dr);
        let expected: Decimal = "-42".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_decimal_rs_positive_fraction() {
        let dr = decimal_rs::Decimal::from_str("123.456").unwrap();
        let od = Decimal::from(dr);
        let expected: Decimal = "123.456".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_decimal_rs_negative_fraction() {
        let dr = decimal_rs::Decimal::from_str("-123.456").unwrap();
        let od = Decimal::from(dr);
        let expected: Decimal = "-123.456".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_decimal_rs_zero() {
        let dr = decimal_rs::Decimal::ZERO;
        let od = Decimal::from(dr);
        assert_eq!(od, Decimal::zero());
    }

    #[test]
    fn from_decimal_rs_small_fraction() {
        let dr = decimal_rs::Decimal::from_str("0.000001").unwrap();
        let od = Decimal::from(dr);
        let expected: Decimal = "0.000001".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_decimal_rs_ref() {
        let dr = decimal_rs::Decimal::from_str("3.14").unwrap();
        let od = Decimal::from(&dr);
        let expected: Decimal = "3.14".parse().unwrap();
        assert_eq!(od, expected);
    }

    // ── TryFrom<Decimal> for decimal_rs::Decimal ───────────────────────

    #[test]
    fn try_into_decimal_rs_positive() {
        let od: Decimal = "123.456".parse().unwrap();
        let dr = decimal_rs::Decimal::try_from(&od).unwrap();
        let expected = decimal_rs::Decimal::from_str("123.456").unwrap();
        assert_eq!(dr, expected);
    }

    #[test]
    fn try_into_decimal_rs_negative() {
        let od: Decimal = "-42.5".parse().unwrap();
        let dr = decimal_rs::Decimal::try_from(&od).unwrap();
        let expected = decimal_rs::Decimal::from_str("-42.5").unwrap();
        assert_eq!(dr, expected);
    }

    #[test]
    fn try_into_decimal_rs_zero() {
        let od = Decimal::zero();
        let dr = decimal_rs::Decimal::try_from(&od).unwrap();
        assert_eq!(dr, decimal_rs::Decimal::ZERO);
    }

    #[test]
    fn try_into_decimal_rs_out_of_range() {
        // decimal_rs has a scale limit of [-126, 130].
        // An extreme exponent that exceeds this should fail.
        let od: Decimal = "1e10000".parse().unwrap();
        let result = decimal_rs::Decimal::try_from(&od);
        assert!(result.is_err());
    }

    #[test]
    fn try_into_decimal_rs_extreme_exponent() {
        let od: Decimal = "1e10000".parse().unwrap();
        let result = decimal_rs::Decimal::try_from(&od);
        assert!(result.is_err());
    }

    // ── Roundtrip ──────────────────────────────────────────────────────

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
            "9999999999999999999999999999.99",
            "-9999999999999999999999999999.99",
        ];

        for s in &values {
            let dr_original = decimal_rs::Decimal::from_str(s).unwrap();
            let od = Decimal::from(dr_original);
            let dr_restored = decimal_rs::Decimal::try_from(&od).unwrap();
            assert_eq!(
                dr_original, dr_restored,
                "roundtrip failed for {s}: {dr_original} != {dr_restored}"
            );
        }
    }

    // ── Order preservation ─────────────────────────────────────────────

    #[test]
    fn order_preserved_through_conversion() {
        let decimal_rs_values: Vec<decimal_rs::Decimal> = [
            "-1000", "-100", "-10", "-1", "-0.5", "-0.001", "0", "0.001", "0.5", "1", "10", "100",
            "1000",
        ]
        .iter()
        .map(|s| decimal_rs::Decimal::from_str(s).unwrap())
        .collect();

        let ordecimal_values: Vec<Decimal> = decimal_rs_values.iter().map(Decimal::from).collect();

        for i in 1..ordecimal_values.len() {
            assert!(
                ordecimal_values[i - 1] < ordecimal_values[i],
                "order not preserved: {} < {} (ordecimal comparison failed)",
                decimal_rs_values[i - 1],
                decimal_rs_values[i]
            );
        }
    }
}
