//! Optional [`bigdecimal`] integration for [`Decimal`].
//!
//! Enabled via the `bigdecimal` feature flag.
//!
//! Provides:
//! - [`From<bigdecimal::BigDecimal>`](From) for [`Decimal`] — infallible,
//!   since both types support arbitrary precision.
//! - [`From<Decimal>`](From) for [`bigdecimal::BigDecimal`] — also infallible,
//!   because `BigDecimal` can represent every ordecimal value.

use crate::Decimal;

/// Infallible conversion from [`bigdecimal::BigDecimal`] to [`ordecimal::Decimal`](Decimal).
///
/// Uses the scientific notation string as an intermediate format to avoid
/// generating huge positional strings for extreme exponents.
impl From<bigdecimal::BigDecimal> for Decimal {
    fn from(value: bigdecimal::BigDecimal) -> Self {
        value
            .to_scientific_notation()
            .parse()
            .expect("BigDecimal scientific notation should always be a valid ordecimal input")
    }
}

/// Infallible conversion from a borrowed [`bigdecimal::BigDecimal`] reference.
impl From<&bigdecimal::BigDecimal> for Decimal {
    fn from(value: &bigdecimal::BigDecimal) -> Self {
        value
            .to_scientific_notation()
            .parse()
            .expect("BigDecimal scientific notation should always be a valid ordecimal input")
    }
}

/// Infallible conversion from [`ordecimal::Decimal`](Decimal) to [`bigdecimal::BigDecimal`].
///
/// Both types support arbitrary precision, so every ordecimal value is
/// representable by `BigDecimal`.
impl From<Decimal> for bigdecimal::BigDecimal {
    fn from(value: Decimal) -> Self {
        bigdecimal::BigDecimal::from(&value)
    }
}

/// Infallible conversion from a borrowed [`ordecimal::Decimal`](Decimal) reference.
impl From<&Decimal> for bigdecimal::BigDecimal {
    fn from(value: &Decimal) -> Self {
        let s = value.to_scientific_string();
        s.parse()
            .expect("ordecimal scientific notation should always be a valid BigDecimal input")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    // ── From<BigDecimal> for Decimal ───────────────────────────────────

    #[test]
    fn from_bigdecimal_positive_integer() {
        let bd = bigdecimal::BigDecimal::from(42);
        let od = Decimal::from(bd);
        let expected: Decimal = "42".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_bigdecimal_negative_integer() {
        let bd = bigdecimal::BigDecimal::from(-42);
        let od = Decimal::from(bd);
        let expected: Decimal = "-42".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_bigdecimal_positive_fraction() {
        let bd = bigdecimal::BigDecimal::from_str("123.456").unwrap();
        let od = Decimal::from(bd);
        let expected: Decimal = "123.456".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_bigdecimal_negative_fraction() {
        let bd = bigdecimal::BigDecimal::from_str("-123.456").unwrap();
        let od = Decimal::from(bd);
        let expected: Decimal = "-123.456".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_bigdecimal_zero() {
        let bd = bigdecimal::BigDecimal::from(0);
        let od = Decimal::from(bd);
        assert_eq!(od, Decimal::zero());
    }

    #[test]
    fn from_bigdecimal_small_fraction() {
        let bd = bigdecimal::BigDecimal::from_str("0.000001").unwrap();
        let od = Decimal::from(bd);
        let expected: Decimal = "0.000001".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_bigdecimal_large_value() {
        let s = "99999999999999999999999999999999999999999999999999";
        let bd = bigdecimal::BigDecimal::from_str(s).unwrap();
        let od = Decimal::from(bd);
        let expected: Decimal = s.parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_bigdecimal_extreme_exponent() {
        let bd = bigdecimal::BigDecimal::from_str("1e10000").unwrap();
        let od = Decimal::from(bd);
        let expected: Decimal = "1e10000".parse().unwrap();
        assert_eq!(od, expected);
    }

    #[test]
    fn from_bigdecimal_ref() {
        let bd = bigdecimal::BigDecimal::from_str("3.14").unwrap();
        let od = Decimal::from(&bd);
        let expected: Decimal = "3.14".parse().unwrap();
        assert_eq!(od, expected);
    }

    // ── From<Decimal> for BigDecimal ───────────────────────────────────

    #[test]
    fn into_bigdecimal_positive() {
        let od: Decimal = "123.456".parse().unwrap();
        let bd = bigdecimal::BigDecimal::from(&od);
        let expected = bigdecimal::BigDecimal::from_str("123.456").unwrap();
        assert_eq!(bd, expected);
    }

    #[test]
    fn into_bigdecimal_negative() {
        let od: Decimal = "-42.5".parse().unwrap();
        let bd = bigdecimal::BigDecimal::from(&od);
        let expected = bigdecimal::BigDecimal::from_str("-42.5").unwrap();
        assert_eq!(bd, expected);
    }

    #[test]
    fn into_bigdecimal_zero() {
        let od = Decimal::zero();
        let bd = bigdecimal::BigDecimal::from(&od);
        assert_eq!(bd, bigdecimal::BigDecimal::from(0));
    }

    #[test]
    fn into_bigdecimal_owned() {
        let od: Decimal = "99".parse().unwrap();
        let bd = bigdecimal::BigDecimal::from(od);
        let expected = bigdecimal::BigDecimal::from(99);
        assert_eq!(bd, expected);
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
            "99999999999999999999999999999999999999.99",
            "-99999999999999999999999999999999999999.99",
        ];

        for s in &values {
            let bd_original = bigdecimal::BigDecimal::from_str(s).unwrap();
            let od = Decimal::from(&bd_original);
            let bd_restored = bigdecimal::BigDecimal::from(&od);
            assert_eq!(
                bd_original, bd_restored,
                "roundtrip failed for {s}: {bd_original} != {bd_restored}"
            );
        }
    }

    #[test]
    fn roundtrip_through_bigdecimal() {
        let values = ["0", "1", "-1", "123.456", "-123.456", "0.001", "-0.001"];

        for s in &values {
            let od_original: Decimal = s.parse().unwrap();
            let bd = bigdecimal::BigDecimal::from(&od_original);
            let od_restored = Decimal::from(&bd);
            assert_eq!(
                od_original,
                od_restored,
                "roundtrip failed for {s}: {} != {}",
                od_original.to_plain_string(),
                od_restored.to_plain_string()
            );
        }
    }

    // ── Order preservation ─────────────────────────────────────────────

    #[test]
    fn order_preserved_through_conversion() {
        let bigdecimals: Vec<bigdecimal::BigDecimal> = [
            "-1000", "-100", "-10", "-1", "-0.5", "-0.001", "0", "0.001", "0.5", "1", "10", "100",
            "1000",
        ]
        .iter()
        .map(|s| bigdecimal::BigDecimal::from_str(s).unwrap())
        .collect();

        let ordecimal_values: Vec<Decimal> = bigdecimals.iter().map(Decimal::from).collect();

        for i in 1..ordecimal_values.len() {
            assert!(
                ordecimal_values[i - 1] < ordecimal_values[i],
                "order not preserved: {} < {} (ordecimal comparison failed)",
                bigdecimals[i - 1],
                bigdecimals[i]
            );
        }
    }
}
