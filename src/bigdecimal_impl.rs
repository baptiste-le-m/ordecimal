//! Optional [`bigdecimal`] integration for [`Decimal`].
//!
//! Enabled via the `bigdecimal` feature flag.
//!
//! Provides:
//! - [`From<bigdecimal::BigDecimal>`](From) for [`Decimal`] — infallible,
//!   since both types support arbitrary precision and ordecimal's exponent
//!   range covers `BigDecimal`'s.
//! - [`TryFrom<Decimal>`](TryFrom) for [`bigdecimal::BigDecimal`] — fallible,
//!   because `BigDecimal` stores its scale as an `i64` while ordecimal's
//!   exponent reaches ±(`u64::MAX - 2`).

use crate::arithmetic::MAX_DIGIT_COUNT;
use crate::Decimal;
use bigdecimal::num_bigint::BigInt;
use thiserror::Error;

/// Error returned when an [`ordecimal::Decimal`](Decimal) cannot be converted
/// to a [`bigdecimal::BigDecimal`].
#[derive(Error, Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum BigDecimalConversionError {
    /// The value has no `BigDecimal` form: an exponent below about −2^63
    /// needs a scale above `i64::MAX` (`1e-9223372036854775808`), and one
    /// above about 2^63 needs its trailing zeros spelled out in the integer,
    /// which is refused past 100 000 digits (the arithmetic budget).
    #[error("value {0} is outside bigdecimal::BigDecimal representable range")]
    OutOfRange(String),
}

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

/// Fallible conversion from [`ordecimal::Decimal`](Decimal) to [`bigdecimal::BigDecimal`].
///
/// Every digit carries over. `BigDecimal` keeps its scale in an `i64`, so
/// exponents beyond about ±2^63 may not fit: see
/// [`BigDecimalConversionError::OutOfRange`].
impl TryFrom<Decimal> for bigdecimal::BigDecimal {
    type Error = BigDecimalConversionError;

    fn try_from(value: Decimal) -> Result<Self, Self::Error> {
        Self::try_from(&value)
    }
}

/// Fallible conversion from a borrowed [`ordecimal::Decimal`](Decimal) reference.
impl TryFrom<&Decimal> for bigdecimal::BigDecimal {
    type Error = BigDecimalConversionError;

    fn try_from(value: &Decimal) -> Result<Self, Self::Error> {
        if value.is_zero() {
            return Ok(bigdecimal::BigDecimal::from(0));
        }

        value
            .with_significand(|sig, parts| {
                // value = sig × 10^(exponent − (len − 1)), and BigDecimal's
                // scale is that power negated.
                let exponent = if parts.exponent_positive {
                    i128::from(parts.exponent)
                } else {
                    -i128::from(parts.exponent)
                };
                let scale = (sig.len() as i128 - 1) - exponent;
                // A scale below i64::MIN is still reachable by moving trailing
                // zeros into the integer, within the digit budget. One above
                // i64::MAX is not: the significand has no trailing zeros to drop.
                let pad = (i128::from(i64::MIN) - scale).max(0);
                let scale = i64::try_from(scale + pad).ok()?;
                let pad = usize::try_from(pad).ok().filter(|&p| {
                    sig.len()
                        .checked_add(p)
                        .is_some_and(|n| n <= MAX_DIGIT_COUNT)
                })?;

                let mut digits = String::with_capacity(1 + sig.len() + pad);
                if !parts.positive {
                    digits.push('-');
                }
                digits.push_str(sig);
                digits.extend(std::iter::repeat('0').take(pad));
                let int: BigInt = digits.parse().ok()?;
                Some(bigdecimal::BigDecimal::new(int, scale))
            })
            .flatten()
            .ok_or_else(|| BigDecimalConversionError::OutOfRange(value.to_scientific_string()))
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
    fn from_bigdecimal_extreme_scales() {
        // Scale i64::MIN is exponent 2^63, one past i64::MAX: it used to fail
        // ordecimal's parser and panic in this infallible conversion.
        let cases = [
            (1, i64::MIN, "1e9223372036854775808"),
            (10, -i64::MAX, "1e9223372036854775808"),
            (1, i64::MAX, "1e-9223372036854775807"),
        ];
        for (int, scale, expected) in cases {
            let bd = bigdecimal::BigDecimal::new(BigInt::from(int), scale);
            assert_eq!(Decimal::from(&bd).to_scientific_string(), expected);
        }
    }

    #[test]
    fn roundtrip_bigdecimal_at_min_scale() {
        // Scale i64::MIN with trailing zeros in the integer: the shortest
        // scientific form needs a scale below i64::MIN, so the way back has
        // to move those zeros into the integer again.
        let cases = [
            bigdecimal::BigDecimal::from_str("1.0e9223372036854775809").unwrap(),
            bigdecimal::BigDecimal::new(
                BigInt::from_str("123456789012345678901234567890").unwrap(),
                i64::MIN,
            ),
        ];
        for bd in cases {
            let od = Decimal::from(&bd);
            let back = bigdecimal::BigDecimal::try_from(&od)
                .unwrap_or_else(|e| panic!("{bd:?} should convert back: {e}"));
            assert_eq!(back, bd);
        }
    }

    #[test]
    fn try_into_bigdecimal_padding_within_digit_budget() {
        // 2^63 + 99 999: scale i64::MIN plus 99 999 padding zeros, 100 000
        // digits in all — the last exponent that fits the budget.
        let od: Decimal = "1e9223372036854875807".parse().unwrap();
        let bd = bigdecimal::BigDecimal::try_from(&od).unwrap();
        assert_eq!(bd.as_bigint_and_exponent().1, i64::MIN);
        assert_eq!(Decimal::from(&bd), od);
        let od: Decimal = "1e9223372036854875808".parse().unwrap();
        assert!(matches!(
            bigdecimal::BigDecimal::try_from(&od),
            Err(BigDecimalConversionError::OutOfRange(_))
        ));
    }

    #[test]
    fn try_into_bigdecimal_beyond_i64_scale_rejected() {
        // The first needs scale 2^63, above i64::MAX, and used to panic in what
        // was an infallible From; the second would need ~9.2e18 padding digits.
        for s in ["1e-9223372036854775808", "1e18446744073709551613"] {
            let od: Decimal = s.parse().unwrap();
            assert!(
                matches!(
                    bigdecimal::BigDecimal::try_from(&od),
                    Err(BigDecimalConversionError::OutOfRange(_))
                ),
                "{s}"
            );
        }
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
        let bd = bigdecimal::BigDecimal::try_from(&od).unwrap();
        let expected = bigdecimal::BigDecimal::from_str("123.456").unwrap();
        assert_eq!(bd, expected);
    }

    #[test]
    fn into_bigdecimal_negative() {
        let od: Decimal = "-42.5".parse().unwrap();
        let bd = bigdecimal::BigDecimal::try_from(&od).unwrap();
        let expected = bigdecimal::BigDecimal::from_str("-42.5").unwrap();
        assert_eq!(bd, expected);
    }

    #[test]
    fn into_bigdecimal_zero() {
        let od = Decimal::zero();
        let bd = bigdecimal::BigDecimal::try_from(&od).unwrap();
        assert_eq!(bd, bigdecimal::BigDecimal::from(0));
    }

    #[test]
    fn into_bigdecimal_owned() {
        let od: Decimal = "99".parse().unwrap();
        let bd = bigdecimal::BigDecimal::try_from(od).unwrap();
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
            let bd_restored = bigdecimal::BigDecimal::try_from(&od).unwrap();
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
            let bd = bigdecimal::BigDecimal::try_from(&od_original).unwrap();
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
