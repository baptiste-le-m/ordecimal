//! [`TryFrom<Decimal>`] conversions to Rust primitive integer types.
//!
//! The reverse direction ([`From<integer>`] for [`Decimal`]) is already
//! provided directly in [`decimal.rs`](crate::decimal) with optimised
//! direct encoding.  This module adds the fallible conversion *back* to
//! integers, which can fail when the decimal has a fractional part or
//! exceeds the target type's range.

use crate::Decimal;
use thiserror::Error;

/// Error returned when a [`Decimal`] cannot be converted to a primitive integer.
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum IntegerConversionError {
    /// The decimal value has a non-zero fractional part.
    #[error("value {0} is not an integer")]
    NotAnInteger(String),

    /// The decimal value exceeds the representable range of the target type.
    #[error("value {0} is outside the representable range of the target integer type")]
    OutOfRange(String),
}

/// Implement `TryFrom<Decimal> for $int` and `TryFrom<&Decimal> for $int`.
macro_rules! impl_try_into_integer {
    ($($int:ty),+) => {
        $(
            impl TryFrom<Decimal> for $int {
                type Error = IntegerConversionError;

                fn try_from(value: Decimal) -> Result<Self, Self::Error> {
                    <$int>::try_from(&value)
                }
            }

            impl TryFrom<&Decimal> for $int {
                type Error = IntegerConversionError;

                fn try_from(value: &Decimal) -> Result<Self, Self::Error> {
                    let s = value.to_plain_string();

                    // Reject values with a fractional part.
                    if s.contains('.') {
                        return Err(IntegerConversionError::NotAnInteger(s));
                    }

                    s.parse::<$int>()
                        .map_err(|_| IntegerConversionError::OutOfRange(s))
                }
            }
        )+
    };
}

impl_try_into_integer!(i8, i16, i32, i64, i128, u8, u16, u32, u64, u128);

#[cfg(test)]
mod tests {
    use super::*;

    // ── TryFrom<Decimal> for integer ───────────────────────────────────

    #[test]
    fn try_into_i64_positive() {
        let od: Decimal = "42".parse().unwrap();
        let v = i64::try_from(&od).unwrap();
        assert_eq!(v, 42);
    }

    #[test]
    fn try_into_i64_negative() {
        let od: Decimal = "-42".parse().unwrap();
        let v = i64::try_from(&od).unwrap();
        assert_eq!(v, -42);
    }

    #[test]
    fn try_into_i64_zero() {
        let od = Decimal::zero();
        let v = i64::try_from(&od).unwrap();
        assert_eq!(v, 0);
    }

    #[test]
    fn try_into_u64_from_negative_fails() {
        let od: Decimal = "-1".parse().unwrap();
        let result = u64::try_from(&od);
        assert!(matches!(result, Err(IntegerConversionError::OutOfRange(_))));
    }

    #[test]
    fn try_into_i8_out_of_range() {
        let od: Decimal = "200".parse().unwrap();
        let result = i8::try_from(&od);
        assert!(matches!(result, Err(IntegerConversionError::OutOfRange(_))));
    }

    #[test]
    fn try_into_i64_fractional_rejected() {
        let od: Decimal = "42.5".parse().unwrap();
        let result = i64::try_from(&od);
        assert!(matches!(
            result,
            Err(IntegerConversionError::NotAnInteger(_))
        ));
    }

    #[test]
    fn try_into_u128_max_roundtrip() {
        let od = Decimal::from(u128::MAX);
        let v = u128::try_from(&od).unwrap();
        assert_eq!(v, u128::MAX);
    }

    #[test]
    fn try_into_i128_min_roundtrip() {
        let od = Decimal::from(i128::MIN);
        let v = i128::try_from(&od).unwrap();
        assert_eq!(v, i128::MIN);
    }

    // ── Owned TryFrom ──────────────────────────────────────────────────

    #[test]
    fn try_into_i64_owned() {
        let od: Decimal = "99".parse().unwrap();
        let v = i64::try_from(od).unwrap();
        assert_eq!(v, 99);
    }

    // ── Roundtrip ──────────────────────────────────────────────────────

    #[test]
    fn roundtrip_i64() {
        let values: &[i64] = &[0, 1, -1, 42, -42, i64::MAX, i64::MIN];
        for &v in values {
            let od = Decimal::from(v);
            let back = i64::try_from(&od).unwrap();
            assert_eq!(v, back, "roundtrip failed for {v}");
        }
    }

    #[test]
    fn roundtrip_u64() {
        let values: &[u64] = &[0, 1, 42, u64::MAX];
        for &v in values {
            let od = Decimal::from(v);
            let back = u64::try_from(&od).unwrap();
            assert_eq!(v, back, "roundtrip failed for {v}");
        }
    }

    // ── Order preservation ─────────────────────────────────────────────

    #[test]
    fn order_preserved_i64() {
        let values: Vec<i64> = vec![-1000, -100, -10, -1, 0, 1, 10, 100, 1000];
        let ordecimal_values: Vec<Decimal> = values.iter().map(|&v| Decimal::from(v)).collect();

        for i in 1..ordecimal_values.len() {
            assert!(
                ordecimal_values[i - 1] < ordecimal_values[i],
                "order not preserved: {} < {}",
                values[i - 1],
                values[i]
            );
        }
    }
}
