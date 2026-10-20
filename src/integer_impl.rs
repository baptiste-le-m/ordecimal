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
#[non_exhaustive]
pub enum IntegerConversionError {
    /// The decimal value has a non-zero fractional part.
    #[error("value {0} is not an integer")]
    NotAnInteger(String),

    /// The decimal value exceeds the representable range of the target type.
    #[error("value {0} is outside the representable range of the target integer type")]
    OutOfRange(String),
}

/// Why [`integer_string`] could not write a value as a plain integer.
pub(crate) enum IntegerStringError {
    /// The value has a fractional part.
    NotAnInteger,
    /// The integer has more digits than the caller allowed.
    TooLarge,
}

/// Write `value` as a plain integer string (`"-1200"`), refusing fractions and
/// integers longer than `max_digits` digits.
///
/// Works from the decoded parts rather than [`Decimal::to_plain_string`],
/// which switches to scientific form past exponent 1000 and so hides both
/// fractions (`1e-1001`) and integers (`1.5e1001`). The length is checked
/// before the digit string is built, so `1e1000000000000` fails at once
/// instead of exhausting memory.
pub(crate) fn integer_string(
    value: &Decimal,
    max_digits: usize,
) -> Result<String, IntegerStringError> {
    if value.is_zero() {
        return Ok("0".to_string());
    }

    value
        .with_significand(|sig, parts| {
            // With a negative exponent the value is < 1, always fractional.
            if !parts.exponent_positive {
                return Err(IntegerStringError::NotAnInteger);
            }

            // With a non-negative exponent the number of integer digits is
            // `exponent + 1`. If that covers all significand digits the value
            // is an integer; the remaining positions are trailing zeros. An
            // exponent past usize is an integer far beyond any budget.
            let int_digits = usize::try_from(parts.exponent)
                .ok()
                .and_then(|e| e.checked_add(1))
                .ok_or(IntegerStringError::TooLarge)?;
            if int_digits < sig.len() {
                // Some significand digits fall after the decimal point → fractional.
                return Err(IntegerStringError::NotAnInteger);
            }
            if int_digits > max_digits {
                return Err(IntegerStringError::TooLarge);
            }

            // Build the full digit string: significand digits + trailing zeros.
            let mut digit_string = String::with_capacity(int_digits + 1);
            if !parts.positive {
                digit_string.push('-');
            }
            digit_string.push_str(sig);
            digit_string.extend(std::iter::repeat('0').take(int_digits - sig.len()));
            Ok(digit_string)
        })
        .unwrap_or(Err(IntegerStringError::NotAnInteger))
}

/// Digits in the longest primitive integer, `u128::MAX` (and `i128::MIN`).
const MAX_PRIMITIVE_DIGITS: usize = 39;

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
                    let s = integer_string(value, MAX_PRIMITIVE_DIGITS).map_err(|e| match e {
                        IntegerStringError::NotAnInteger => {
                            IntegerConversionError::NotAnInteger(value.to_plain_string())
                        }
                        IntegerStringError::TooLarge => {
                            IntegerConversionError::OutOfRange(value.to_plain_string())
                        }
                    })?;

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
    fn try_into_i64_fraction_in_scientific_form_rejected() {
        // Past exponent 1000 to_plain_string switches to scientific form, so
        // this fraction has no '.' to spot — it used to come back OutOfRange.
        let od: Decimal = "1e-1001".parse().unwrap();
        assert!(matches!(
            i64::try_from(&od),
            Err(IntegerConversionError::NotAnInteger(_))
        ));
    }

    #[test]
    fn try_into_i64_huge_integer_in_scientific_form_out_of_range() {
        // "1.5e1001" has a '.' but is an integer — too large, not fractional.
        let od: Decimal = "1.5e1001".parse().unwrap();
        assert!(matches!(
            i64::try_from(&od),
            Err(IntegerConversionError::OutOfRange(_))
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
