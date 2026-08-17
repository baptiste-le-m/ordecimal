//! Arithmetic operations for [`Decimal`]: `Add`, `Sub`, `Neg`, the matching
//! assignment operators, and [`Sum`].
//!
//! All arithmetic is performed on digit arrays (base-10, schoolbook method)
//! with no floating-point involved, preserving full precision.
//!
//! # Digit budget
//!
//! Adding two values whose exponents are far apart forces the smaller one to be
//! materialized as trailing zeros: `1e100 + 1` needs 101 digits. Operands are
//! aligned this way up to `MAX_DIGIT_COUNT` digits; beyond that the operation
//! **panics** rather than allocating unbounded memory. The limit is 100 000
//! digits — far past any practical use (DynamoDB numbers hold at most 38), but
//! reachable with deliberately extreme exponents such as `1e100000 + 1`.
//! Treat it like integer overflow in `std`: a bug in the caller, not a runtime
//! condition to handle.

use std::cmp::Ordering;
use std::iter::Sum;
use std::ops::{Add, AddAssign, Neg, Sub, SubAssign};

use crate::decimal::Decimal;
use crate::decoder::decode_to_parts;
use crate::encoder::encode_from_parts;

// ---------------------------------------------------------------------------
// Internal representation for arithmetic
// ---------------------------------------------------------------------------

/// Maximum number of digits the arithmetic engine will materialize when
/// aligning operands with very different exponents.  This prevents
/// pathological OOM from inputs like `1e+2_000_000_000 + 1e-2_000_000_000`.
/// 100 000 digits is far beyond any practical need (DynamoDB uses at most 38).
const MAX_DIGIT_COUNT: usize = 100_000;

/// A decimal decomposed for arithmetic: `sign × digits × 10^power`.
///
/// `digits` is a most-significant-first array of values 0–9.
/// `power` is the exponent of the least-significant digit, stored as `i128`
/// so that any `u64` exponent from the encoding layer can be represented
/// with either sign without truncation.
///
/// Example: 123.456 → positive=true, digits=[1,2,3,4,5,6], power=-3
///   because 123456 × 10^(-3) = 123.456
struct Decomposed {
    positive: bool,
    digits: Vec<u8>,
    power: i128,
}

impl Decomposed {
    /// Decompose a [`Decimal`] into sign, digit array, and power.
    fn from_decimal(d: &Decimal) -> Self {
        if d.is_zero() {
            return Decomposed {
                positive: true,
                digits: vec![0],
                power: 0,
            };
        }

        let decoded = decode_to_parts(d.as_bytes()).expect("Decimal bytes should always be valid");

        // Strip trailing zeros from significand (declet padding)
        let sig_end = decoded
            .significand
            .iter()
            .rposition(|&x| x != 0)
            .map_or(1, |p| p + 1);
        let digits = decoded.significand[..sig_end].to_vec();

        let signed_exp: i128 = if decoded.exponent_positive {
            i128::from(decoded.exponent)
        } else {
            -i128::from(decoded.exponent)
        };

        // power = signed_exp - (number_of_digits - 1)
        // because value = d0.d1d2...dn × 10^signed_exp
        //               = d0d1d2...dn × 10^(signed_exp - n)
        let power = signed_exp - (digits.len() as i128 - 1);

        Decomposed {
            positive: decoded.positive,
            digits,
            power,
        }
    }

    /// Convert back to a [`Decimal`].
    fn to_decimal(&self) -> Decimal {
        // Strip leading zeros
        let start = match self.digits.iter().position(|&d| d != 0) {
            Some(pos) => pos,
            None => return Decimal::zero(),
        };

        let digits = &self.digits[start..];

        // Strip trailing zeros (they're encoded via the exponent)
        let last_nonzero = digits.iter().rposition(|&d| d != 0).unwrap();
        let significand = &digits[..=last_nonzero];

        // signed_exp = power + (total_digit_count - 1)
        // where total_digit_count is BEFORE trailing zero stripping
        let signed_exp = self.power + (digits.len() as i128 - 1);

        let (exponent, exponent_positive) = if signed_exp >= 0 {
            // i128 → u64: safe because the encoder uses Elias Gamma with count < 64,
            // so valid exponents fit in u64. Panic on overflow = corrupted Decomposed.
            (u64::try_from(signed_exp).expect("exponent overflow"), true)
        } else {
            (
                u64::try_from(signed_exp.unsigned_abs()).expect("exponent overflow"),
                false,
            )
        };

        let bytes = encode_from_parts(self.positive, exponent_positive, exponent, significand);
        Decimal::from_bytes_unchecked(bytes)
    }
}

// ---------------------------------------------------------------------------
// Digit-array arithmetic (schoolbook base-10)
// ---------------------------------------------------------------------------

/// Add two digit arrays of the same length. Returns a result that may be one
/// digit longer due to carry.
fn add_digit_arrays(a: &[u8], b: &[u8]) -> Vec<u8> {
    debug_assert_eq!(a.len(), b.len());
    let len = a.len();
    let mut result = vec![0u8; len + 1];
    let mut carry: u8 = 0;

    for i in (0..len).rev() {
        let sum = a[i] + b[i] + carry;
        result[i + 1] = sum % 10;
        carry = sum / 10;
    }
    result[0] = carry;

    result
}

/// Subtract digit array `b` from `a` (`a >= b` required, same length).
fn sub_digit_arrays(a: &[u8], b: &[u8]) -> Vec<u8> {
    debug_assert_eq!(a.len(), b.len());
    let len = a.len();
    let mut result = vec![0u8; len];
    let mut borrow: u8 = 0;

    for i in (0..len).rev() {
        let ai = a[i] as i16;
        let bi = b[i] as i16 + borrow as i16;
        if ai >= bi {
            result[i] = (ai - bi) as u8;
            borrow = 0;
        } else {
            result[i] = (ai + 10 - bi) as u8;
            borrow = 1;
        }
    }
    debug_assert_eq!(borrow, 0, "sub_digit_arrays: a must be >= b");

    result
}

/// Left-pad a digit array with zeros to reach `target_len`.
fn left_pad(digits: &[u8], target_len: usize) -> Vec<u8> {
    if digits.len() >= target_len {
        return digits.to_vec();
    }
    let mut padded = vec![0u8; target_len - digits.len()];
    padded.extend_from_slice(digits);
    padded
}

/// Core addition of two decomposed decimals.
fn add_decomposed(a: &Decomposed, b: &Decomposed) -> Decomposed {
    // Handle zeros
    let a_is_zero = a.digits.iter().all(|&d| d == 0);
    let b_is_zero = b.digits.iter().all(|&d| d == 0);
    if a_is_zero {
        return Decomposed {
            positive: b.positive,
            digits: b.digits.clone(),
            power: b.power,
        };
    }
    if b_is_zero {
        return Decomposed {
            positive: a.positive,
            digits: a.digits.clone(),
            power: a.power,
        };
    }

    // Align powers by padding with trailing zeros
    let min_power = a.power.min(b.power);
    let a_trail_128 = a.power - min_power;
    let b_trail_128 = b.power - min_power;

    // Guard: refuse to materialize an absurdly large digit array.
    // The total digit count after alignment is at most
    //   max(a.digits.len() + a_trail, b.digits.len() + b_trail).
    // If the trailing-zero padding alone exceeds MAX_DIGIT_COUNT, the
    // computation is impractical — panic with a clear message.
    let a_trail: usize = usize::try_from(a_trail_128).unwrap_or_else(|_| {
        panic!(
            "ordecimal: arithmetic requires {a_trail_128} trailing zeros — \
             exceeds maximum of {MAX_DIGIT_COUNT} digits"
        )
    });
    let b_trail: usize = usize::try_from(b_trail_128).unwrap_or_else(|_| {
        panic!(
            "ordecimal: arithmetic requires {b_trail_128} trailing zeros — \
             exceeds maximum of {MAX_DIGIT_COUNT} digits"
        )
    });
    assert!(
        a.digits.len().saturating_add(a_trail) <= MAX_DIGIT_COUNT
            && b.digits.len().saturating_add(b_trail) <= MAX_DIGIT_COUNT,
        "ordecimal: arithmetic would produce more than {MAX_DIGIT_COUNT} digits \
         (a: {} + {a_trail}, b: {} + {b_trail})",
        a.digits.len(),
        b.digits.len(),
    );

    let mut a_digits = a.digits.clone();
    a_digits.resize(a_digits.len() + a_trail, 0);

    let mut b_digits = b.digits.clone();
    b_digits.resize(b_digits.len() + b_trail, 0);

    // Left-pad to same length
    let max_len = a_digits.len().max(b_digits.len());
    a_digits = left_pad(&a_digits, max_len);
    b_digits = left_pad(&b_digits, max_len);

    if a.positive == b.positive {
        // Same sign: add magnitudes, keep sign
        let result_digits = add_digit_arrays(&a_digits, &b_digits);
        Decomposed {
            positive: a.positive,
            digits: result_digits,
            // The add may produce an extra leading digit, but power stays the same
            // because we didn't shift the least-significant position.
            power: min_power,
        }
    } else {
        // Different signs: subtract smaller magnitude from larger
        match a_digits.cmp(&b_digits) {
            Ordering::Equal => Decomposed {
                positive: true,
                digits: vec![0],
                power: 0,
            },
            Ordering::Greater => {
                let result_digits = sub_digit_arrays(&a_digits, &b_digits);
                Decomposed {
                    positive: a.positive,
                    digits: result_digits,
                    power: min_power,
                }
            }
            Ordering::Less => {
                let result_digits = sub_digit_arrays(&b_digits, &a_digits);
                Decomposed {
                    positive: b.positive,
                    digits: result_digits,
                    power: min_power,
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Trait implementations
// ---------------------------------------------------------------------------

/// Exact addition, preserving every digit of both operands.
///
/// # Panics
///
/// Panics if aligning the operands would need more than 100 000 digits, which
/// only happens for exponents far outside any practical range (`1e100000 + 1`).
///
/// ```rust
/// use ordecimal::Decimal;
///
/// let a: Decimal = "0.1".parse().unwrap();
/// let b: Decimal = "0.2".parse().unwrap();
/// assert_eq!((&a + &b).to_plain_string(), "0.3");
/// ```
impl Add for &Decimal {
    type Output = Decimal;

    fn add(self, rhs: &Decimal) -> Decimal {
        let a = Decomposed::from_decimal(self);
        let b = Decomposed::from_decimal(rhs);
        add_decomposed(&a, &b).to_decimal()
    }
}

impl Add for Decimal {
    type Output = Decimal;

    fn add(self, rhs: Decimal) -> Decimal {
        &self + &rhs
    }
}

impl Add<&Decimal> for Decimal {
    type Output = Decimal;

    fn add(self, rhs: &Decimal) -> Decimal {
        &self + rhs
    }
}

impl Add<Decimal> for &Decimal {
    type Output = Decimal;

    fn add(self, rhs: Decimal) -> Decimal {
        self + &rhs
    }
}

impl AddAssign for Decimal {
    fn add_assign(&mut self, rhs: Decimal) {
        *self = &*self + &rhs;
    }
}

impl AddAssign<&Decimal> for Decimal {
    fn add_assign(&mut self, rhs: &Decimal) {
        *self = &*self + rhs;
    }
}

/// Negation. Zero is its own negative — there is no −0 in this encoding.
impl Neg for &Decimal {
    type Output = Decimal;

    fn neg(self) -> Decimal {
        if self.is_zero() {
            return self.clone();
        }
        let mut d = Decomposed::from_decimal(self);
        d.positive = !d.positive;
        d.to_decimal()
    }
}

impl Neg for Decimal {
    type Output = Decimal;

    fn neg(self) -> Decimal {
        if self.is_zero() {
            return self;
        }
        let mut d = Decomposed::from_decimal(&self);
        d.positive = !d.positive;
        d.to_decimal()
    }
}

/// Exact subtraction, preserving every digit of both operands.
///
/// # Panics
///
/// Same digit budget as [`Add`]: panics past 100 000 aligned digits.
impl Sub for &Decimal {
    type Output = Decimal;

    fn sub(self, rhs: &Decimal) -> Decimal {
        self + &(-rhs)
    }
}

impl Sub for Decimal {
    type Output = Decimal;

    fn sub(self, rhs: Decimal) -> Decimal {
        &self - &rhs
    }
}

impl Sub<&Decimal> for Decimal {
    type Output = Decimal;

    fn sub(self, rhs: &Decimal) -> Decimal {
        &self - rhs
    }
}

impl Sub<Decimal> for &Decimal {
    type Output = Decimal;

    fn sub(self, rhs: Decimal) -> Decimal {
        self - &rhs
    }
}

impl SubAssign for Decimal {
    fn sub_assign(&mut self, rhs: Decimal) {
        *self = &*self - &rhs;
    }
}

impl SubAssign<&Decimal> for Decimal {
    fn sub_assign(&mut self, rhs: &Decimal) {
        *self = &*self - rhs;
    }
}

/// Sums an iterator of decimals exactly; an empty iterator sums to zero.
///
/// ```rust
/// use ordecimal::Decimal;
///
/// let values: Vec<Decimal> = ["0.1", "0.2", "0.3"]
///     .iter()
///     .map(|s| s.parse().unwrap())
///     .collect();
/// let total: Decimal = values.iter().sum();
/// assert_eq!(total.to_plain_string(), "0.6");
/// ```
impl Sum for Decimal {
    fn sum<I: Iterator<Item = Decimal>>(iter: I) -> Decimal {
        iter.fold(Decimal::zero(), |acc, x| &acc + &x)
    }
}

impl<'a> Sum<&'a Decimal> for Decimal {
    fn sum<I: Iterator<Item = &'a Decimal>>(iter: I) -> Decimal {
        iter.fold(Decimal::zero(), |acc, x| &acc + x)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Parse shorthand
    fn d(s: &str) -> Decimal {
        s.parse().unwrap()
    }

    /// Assert that a + b = expected (by comparing plain string output)
    fn assert_add(a: &str, b: &str, expected: &str) {
        let result = &d(a) + &d(b);
        let result_str = result.to_plain_string();
        assert_eq!(
            result_str, expected,
            "{a} + {b}: expected {expected}, got {result_str}"
        );
    }

    /// Assert that a - b = expected
    fn assert_sub(a: &str, b: &str, expected: &str) {
        let result = &d(a) - &d(b);
        let result_str = result.to_plain_string();
        assert_eq!(
            result_str, expected,
            "{a} - {b}: expected {expected}, got {result_str}"
        );
    }

    // ── Basic addition ──────────────────────────────────────────────────

    #[test]
    fn add_positive_integers() {
        assert_add("1", "2", "3");
        assert_add("100", "200", "300");
        assert_add("999", "1", "1000");
        assert_add("123456789", "987654321", "1111111110");
    }

    #[test]
    fn add_with_decimals() {
        assert_add("1.5", "2.3", "3.8");
        assert_add("0.1", "0.2", "0.3");
        assert_add("123.456", "0.544", "124");
    }

    #[test]
    fn add_different_scales() {
        assert_add("1000", "0.001", "1000.001");
        assert_add("1", "0.00001", "1.00001");
    }

    #[test]
    fn add_with_carry() {
        assert_add("9", "1", "10");
        assert_add("99", "1", "100");
        assert_add("999999", "1", "1000000");
    }

    // ── Addition with negative numbers ──────────────────────────────────

    #[test]
    fn add_negative_numbers() {
        assert_add("-1", "-2", "-3");
        assert_add("-100", "-200", "-300");
    }

    #[test]
    fn add_mixed_signs() {
        assert_add("5", "-3", "2");
        assert_add("-3", "5", "2");
        assert_add("3", "-5", "-2");
        assert_add("-5", "3", "-2");
    }

    #[test]
    fn add_to_zero() {
        assert_add("42", "-42", "0");
        assert_add("-42", "42", "0");
        assert_add("123.456", "-123.456", "0");
    }

    // ── Zero cases ──────────────────────────────────────────────────────

    #[test]
    fn add_zero() {
        assert_add("0", "0", "0");
        assert_add("42", "0", "42");
        assert_add("0", "42", "42");
        assert_add("-7", "0", "-7");
        assert_add("0", "-7", "-7");
    }

    // ── Subtraction ─────────────────────────────────────────────────────

    #[test]
    fn sub_positive_integers() {
        assert_sub("5", "3", "2");
        assert_sub("1000", "1", "999");
        assert_sub("1000", "999", "1");
    }

    #[test]
    fn sub_result_negative() {
        assert_sub("3", "5", "-2");
        assert_sub("1", "1000", "-999");
    }

    #[test]
    fn sub_to_zero() {
        assert_sub("42", "42", "0");
        assert_sub("123.456", "123.456", "0");
    }

    #[test]
    fn sub_with_decimals() {
        assert_sub("10.5", "3.2", "7.3");
        assert_sub("1", "0.001", "0.999");
    }

    #[test]
    fn sub_negative_numbers() {
        // 5 - (-3) = 8
        assert_sub("5", "-3", "8");
        // -5 - (-3) = -2
        assert_sub("-5", "-3", "-2");
        // -3 - (-5) = 2
        assert_sub("-3", "-5", "2");
    }

    // ── Negation ────────────────────────────────────────────────────────

    #[test]
    fn neg_positive() {
        let a = d("42");
        let neg_a = -a;
        assert_eq!(neg_a.to_plain_string(), "-42");
    }

    #[test]
    fn neg_negative() {
        let a = d("-42");
        let neg_a = -a;
        assert_eq!(neg_a.to_plain_string(), "42");
    }

    #[test]
    fn neg_zero() {
        let a = d("0");
        let neg_a = -a;
        assert!(neg_a.is_zero());
    }

    // ── Large numbers (DynamoDB range) ──────────────────────────────────

    #[test]
    fn add_large_integers() {
        assert_add(
            "99999999999999999999999999999999999999",
            "1",
            "100000000000000000000000000000000000000",
        );
    }

    #[test]
    fn add_38_digit_precision() {
        // Two 19-digit numbers — result is 20 digits, well within precision
        assert_add(
            "1234567890123456789",
            "9876543210987654321",
            "11111111101111111110",
        );
    }

    #[test]
    fn sub_large_numbers() {
        assert_sub(
            "100000000000000000000000000000000000000",
            "1",
            "99999999999999999999999999999999999999",
        );
    }

    // ── Very different exponents ────────────────────────────────────────

    #[test]
    fn add_very_different_exponents() {
        assert_add("1e20", "1", "100000000000000000001");
        assert_add("1", "1e-20", "1.00000000000000000001");
    }

    // ── Order preservation after arithmetic ─────────────────────────────

    #[test]
    fn addition_preserves_order() {
        let values = [d("-100"), d("-1"), d("0"), d("1"), d("100")];

        // Adding a positive number to each should preserve order
        let offset = d("50");
        let shifted: Vec<Decimal> = values.iter().map(|v| v + &offset).collect();
        for i in 1..shifted.len() {
            assert!(
                shifted[i - 1] < shifted[i],
                "order broken after adding 50: index {} vs {}",
                i - 1,
                i
            );
        }
    }

    // ── Commutativity ───────────────────────────────────────────────────

    #[test]
    fn addition_is_commutative() {
        let cases = [
            ("123", "456"),
            ("-7", "3"),
            ("0.001", "1000"),
            ("1e10", "-1e5"),
        ];
        for (a, b) in cases {
            let ab = &d(a) + &d(b);
            let ba = &d(b) + &d(a);
            assert_eq!(
                ab.to_plain_string(),
                ba.to_plain_string(),
                "commutativity failed for {a} + {b}"
            );
        }
    }

    // ── Round-trip: arithmetic result re-encodes correctly ──────────────

    #[test]
    fn arithmetic_result_roundtrips() {
        let result = &d("123.456") + &d("876.544");
        let bytes = result.as_bytes();
        let recovered = Decimal::from_bytes(bytes).unwrap();
        assert_eq!(result, recovered);
    }

    // ── Operand ownership combinations ──────────────────────────────────

    #[test]
    fn add_accepts_every_ownership_combination() {
        let expected = "8";
        assert_eq!((d("5") + d("3")).to_plain_string(), expected);
        assert_eq!((&d("5") + &d("3")).to_plain_string(), expected);
        assert_eq!((d("5") + &d("3")).to_plain_string(), expected);
        assert_eq!((&d("5") + d("3")).to_plain_string(), expected);
    }

    #[test]
    fn sub_accepts_every_ownership_combination() {
        let expected = "2";
        assert_eq!((d("5") - d("3")).to_plain_string(), expected);
        assert_eq!((&d("5") - &d("3")).to_plain_string(), expected);
        assert_eq!((d("5") - &d("3")).to_plain_string(), expected);
        assert_eq!((&d("5") - d("3")).to_plain_string(), expected);
    }

    // ── Assignment operators ────────────────────────────────────────────

    #[test]
    fn add_assign_owned_and_borrowed() {
        let mut a = d("1.5");
        a += d("2.25");
        assert_eq!(a.to_plain_string(), "3.75");
        a += &d("-0.75");
        assert_eq!(a.to_plain_string(), "3");
    }

    #[test]
    fn sub_assign_owned_and_borrowed() {
        let mut a = d("10");
        a -= d("2.5");
        assert_eq!(a.to_plain_string(), "7.5");
        a -= &d("7.5");
        assert!(a.is_zero());
    }

    // ── Sum ─────────────────────────────────────────────────────────────

    #[test]
    fn sum_of_owned_values() {
        let values = vec![d("0.1"), d("0.2"), d("0.3")];
        let total: Decimal = values.into_iter().sum();
        assert_eq!(total.to_plain_string(), "0.6");
    }

    #[test]
    fn sum_of_borrowed_values() {
        let values = [d("1e10"), d("-1"), d("0.001")];
        let total: Decimal = values.iter().sum();
        assert_eq!(total.to_plain_string(), "9999999999.001");
    }

    #[test]
    fn sum_of_empty_iterator_is_zero() {
        let total: Decimal = Vec::<Decimal>::new().into_iter().sum();
        assert!(total.is_zero());
    }

    // ── Digit budget ────────────────────────────────────────────────────

    #[test]
    #[should_panic(expected = "more than 100000 digits")]
    fn add_beyond_digit_budget_panics() {
        let _ = &d("1e100000") + &d("1");
    }
}
