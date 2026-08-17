//! Property tests for `Add`, `Sub`, `Neg` and `Sum`, cross-checked against
//! `bigdecimal` as an independent arbitrary-precision oracle.

use bigdecimal::BigDecimal;
use ordecimal::Decimal;
use proptest::prelude::*;
use std::str::FromStr;

/// Decimal string built from a mantissa and an exponent, e.g. `-1234e-7`.
fn decimal_str() -> impl Strategy<Value = String> {
    (any::<i64>(), -40i32..40i32).prop_map(|(mantissa, exponent)| format!("{mantissa}e{exponent}"))
}

/// Same, but with mantissas far beyond 64 bits, so that significands span many
/// declets and carries have to propagate across them.
fn long_decimal_str() -> impl Strategy<Value = String> {
    (any::<bool>(), "[0-9]{1,200}", -300i32..300i32).prop_map(|(negative, digits, exponent)| {
        let sign = if negative { "-" } else { "" };
        format!("{sign}{digits}e{exponent}")
    })
}

fn ord(s: &str) -> Decimal {
    s.parse().expect("valid decimal string")
}

fn big(s: &str) -> BigDecimal {
    BigDecimal::from_str(s).expect("valid decimal string")
}

/// Compare an ordecimal result against a `bigdecimal` expectation. Both sides
/// are normalized so that trailing-zero differences do not count as mismatches.
fn assert_same_value(
    got: &Decimal,
    expected: &BigDecimal,
) -> Result<(), proptest::test_runner::TestCaseError> {
    let got_big = big(&got.to_plain_string());
    prop_assert_eq!(
        got_big.normalized(),
        expected.normalized(),
        "ordecimal produced {}",
        got.to_plain_string()
    );
    Ok(())
}

proptest! {
    #[test]
    fn add_matches_bigdecimal(a in decimal_str(), b in decimal_str()) {
        assert_same_value(&(&ord(&a) + &ord(&b)), &(big(&a) + big(&b)))?;
    }

    #[test]
    fn sub_matches_bigdecimal(a in decimal_str(), b in decimal_str()) {
        assert_same_value(&(&ord(&a) - &ord(&b)), &(big(&a) - big(&b)))?;
    }

    #[test]
    fn neg_matches_bigdecimal(a in decimal_str()) {
        assert_same_value(&(-&ord(&a)), &(-big(&a)))?;
    }

    #[test]
    fn sum_matches_bigdecimal(values in prop::collection::vec(decimal_str(), 0..8)) {
        let total: Decimal = values.iter().map(|s| ord(s)).sum();
        let expected = values
            .iter()
            .map(|s| big(s))
            .fold(BigDecimal::from(0), |acc, v| acc + v);
        assert_same_value(&total, &expected)?;
    }

    #[test]
    fn addition_is_commutative(a in decimal_str(), b in decimal_str()) {
        prop_assert_eq!(&ord(&a) + &ord(&b), &ord(&b) + &ord(&a));
    }

    #[test]
    fn sub_then_add_restores_original(a in decimal_str(), b in decimal_str()) {
        let restored = &(&ord(&a) - &ord(&b)) + &ord(&b);
        prop_assert_eq!(restored, ord(&a));
    }

    /// Adding the same value to both sides must not reorder them — the whole
    /// point of the encoding is that byte order is numeric order.
    #[test]
    fn addition_preserves_order(a in decimal_str(), b in decimal_str(), c in decimal_str()) {
        let (a, b, c) = (ord(&a), ord(&b), ord(&c));
        prop_assert_eq!(a.cmp(&b), (&a + &c).cmp(&(&b + &c)));
    }

    /// Results of arithmetic must be valid encodings, not just valid values.
    #[test]
    fn arithmetic_results_roundtrip_through_bytes(a in decimal_str(), b in decimal_str()) {
        let sum = &ord(&a) + &ord(&b);
        prop_assert_eq!(Decimal::from_bytes(sum.as_bytes()).unwrap(), sum);
    }

    /// The strong form of the above: a result must be byte-identical to the
    /// same value parsed from its own printed form. `Eq`, `Ord` and `Hash`
    /// compare raw bytes, so a value with two encodings would break all three.
    #[test]
    fn results_are_canonical_encodings(a in decimal_str(), b in decimal_str()) {
        let sum = &ord(&a) + &ord(&b);
        let reparsed_sum = ord(&sum.to_scientific_string());
        prop_assert_eq!(reparsed_sum.as_bytes(), sum.as_bytes());

        let difference = &ord(&a) - &ord(&b);
        let reparsed_difference = ord(&difference.to_scientific_string());
        prop_assert_eq!(reparsed_difference.as_bytes(), difference.as_bytes());
    }

    #[test]
    fn addition_is_associative(a in decimal_str(), b in decimal_str(), c in decimal_str()) {
        let (a, b, c) = (ord(&a), ord(&b), ord(&c));
        prop_assert_eq!(&(&a + &b) + &c, &a + &(&b + &c));
    }

    // ── Long mantissas: multi-declet significands ───────────────────────

    #[test]
    fn add_matches_bigdecimal_for_long_mantissas(
        a in long_decimal_str(),
        b in long_decimal_str(),
    ) {
        assert_same_value(&(&ord(&a) + &ord(&b)), &(big(&a) + big(&b)))?;
    }

    #[test]
    fn sub_matches_bigdecimal_for_long_mantissas(
        a in long_decimal_str(),
        b in long_decimal_str(),
    ) {
        assert_same_value(&(&ord(&a) - &ord(&b)), &(big(&a) - big(&b)))?;
    }

    #[test]
    fn long_mantissa_results_are_canonical(a in long_decimal_str(), b in long_decimal_str()) {
        let sum = &ord(&a) + &ord(&b);
        let reparsed = ord(&sum.to_scientific_string());
        prop_assert_eq!(reparsed.as_bytes(), sum.as_bytes());
    }
}
