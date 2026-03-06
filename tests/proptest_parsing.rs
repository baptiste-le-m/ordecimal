//! Property-based tests for `Decimal` parsing, roundtripping, and ordering.
//!
//! Uses `proptest` to generate arbitrary inputs and verify invariants that must
//! hold for all values.

use ordecimal::Decimal;
use proptest::prelude::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

// ---------------------------------------------------------------------------
// Strategies
// ---------------------------------------------------------------------------

/// Generate a syntactically plausible decimal string with:
/// optional sign, 1-40 integer digits, optional fractional part (1-40 digits),
/// and optional scientific-notation exponent.
fn arb_decimal_string() -> impl Strategy<Value = String> {
    (
        prop::option::of(prop::sample::select(vec!["+", "-"])),
        "[0-9]{1,40}",
        prop::option::of("[0-9]{1,40}"),
        prop::option::of(-1000i64..1000),
    )
        .prop_map(|(sign, integer, frac, exp)| {
            let mut s = String::new();
            if let Some(sign) = sign {
                s.push_str(sign);
            }
            s.push_str(&integer);
            if let Some(frac) = frac {
                s.push('.');
                s.push_str(&frac);
            }
            if let Some(exp) = exp {
                s.push('e');
                s.push_str(&exp.to_string());
            }
            s
        })
}

/// Generate a string that is guaranteed to parse successfully into a `Decimal`.
/// We parse eagerly and discard inputs that fail.
fn arb_valid_decimal() -> impl Strategy<Value = (String, Decimal)> {
    arb_decimal_string().prop_filter_map("must parse as Decimal", |s| {
        s.parse::<Decimal>().ok().map(|d| (s, d))
    })
}

/// Generate two valid decimals for comparison.
fn arb_decimal_pair() -> impl Strategy<Value = ((String, Decimal), (String, Decimal))> {
    (arb_valid_decimal(), arb_valid_decimal())
}

// ---------------------------------------------------------------------------
// Property 1: Parsing arbitrary strings never panics
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn parse_never_panics(s in "\\PC*") {
        // Must always return Ok or Err, never panic.
        let _ = s.parse::<Decimal>();
    }
}

// ---------------------------------------------------------------------------
// Property 2: to_plain_string roundtrip
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn to_plain_string_roundtrips((_, decimal) in arb_valid_decimal()) {
        let plain = decimal.to_plain_string();
        let reparsed: Decimal = plain.parse()
            .expect("to_plain_string output must be re-parseable");
        prop_assert_eq!(
            decimal.as_bytes(),
            reparsed.as_bytes(),
            "roundtrip mismatch: plain={:?}",
            plain,
        );
    }
}

// ---------------------------------------------------------------------------
// Property 3: From<i64> agrees with string parsing
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn from_i64_matches_str_parse(n: i64) {
        let from_int = Decimal::from(n);
        let from_str: Decimal = n.to_string().parse()
            .expect("integer string must parse");
        prop_assert_eq!(
            from_int.as_bytes(),
            from_str.as_bytes(),
            "mismatch for i64 value {}",
            n,
        );
    }
}

// ---------------------------------------------------------------------------
// Property 4: From<i128> agrees with string parsing
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn from_i128_matches_str_parse(n: i128) {
        let from_int = Decimal::from(n);
        let from_str: Decimal = n.to_string().parse()
            .expect("integer string must parse");
        prop_assert_eq!(
            from_int.as_bytes(),
            from_str.as_bytes(),
            "mismatch for i128 value {}",
            n,
        );
    }
}

// ---------------------------------------------------------------------------
// Property 5: TryFrom<f64> roundtrip via to_plain_string
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn try_from_f64_roundtrips(x: f64) {
        // TryFrom rejects NaN/Infinity, so filter to Ok values
        if let Ok(d) = Decimal::try_from(x) {
            let plain = d.to_plain_string();
            let reparsed: Decimal = plain.parse()
                .expect("to_plain_string of TryFrom<f64> must be re-parseable");
            prop_assert_eq!(
                d.as_bytes(),
                reparsed.as_bytes(),
                "roundtrip mismatch for f64 {}: plain={:?}",
                x,
                plain,
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Property 6: Order preservation — Decimal ordering matches numeric ordering
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn order_preserved_for_integers(a: i64, b: i64) {
        let da = Decimal::from(a);
        let db = Decimal::from(b);
        prop_assert_eq!(
            a.cmp(&b),
            da.cmp(&db),
            "ordering mismatch: a={}, b={}",
            a, b,
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn order_preserved_for_f64(a: f64, b: f64) {
        // Only test finite, non-NaN values where f64 ordering is meaningful
        prop_assume!(a.is_finite() && b.is_finite() && !a.is_nan() && !b.is_nan());
        // Skip -0 vs +0 edge case (both map to positive zero in Decimal)
        prop_assume!(!(a == 0.0 && b == 0.0));

        let da = Decimal::try_from(a).unwrap();
        let db = Decimal::try_from(b).unwrap();

        let expected = a.partial_cmp(&b).unwrap();
        prop_assert_eq!(
            expected,
            da.cmp(&db),
            "ordering mismatch: a={}, b={}",
            a, b,
        );
    }
}

// ---------------------------------------------------------------------------
// Property 7: Eq ↔ Hash consistency
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn eq_implies_same_hash(
        ((_sa, a), (_sb, b)) in arb_decimal_pair()
    ) {
        if a == b {
            let hash_a = {
                let mut h = DefaultHasher::new();
                a.hash(&mut h);
                h.finish()
            };
            let hash_b = {
                let mut h = DefaultHasher::new();
                b.hash(&mut h);
                h.finish()
            };
            prop_assert_eq!(hash_a, hash_b, "equal Decimals must have equal hashes");
        }
    }
}

// ---------------------------------------------------------------------------
// Property 8: Scientific notation equivalence
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(5_000))]

    #[test]
    fn scientific_notation_equivalent(
        coeff in 1i64..1_000_000,
        exp in -20i32..20,
    ) {
        // Parse via scientific notation
        let sci = format!("{}e{}", coeff, exp);
        let d_sci: Decimal = sci.parse()
            .expect("scientific notation must parse");

        // Expand to plain decimal and parse that
        let plain = d_sci.to_plain_string();
        let d_plain: Decimal = plain.parse()
            .expect("plain expansion must parse");

        prop_assert_eq!(
            d_sci.as_bytes(),
            d_plain.as_bytes(),
            "sci={:?} vs plain={:?}",
            sci,
            plain,
        );
    }
}

// ---------------------------------------------------------------------------
// Property 9: Decode(encode(x)) roundtrip via from_bytes
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn encode_decode_bytes_roundtrip((_, decimal) in arb_valid_decimal()) {
        let bytes = decimal.as_bytes();
        let decoded = Decimal::from_bytes(bytes)
            .expect("encoded bytes must decode successfully");
        prop_assert_eq!(
            decimal.as_bytes(),
            decoded.as_bytes(),
            "encode/decode roundtrip failed",
        );
    }
}

// ---------------------------------------------------------------------------
// Property 10: Arbitrary bytes to from_bytes never panics
// ---------------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10_000))]

    #[test]
    fn from_bytes_never_panics(data: Vec<u8>) {
        // Must always return Ok or Err, never panic.
        let _ = Decimal::from_bytes(&data);
    }
}
