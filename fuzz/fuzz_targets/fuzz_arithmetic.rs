#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use ordecimal::Decimal;

/// Structured input that always produces a valid decimal string.
///
/// Uses a bounded exponent (i16) so that arithmetic between two values
/// doesn't hit the 100 000-digit guard (max exponent gap ≈ 65 535).
#[derive(Debug, Arbitrary)]
struct DecimalInput {
    negative: bool,
    integer_digits: Vec<u8>,
    fractional_digits: Option<Vec<u8>>,
    exponent: Option<i16>,
}

impl DecimalInput {
    fn to_decimal_string(&self) -> String {
        let mut s = String::new();

        if self.negative {
            s.push('-');
        }

        if self.integer_digits.is_empty() {
            s.push('0');
        } else {
            for &d in &self.integer_digits {
                s.push((b'0' + d % 10) as char);
            }
        }

        if let Some(ref frac) = self.fractional_digits {
            if !frac.is_empty() {
                s.push('.');
                for &d in frac {
                    s.push((b'0' + d % 10) as char);
                }
            }
        }

        if let Some(exp) = self.exponent {
            s.push('e');
            s.push_str(&exp.to_string());
        }

        s
    }

    fn to_decimal(&self) -> Option<Decimal> {
        self.to_decimal_string().parse().ok()
    }
}

#[derive(Debug, Arbitrary)]
struct ArithmeticInput {
    a: DecimalInput,
    b: DecimalInput,
}

fuzz_target!(|input: ArithmeticInput| {
    let a = input
        .a
        .to_decimal()
        .unwrap_or_else(|| panic!("failed to parse a: {:?}", input.a.to_decimal_string()));
    let b = input
        .b
        .to_decimal()
        .unwrap_or_else(|| panic!("failed to parse b: {:?}", input.b.to_decimal_string()));

    let zero = Decimal::zero();

    // -- Negation --

    // Involution: -(-a) == a
    let neg_neg_a = -(-a.clone());
    assert_eq!(
        a.as_bytes(),
        neg_neg_a.as_bytes(),
        "negation involution failed for {:?}",
        a.to_plain_string()
    );

    // -- Addition --

    // Commutativity: a + b == b + a
    let ab = &a + &b;
    let ba = &b + &a;
    assert_eq!(
        ab.as_bytes(),
        ba.as_bytes(),
        "commutativity failed: {} + {}",
        a.to_plain_string(),
        b.to_plain_string()
    );

    // Additive identity: a + 0 == a
    let a_plus_0 = &a + &zero;
    assert_eq!(
        a.as_bytes(),
        a_plus_0.as_bytes(),
        "additive identity failed for {}",
        a.to_plain_string()
    );

    // Self-subtraction: a - a == 0
    let a_minus_a = &a - &a;
    assert!(
        a_minus_a.is_zero(),
        "self-subtraction non-zero for {}: got {}",
        a.to_plain_string(),
        a_minus_a.to_plain_string()
    );

    // Subtraction is add-neg: a - b == a + (-b)
    let a_sub_b = &a - &b;
    let a_add_neg_b = &a + &(-b.clone());
    assert_eq!(
        a_sub_b.as_bytes(),
        a_add_neg_b.as_bytes(),
        "sub vs add-neg mismatch: {} - {}",
        a.to_plain_string(),
        b.to_plain_string()
    );

    // -- Round-trip: result re-encodes correctly --

    let ab_bytes = ab.as_bytes();
    let ab_recovered = Decimal::from_bytes(ab_bytes)
        .unwrap_or_else(|e| panic!("from_bytes failed on addition result: {e}"));
    assert_eq!(
        ab_bytes,
        ab_recovered.as_bytes(),
        "addition result round-trip failed"
    );

    // Result's to_plain_string must re-parse to the same value
    let ab_plain = ab.to_plain_string();
    let ab_reparsed: Decimal = ab_plain
        .parse()
        .unwrap_or_else(|e| panic!("addition result {ab_plain:?} failed to reparse: {e}"));
    assert_eq!(
        ab.as_bytes(),
        ab_reparsed.as_bytes(),
        "addition result to_plain_string round-trip mismatch"
    );
});
