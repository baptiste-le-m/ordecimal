#![no_main]

use arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use ordecimal::Decimal;

/// Structured input that always produces a valid decimal string.
///
/// By deriving `Arbitrary`, every fuzz iteration exercises the full
/// roundtrip (parse → to_plain_string → reparse → from_bytes → as_bytes)
/// instead of wasting cycles on unparseable strings.
#[derive(Debug, Arbitrary)]
struct DecimalInput {
    /// Whether the number is negative.
    negative: bool,
    /// Integer part digits (0–9 each, at least one forced).
    integer_digits: Vec<u8>,
    /// Optional fractional part digits.
    fractional_digits: Option<Vec<u8>>,
    /// Optional scientific notation exponent.
    exponent: Option<i16>,
}

impl DecimalInput {
    fn to_decimal_string(&self) -> String {
        let mut s = String::new();

        if self.negative {
            s.push('-');
        }

        // Ensure at least one integer digit
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
}

fuzz_target!(|input: DecimalInput| {
    let s = input.to_decimal_string();

    let decimal: Decimal = match s.parse() {
        Ok(d) => d,
        Err(_) => return, // e.g. all-zero input normalised to "0" edge cases
    };

    // to_plain_string must produce a re-parseable string
    let plain = decimal.to_plain_string();
    let reparsed: Decimal = plain
        .parse()
        .unwrap_or_else(|e| panic!("to_plain_string output {plain:?} failed to reparse: {e}"));

    assert_eq!(
        decimal.as_bytes(),
        reparsed.as_bytes(),
        "to_plain_string roundtrip mismatch: input={s:?} → plain={plain:?}"
    );

    // Encoded bytes must decode back to the same value
    let decoded = Decimal::from_bytes(decimal.as_bytes())
        .unwrap_or_else(|e| panic!("from_bytes failed on encoded bytes: {e}"));
    assert_eq!(
        decimal.as_bytes(),
        decoded.as_bytes(),
        "encode/decode mismatch for input={s:?}"
    );
});
