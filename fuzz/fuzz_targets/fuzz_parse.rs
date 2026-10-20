#![no_main]

use libfuzzer_sys::fuzz_target;
use ordecimal::Decimal;

fuzz_target!(|s: String| {
    // Feed arbitrary valid-UTF8 strings to the parser.
    // Must never panic — only Ok or Err.
    let Ok(decimal) = s.parse::<Decimal>() else {
        return;
    };

    // Whatever parses must encode to bytes the decoder accepts, and its
    // scientific form must parse back to the same bytes.
    Decimal::from_bytes(decimal.as_bytes())
        .unwrap_or_else(|e| panic!("from_bytes rejected the encoding of {s:?}: {e}"));
    let sci = decimal.to_scientific_string();
    let reparsed: Decimal = sci
        .parse()
        .unwrap_or_else(|e| panic!("to_scientific_string output {sci:?} failed to reparse: {e}"));
    assert_eq!(
        decimal.as_bytes(),
        reparsed.as_bytes(),
        "scientific roundtrip mismatch: input={s:?} → {sci:?}"
    );
});
