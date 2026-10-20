#![no_main]

use libfuzzer_sys::fuzz_target;
use ordecimal::Decimal;

fuzz_target!(|data: &[u8]| {
    // Feed arbitrary bytes to the decoder.
    // Must never panic — only Ok or Err.
    let Ok(decimal) = Decimal::from_bytes(data) else {
        return;
    };

    // Eq/Ord/Hash compare raw bytes, so accepted bytes must be exactly what
    // parsing the value produces — a second byte form would compare unequal
    // to it and could sort out of place.
    let sci = decimal.to_scientific_string();
    let reparsed: Decimal = sci
        .parse()
        .unwrap_or_else(|e| panic!("to_scientific_string output {sci:?} failed to reparse: {e}"));
    assert_eq!(
        reparsed.as_bytes(),
        data,
        "from_bytes accepted non-canonical bytes for {sci:?}"
    );
});
