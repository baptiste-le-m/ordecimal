#![no_main]

use libfuzzer_sys::fuzz_target;
use ordecimal::Decimal;

fuzz_target!(|data: &[u8]| {
    let s = match std::str::from_utf8(data) {
        Ok(s) => s,
        Err(_) => return,
    };

    let decimal = match s.parse::<Decimal>() {
        Ok(d) => d,
        Err(_) => return,
    };

    // to_plain_string must produce a re-parseable string
    let plain = decimal.to_plain_string();
    let reparsed: Decimal = plain
        .parse()
        .unwrap_or_else(|e| panic!("to_plain_string output {plain:?} failed to reparse: {e}"));

    assert_eq!(
        decimal.as_bytes(),
        reparsed.as_bytes(),
        "roundtrip mismatch: input={s:?} → plain={plain:?}"
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
