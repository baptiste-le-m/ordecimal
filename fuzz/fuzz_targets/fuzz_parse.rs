#![no_main]

use libfuzzer_sys::fuzz_target;
use ordecimal::Decimal;

fuzz_target!(|data: &[u8]| {
    // Feed arbitrary bytes as UTF-8 to the parser.
    // Must never panic — only Ok or Err.
    if let Ok(s) = std::str::from_utf8(data) {
        let _ = s.parse::<Decimal>();
    }
});
