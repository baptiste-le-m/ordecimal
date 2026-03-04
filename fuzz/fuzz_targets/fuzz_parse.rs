#![no_main]

use libfuzzer_sys::fuzz_target;
use ordecimal::Decimal;

fuzz_target!(|s: String| {
    // Feed arbitrary valid-UTF8 strings to the parser.
    // Must never panic — only Ok or Err.
    let _ = s.parse::<Decimal>();
});
