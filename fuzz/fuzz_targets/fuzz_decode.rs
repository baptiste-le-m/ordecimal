#![no_main]

use libfuzzer_sys::fuzz_target;
use ordecimal::Decimal;

fuzz_target!(|data: &[u8]| {
    // Feed arbitrary bytes to the decoder.
    // Must never panic — only Ok or Err.
    let _ = Decimal::from_bytes(data);
});
