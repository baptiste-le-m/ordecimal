# Changelog

## 0.4.0

### Breaking Changes

- **`From<Decimal>` for `BigDecimal` → `TryFrom`**, returning the new `BigDecimalConversionError::OutOfRange`. `BigDecimal` stores its scale as an `i64`, so an exponent below about −2^63 has no `BigDecimal` form; `BigDecimal::from(&"1e-9223372036854775808".parse()?)` used to panic. Above about 2^63 the conversion moves trailing zeros into the integer to keep the scale at `i64::MIN`, as long as the padded integer stays within 100 000 digits, so a value that came from a `BigDecimal` converts back unless that padding would exceed the budget. `From<BigDecimal> for Decimal` stays infallible
- **`from_bytes` rejects non-canonical encodings** with the new `DecodeError::NonCanonical`: non-zero padding bits, a trailing zero declet, or an extra trailing byte (zero padded with more zero bytes included). These decoded to a valid number under different bytes, and since `Eq`/`Ord`/`Hash` compare bytes they broke all three (`[A0, 81]` decoded to 1 but compared unequal to it and sorted above 1.001). Applies to serde's binary formats too. Bytes produced by this crate are always canonical, so stored keys are unaffected: encodings from every published version (0.1.0–0.3.1) were checked to decode
- **Non-canonical bytes are invalid in `from_bytes_unchecked` too**: a `Decimal` built from them now formats as `"<invalid>"`, fails conversions and panics in arithmetic, where 0.3 treated `[A0, 81]` as 1. Its documentation now states that the bytes must be a canonical encoding
- **Error enums are `#[non_exhaustive]`**: `DecodeError`, `EncodeError`, `IntegerConversionError`, `BigIntConversionError`, `RustDecimalConversionError`, `DecimalRsConversionError` and the new `BigDecimalConversionError`, so future variants are not breaking
- **`BigIntConversionError::TooLarge`**: `TryFrom<Decimal>` for `BigInt`/`BigUint` refuses integers longer than 100 000 digits (the same budget as arithmetic). `1e1000000000000` used to try to allocate ~1 TB, and `1e9223372036854775807` panicked with "capacity overflow"
- **`TryFrom<Decimal>` for `rust_decimal` and `decimal_rs` no longer rounds**: both crates' parsers round excess digits instead of failing, so 35- or 40-digit values came back silently rounded as `Ok`. They now return `OutOfRange` unless the value converts exactly
- **`FromStr` accepts exponents up to ±(`u64::MAX - 2`)**, the full encodable range, instead of ±`i64::MAX`
- **Removed `DecodeError::InvalidSign` and `EncodeError::SignificandOutOfRange`**, which nothing ever returned. The `DecodeError::BufferTooShort` message now says digits, which is what it counts
- **`bigdecimal` feature requires `bigdecimal` 0.4.3 or later**: the crate never built against 0.4.0–0.4.2 (no `to_scientific_notation`), but the manifest allowed them

### Fixes

- **Exponent overflow in `FromStr` ([#9](https://github.com/baptiste-le-m/ordecimal/issues/9))**: adding the digit exponent to the `e` exponent was unchecked, so `"10e9223372036854775807"` panicked in debug builds and wrapped in release ones, encoding a value that sorted below 1. The sum is now computed in `i128` and range-checked against the encodable range; beyond it parsing returns `EncodeError::InvalidFormat`
- **Malformed zero coefficients ([#10](https://github.com/baptiste-le-m/ordecimal/issues/10))**: the zero shortcut ran before the coefficient was validated, so `"0..0"`, `"0.0.0"`, `".e5"` and `"-.e1"` parsed as zero. They are now rejected; `"0."`, `".0"`, `"-0"` and `"0e5"` still parse as zero
- **String forms of every value parse back**: arithmetic on parseable values can produce exponents past `i64::MAX` (`9e9223372036854775807 + 9e9223372036854775807`), whose `to_scientific_string`/`to_plain_string` output `FromStr` used to reject — so serde JSON serialized them but could not deserialize them. Fixed by the wider exponent range above
- **`From<BigDecimal>` no longer panics at extreme scales**: scale `i64::MIN` is exponent 2^63, which the parser used to reject
- **`Display` for long significands**: values with more than 1534 significant digits overflowed the stack buffer and printed `<invalid>`; `Display` now falls back to a heap decode like `to_plain_string`
- **`Display` on malformed unchecked bytes**: a 64-bit gamma run reached a `u64` shift overflow in the decoder path behind `Display` (debug panic). Both decoder paths now share one sign/exponent reader that has the guard
- **Integer `TryFrom` past exponent 1000**: classification read `to_plain_string`, which switches to scientific form there, so `1e-1001` came back `OutOfRange` instead of `NotAnInteger` and `1.5e1001` came back `NotAnInteger` instead of `OutOfRange`. It now works from the decoded digits

### Tests

- Property tests that `from_bytes` accepts only canonical bytes, over arbitrary bytes and over valid encodings with padding bits set or junk appended
- `fuzz_decode` and `fuzz_parse` now check that accepted bytes and parsed values round-trip through `to_scientific_string` byte for byte; `fuzz_roundtrip` generates exponents over the full `i64` range
- Directed tests at both ends of the encodable exponent range, for parsing, string output and serde, and for the `rust_decimal`/`decimal_rs` exactness check at those types' own limits
- CI checks that the library builds on the declared MSRV (1.73)

## 0.3.1

### Features

- **Arithmetic on `Decimal`**: `Add`, `Sub`, `Neg`, `AddAssign`, `SubAssign` and `Sum`, in every operand-ownership combination (`a + b`, `&a + &b`, `a + &b`, `&a + b`). Computed with schoolbook base-10 digit arrays — no floating point, no rounding, no precision limit beyond the digit budget below
- **`Sum` for iterators**: `values.iter().sum::<Decimal>()` and `values.into_iter().sum::<Decimal>()`; an empty iterator sums to zero

### Fixes

- **`encode_from_parts` no longer wraps on extreme exponents**: the `exponent + 2` gamma offset was unchecked, so an exponent above `u64::MAX - 2` panicked in debug builds and silently produced undecodable bytes in release ones. It is now range-checked in both profiles. Only reachable for values decoded from stored bytes — `FromStr` caps exponents at `i64::MAX` — and, before arithmetic existed, only by carrying past the ceiling, which nothing could do

### Notes

- Aligning operands with distant exponents materializes trailing zeros (`1e100 + 1` needs 101 digits). Operations are capped at 100 000 aligned digits and **panic** beyond that, like integer overflow in `std`. Unreachable for practical values — DynamoDB numbers hold at most 38 digits — but `1e100000 + 1` will panic
- Results whose exponent would leave the encodable range of ±(`u64::MAX - 2`) also panic: a carry can push one place past the ceiling, and cancelling near-equal values one place below the floor, from operands that are themselves encodable
- Arithmetic results are ordinary encoded values: byte order still matches numeric order, `from_bytes` round-trips them, and they are byte-identical to the same value parsed from a string

### Tests

- Property tests cross-checking `Add`/`Sub`/`Neg`/`Sum` against `bigdecimal`, over both 64-bit and 200-digit mantissas, plus associativity, order preservation, and canonicality of results (a result must be byte-identical to the same value parsed from a string, since `Eq`/`Ord`/`Hash` compare raw bytes)
- Directed tests at both ends of the encodable exponent range and at the exact digit-budget boundary
- `fuzz_arithmetic` fuzz target now runs in CI alongside the parse/decode/roundtrip targets

## 0.3.0

### Features

- **`TryFrom<Decimal>` for primitive integers**: `i8`–`i128`, `u8`–`u128` — returns `IntegerConversionError` for fractional or out-of-range values
- **`rust_decimal` integration** (feature `rust_decimal`): `From<rust_decimal::Decimal> for Decimal` (infallible) and `TryFrom<Decimal> for rust_decimal::Decimal` (fallible — returns `RustDecimalConversionError::OutOfRange` beyond a 96-bit coefficient / scale 0–28)
- **`bigdecimal` integration** (feature `bigdecimal`): `From<BigDecimal> for Decimal` and `From<Decimal> for BigDecimal` — both infallible since both types support arbitrary precision
- **`decimal-rs` integration** (feature `decimal_rs`): `From<decimal_rs::Decimal> for Decimal` (infallible) and `TryFrom<Decimal> for decimal_rs::Decimal` (fallible — 38-digit / scale limits)
- **`num-bigint` integration** (feature `num_bigint`): `From<BigInt/BigUint> for Decimal` (infallible) and `TryFrom<Decimal> for BigInt/BigUint` (fallible — rejects fractional/negative values)

### Breaking Changes

- **Removed special values**: `Decimal::infinity()`, `neg_infinity()`, `nan()` constructors removed; `SpecialValue` enum removed entirely
- **Removed predicates**: `is_nan()`, `is_infinity()`, `is_pos_infinity()`, `is_neg_infinity()`, `is_finite()` removed — all values are now finite non-NaN
- **Removed `decode()` method**: use `to_plain_string()` or `to_scientific_string()` to inspect values
- **Removed public `DecodedDecimal`**: decoder types are now `pub(crate)` only
- **`From<f64>` → `TryFrom<f64>`**: rejects NaN and Infinity with `EncodeError`; same for `f32`
- **`FromStr` rejects `"inf"`, `"nan"` etc.**: returns `EncodeError::InvalidFormat`
- **`"-0"` normalizes to positive zero**: parsing `-0` no longer creates a distinct negative zero
- **`from_bytes` rejects old special-value bytes**: `0x00` (−∞), `0x40` (−0), `0xC0` (+∞), `0xE0` (NaN) now return `DecodeError::InvalidSpecialValue` — **data-breaking** for stored bytes
- **Simplified `PartialEq`/`Ord`/`Hash`**: direct byte comparison with no +0/−0 normalization (no longer needed)

### Fixes

- **`BigInt`/`BigUint` conversions with large exponents**: `TryFrom<Decimal>` used `to_plain_string()`, which switches to scientific notation past exponent 1000 — a form `num-bigint`'s `FromStr` cannot parse, so valid integers such as `1e5000` were rejected as `NotAnInteger`. Both conversions now decode the binary form via `decode_to_parts` and build the digit string directly

### Rationale

Special values (±∞, NaN, −0) added complexity to every code path and are not needed for the primary use case (database sort keys for finite decimal numbers). Removing them simplifies the API, reduces code size, and eliminates edge cases in ordering and hashing.

## 0.2.0

### Features

- **Serde support**: optional `serde` feature flag for `Serialize`/`Deserialize` on `Decimal`
- **`Hash` and `Default` traits**: `Decimal` now implements `Hash` and `Default`
- **Scientific notation parsing**: parse strings like `1.23e10` or `5E-3`

### Performance

- **Display / `to_plain_string`**: decode significand into stack buffer instead of heap-allocating a `Vec`; batch-write ASCII digits via `write_str`; format exponent with manual u64-to-ASCII
- **`From<u64>` / `From<i64>`**: use native u64 division instead of widening to u128

### Tests

- Cross-validation tests against C++ and Java reference implementations

### Benchmarks

- Side-by-side comparisons with `decimal-bytes` and `memcomparable`
- Scientific notation benchmarks and byte size comparisons

## 0.1.1

- Stack buffer for significand digits
- DynamoDB benchmark

## 0.1.0

- Initial release: order-preserving binary encoding for arbitrary-precision decimals
