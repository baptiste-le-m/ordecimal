# Changelog

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
