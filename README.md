# ordecimal

[![crates.io](https://img.shields.io/crates/v/ordecimal.svg)](https://crates.io/crates/ordecimal)
[![docs.rs](https://docs.rs/ordecimal/badge.svg)](https://docs.rs/ordecimal)

A Rust implementation of the [decimalInfinite](https://arxiv.org/abs/1506.01598) encoding
by Ghislain Fourny. It encodes arbitrary-precision decimals into variable-length byte strings
that preserve numerical ordering under lexicographic comparison — useful anywhere you need
decimal sort keys (database indexes, range queries, etc.).

```rust
use ordecimal::Decimal;

let a: Decimal = "-103.2".parse().unwrap();
let b: Decimal = "0.707106".parse().unwrap();
let c = Decimal::from(42u64);

// encoded bytes compare in the same order as the numbers
assert!(a < b);
assert!(b < c);

// zero-copy access to the encoded bytes
let key: &[u8] = c.as_bytes();

// round-trip back from bytes
let d = Decimal::from_bytes(key).unwrap();
assert_eq!(c, d);
```

## How it works

The encoding uses a STEM format (Sign, exponent sign (**T**), **E**xponent, **M**antissa):

| Field | Size | Description |
|-------|------|-------------|
| S | 2 bits | `00` = negative, `10` = +0 or positive |
| T | 1 bit | Exponent sign (flipped for negatives to preserve order) |
| E | variable | Exponent, modified Elias Gamma code (offset +2) |
| M | variable | Significand: first digit as 4-bit tetrade, then groups of 3 digits packed into 10-bit declets |

Negative significands use a 10 − *m* complement so that byte ordering is preserved
without any post-processing.

Example encodings from the paper:

| Decimal | Binary |
|---------|--------|
| 0 | `10` |
| 1 | `10 100 0001` |
| −103.2 | `00 001 11 1000 1111001000` |
| 0.707106 | `10 01 0 0111 0001000111 0000111100` |

## API

```rust
use ordecimal::Decimal;

// from strings (plain or scientific notation)
let d: Decimal = "123.456".parse().unwrap();
let d: Decimal = "6.022e23".parse().unwrap();

// from numeric types (no intermediate string, stack-only)
let d = Decimal::from(42u64);
let d = Decimal::from(-7i32);
let d = Decimal::try_from(3.14f64).unwrap();

// back to integers (fallible — rejects fractions and out-of-range)
let n: i64 = i64::try_from(&d).unwrap();

// zero
let _ = Decimal::zero();

// raw bytes
let bytes = d.as_bytes();        // &[u8], zero-copy
let owned = d.into_bytes();      // Vec<u8>
```

All `Decimal` values are finite, non-NaN numbers. Parsing `"inf"`, `"nan"`,
etc. returns an error, and `TryFrom<f64>` rejects NaN/Infinity.
Negative zero (`"-0"`) is normalized to positive zero.

`TryFrom<Decimal>` is implemented for all standard integer types (`i8`–`i128`,
`u8`–`u128`), returning an error if the value has a fractional part or exceeds
the target type's range.

## Serde

Enable the `serde` feature for `Serialize` / `Deserialize`:

```toml
ordecimal = { version = "0.3", features = ["serde"] }
```

Decimals serialize as their string representation in human-readable formats (JSON, TOML)
and as raw bytes in binary formats (bincode).

## Optional integrations

Each integration is behind a feature flag:

```toml
ordecimal = { version = "0.3", features = ["rust_decimal", "bigdecimal", "decimal_rs", "num_bigint"] }
```

### `rust_decimal`

Convert between `ordecimal::Decimal` and [`rust_decimal::Decimal`](https://docs.rs/rust_decimal)
(96-bit coefficient, 28-digit precision):

```rust
use ordecimal::Decimal;

// rust_decimal → ordecimal (infallible)
let rd = rust_decimal::Decimal::new(123_456, 3); // 123.456
let od = Decimal::from(rd);

// ordecimal → rust_decimal (fallible — rejects out-of-range values)
let rd_back = rust_decimal::Decimal::try_from(&od).unwrap();
```

### `bigdecimal`

Convert between `ordecimal::Decimal` and [`bigdecimal::BigDecimal`](https://docs.rs/bigdecimal).
Both types support arbitrary precision, so conversions are **infallible in both directions**:

```rust
use ordecimal::Decimal;

let bd = bigdecimal::BigDecimal::from(42);
let od = Decimal::from(bd);
let bd_back = bigdecimal::BigDecimal::from(&od);
```

### `decimal_rs`

Convert between `ordecimal::Decimal` and [`decimal_rs::Decimal`](https://docs.rs/decimal-rs)
(38-digit precision):

```rust
use ordecimal::Decimal;

let dr = decimal_rs::Decimal::from(42_i64);
let od = Decimal::from(dr);

// ordecimal → decimal_rs (fallible — rejects out-of-range values)
let dr_back = decimal_rs::Decimal::try_from(&od).unwrap();
```

### `num_bigint`

Convert between `ordecimal::Decimal` and [`num_bigint::BigInt`](https://docs.rs/num-bigint) /
`BigUint`:

```rust
use ordecimal::Decimal;
use num_bigint::BigInt;

let bi = BigInt::from(42);
let od = Decimal::from(bi);

// ordecimal → BigInt (fallible — rejects fractional values)
let bi_back = BigInt::try_from(&od).unwrap();
```

## Reference

> Ghislain Fourny. "decimalInfinite — All Decimals In Bits. No Loss. Same Order. Simple."
> arXiv:1506.01598, June 2015.

## License

MIT OR Apache-2.0
