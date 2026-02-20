# ordecimal

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
| S | 2 bits | `00` = negative, `01` = −0, `10` = +0 or positive, `11` = +∞ / NaN |
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
use ordecimal::{Decimal, DecodedDecimal};

// from strings
let d: Decimal = "123.456".parse().unwrap();

// from numeric types (no intermediate string, stack-only)
let d = Decimal::from(42u64);
let d = Decimal::from(-7i32);
let d = Decimal::from(3.14f64);

// special values
let _ = Decimal::infinity();
let _ = Decimal::neg_infinity();
let _ = Decimal::nan();
let _ = Decimal::zero();

// inspect components
if let Some(dec) = d.decode() {
    println!("{:?} × 10^{}", dec.significand, dec.exponent);
}

// raw bytes
let bytes = d.as_bytes();        // &[u8], zero-copy
let owned = d.into_bytes();      // Vec<u8>
```

`decode()` returns `None` for special values (±0, ±∞, NaN) — check with
`is_zero()`, `is_nan()`, `is_infinity()` instead.

### NaN ordering

Unlike IEEE 754, `Decimal` gives NaN a deterministic position in the total order:
NaN == NaN is true, and NaN sorts after everything else (including +∞). This is
intentional for sort-key use cases where every value needs a well-defined position.

## Reference

> Ghislain Fourny. "decimalInfinite — All Decimals In Bits. No Loss. Same Order. Simple."
> arXiv:1506.01598, June 2015.

## License

MIT OR Apache-2.0
