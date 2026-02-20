//! # ordecimal
//!
//! An implementation of the **decimalInfinite** binary encoding format for arbitrary-precision
//! decimal numbers with order-preserving properties.
//!
//! This encoding scheme, described in the paper "decimalInfinite: All Decimals In Bits.
//! No Loss. Same Order. Simple." by Ghislain Fourny, provides:
//!
//! - **Arbitrary precision**: No loss of information for any decimal number
//! - **Order preservation**: Lexicographic comparison of encoded bytes matches numerical comparison
//! - **Variable length**: Compact encoding that scales with the number's size
//! - **Simplicity**: Straightforward algorithm based on scientific notation (STEM format)
//!
//! ## Use Cases
//!
//! - Database indexing (sort keys, range queries)
//! - Storing decimals in binary formats while maintaining sort order
//! - Efficient range queries on decimal values
//!
//! ## Examples
//!
//! ```rust
//! use ordecimal::Decimal;
//!
//! // Parse a decimal from string (encodes immediately)
//! let value: Decimal = "123.456".parse().unwrap();
//!
//! // Zero-copy access to encoded bytes
//! let encoded = value.as_bytes();
//!
//! // Decode from bytes
//! let decoded = Decimal::from_bytes(encoded).unwrap();
//!
//! // Order preservation: lexicographic byte comparison = numerical comparison
//! let a: Decimal = "1.5".parse().unwrap();
//! let b: Decimal = "2.5".parse().unwrap();
//! assert!(a < b); // Direct comparison on Decimal works!
//! ```
//!
//! ## Format Overview
//!
//! The encoding uses a STEM format (Sign, exponent sign (T), Exponent, Mantissa/significand):
//!
//! - **S** (2 bits): Overall sign (00=negative, 10=positive, also handles special values)
//! - **T** (1 bit): Exponent sign
//! - **E** (variable): Exponent using modified Elias Gamma code
//! - **M** (variable): Significand using tetrades (4 bits) and declets (10 bits per 3 digits)

pub(crate) mod decimal;
pub(crate) mod decoder;
pub(crate) mod encoder;
pub(crate) mod error;
pub(crate) mod gamma;
pub(crate) mod significand;

// Re-export main types and functions
pub use decimal::{Decimal, SpecialValue};
pub use decoder::DecodedDecimal;
pub use error::{DecodeError, DecodeResult, EncodeError, EncodeResult};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_decode_roundtrip() {
        let value: Decimal = "123.456".parse().unwrap();
        let encoded = value.as_bytes();
        let decoded = Decimal::from_bytes(encoded).unwrap();

        // Compare the decimals
        assert_eq!(value, decoded);
    }

    #[test]
    fn test_order_preservation() {
        let numbers = vec![
            "-100", "-10", "-1.5", "-1", "-0.5", "0", "0.5", "1", "1.5", "10", "100",
        ];

        let decimals: Vec<Decimal> = numbers.iter().map(|s| s.parse().unwrap()).collect();

        // Check that encoded values are in the same order as input
        for i in 1..decimals.len() {
            assert!(
                decimals[i - 1] < decimals[i],
                "Order not preserved: {} < {} failed",
                numbers[i - 1],
                numbers[i]
            );
        }
    }

    #[test]
    fn test_special_values() {
        let special_values = vec![
            (Decimal::neg_infinity(), "negative infinity"),
            (Decimal::zero(), "zero"),
            (Decimal::infinity(), "positive infinity"),
            (Decimal::nan(), "NaN"),
        ];

        for (decimal, _name) in special_values {
            let encoded = decimal.as_bytes();
            let decoded = Decimal::from_bytes(encoded).unwrap();
            assert_eq!(decimal, decoded);
        }
    }

    #[test]
    fn test_zero_copy() {
        let decimal: Decimal = "42.0".parse().unwrap();
        let bytes1 = decimal.as_bytes();
        let bytes2 = decimal.as_bytes();

        // Same pointer = zero copy
        assert_eq!(bytes1.as_ptr(), bytes2.as_ptr());
    }
}
