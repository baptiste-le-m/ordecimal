//! Optional Serde support for [`Decimal`].
//!
//! Enabled via the `serde` feature flag.
//!
//! - **Human-readable formats** (JSON, TOML): serializes as a plain decimal
//!   string (e.g. `"123.456"`) that round-trips through [`FromStr`](std::str::FromStr).
//! - **Binary formats** (bincode, postcard): serializes as raw bytes, preserving
//!   the order-preserving encoding directly.

use crate::Decimal;
use serde::de::{self, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

impl Serialize for Decimal {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if serializer.is_human_readable() {
            serializer.serialize_str(&self.to_plain_string())
        } else {
            serializer.serialize_bytes(self.as_bytes())
        }
    }
}

impl<'de> Deserialize<'de> for Decimal {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        if deserializer.is_human_readable() {
            deserializer.deserialize_str(DecimalStrVisitor)
        } else {
            deserializer.deserialize_byte_buf(DecimalBytesVisitor)
        }
    }
}

/// Visitor for human-readable formats (string representation).
struct DecimalStrVisitor;

impl<'de> Visitor<'de> for DecimalStrVisitor {
    type Value = Decimal;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a decimal number string")
    }

    fn visit_str<E: de::Error>(self, value: &str) -> Result<Decimal, E> {
        value.parse().map_err(de::Error::custom)
    }
}

/// Visitor for binary formats (raw encoded bytes).
struct DecimalBytesVisitor;

impl<'de> Visitor<'de> for DecimalBytesVisitor {
    type Value = Decimal;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("ordecimal-encoded bytes")
    }

    fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Decimal, E> {
        Decimal::from_bytes(value).map_err(de::Error::custom)
    }

    fn visit_byte_buf<E: de::Error>(self, value: Vec<u8>) -> Result<Decimal, E> {
        // Validate then take ownership — avoids a copy vs from_bytes
        Decimal::from_bytes(&value).map_err(de::Error::custom)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- JSON (human-readable) ------------------------------------------------

    #[test]
    fn test_json_roundtrip_positive() {
        let original: Decimal = "123.456".parse().unwrap();
        let json = serde_json::to_string(&original).unwrap();
        let restored: Decimal = serde_json::from_str(&json).unwrap();
        assert_eq!(original, restored);
    }

    #[test]
    fn test_json_roundtrip_negative() {
        let original: Decimal = "-42.5".parse().unwrap();
        let json = serde_json::to_string(&original).unwrap();
        let restored: Decimal = serde_json::from_str(&json).unwrap();
        assert_eq!(original, restored);
    }

    #[test]
    fn test_json_roundtrip_zero() {
        let original = Decimal::zero();
        let json = serde_json::to_string(&original).unwrap();
        assert_eq!(json, "\"0\"");
        let restored: Decimal = serde_json::from_str(&json).unwrap();
        assert_eq!(original, restored);
    }

    #[test]
    fn test_json_deserialize_from_plain_number_string() {
        // Users will likely provide plain number strings in JSON
        let d: Decimal = serde_json::from_str("\"99.99\"").unwrap();
        let expected: Decimal = "99.99".parse().unwrap();
        assert_eq!(d, expected);
    }

    #[test]
    fn test_json_rejects_special_values() {
        // These should fail since inf/nan are no longer valid
        assert!(serde_json::from_str::<Decimal>("\"inf\"").is_err());
        assert!(serde_json::from_str::<Decimal>("\"-inf\"").is_err());
        assert!(serde_json::from_str::<Decimal>("\"nan\"").is_err());
    }

    // -- bincode (binary) -----------------------------------------------------

    #[test]
    fn test_bincode_roundtrip_positive() {
        let original: Decimal = "123.456".parse().unwrap();
        let encoded = bincode::serialize(&original).unwrap();
        let restored: Decimal = bincode::deserialize(&encoded).unwrap();
        assert_eq!(original, restored);
    }

    #[test]
    fn test_bincode_roundtrip_negative() {
        let original: Decimal = "-42.5".parse().unwrap();
        let encoded = bincode::serialize(&original).unwrap();
        let restored: Decimal = bincode::deserialize(&encoded).unwrap();
        assert_eq!(original, restored);
    }

    #[test]
    fn test_bincode_roundtrip_zero() {
        let original = Decimal::zero();
        let encoded = bincode::serialize(&original).unwrap();
        let restored: Decimal = bincode::deserialize(&encoded).unwrap();
        assert_eq!(original, restored);
    }

    #[test]
    fn test_bincode_roundtrip_dynamodb_38d() {
        let mut s = String::with_capacity(39);
        for i in 0..38 {
            if i == 3 {
                s.push('.');
            }
            s.push(char::from(b'0' + (((i % 9) + 1) as u8)));
        }
        let original: Decimal = s.parse().unwrap();
        let encoded = bincode::serialize(&original).unwrap();
        let restored: Decimal = bincode::deserialize(&encoded).unwrap();
        assert_eq!(original, restored);
    }

    // -- Order preservation through bincode -----------------------------------

    #[test]
    fn test_bincode_preserves_order() {
        // Verify that bincode-serialized bytes maintain the same order.
        // bincode prepends a length prefix, so raw byte order isn't preserved,
        // but the deserialized values must still compare correctly.
        let values: Vec<Decimal> = vec![
            "-100".parse().unwrap(),
            "-1".parse().unwrap(),
            "0".parse::<Decimal>().unwrap(),
            "1".parse().unwrap(),
            "100".parse().unwrap(),
        ];

        let serialized: Vec<Vec<u8>> = values
            .iter()
            .map(|v| bincode::serialize(v).unwrap())
            .collect();

        let deserialized: Vec<Decimal> = serialized
            .iter()
            .map(|b| bincode::deserialize(b).unwrap())
            .collect();

        for i in 1..deserialized.len() {
            assert!(
                deserialized[i - 1] < deserialized[i],
                "order broken after bincode roundtrip: {:?} < {:?}",
                deserialized[i - 1],
                deserialized[i]
            );
        }
    }

    // -- Error handling -------------------------------------------------------

    #[test]
    fn test_json_deserialize_invalid_string() {
        let result: Result<Decimal, _> = serde_json::from_str("\"not_a_number\"");
        assert!(result.is_err());
    }

    #[test]
    fn test_bincode_deserialize_invalid_bytes() {
        // Empty bytes should fail validation
        let result: Result<Decimal, _> =
            bincode::deserialize(&[0u64.to_le_bytes().as_slice(), &[]].concat());
        assert!(result.is_err());
    }
}
