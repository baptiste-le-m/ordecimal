use thiserror::Error;

/// Errors that can occur during decoding of decimalInfinite format
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum DecodeError {
    #[error("Invalid sign bits: expected 00, 01, 10, or 11")]
    InvalidSign,

    #[error(
        "Invalid encoding: zero encoded with negative exponent (cannot start with 10011 or 00100)"
    )]
    ZeroWithNegativeExponent,

    #[error("Invalid tetrade: value {0} is outside valid range [0, 9]")]
    InvalidTetrade(u8),

    #[error("Invalid declet: value {0} is outside valid range [0, 999]")]
    InvalidDeclet(u16),

    #[error("Invalid significand: decoded value {0} is outside range [1, 10)")]
    InvalidSignificand(String),

    #[error("Unexpected end of input while decoding")]
    UnexpectedEndOfInput,

    #[error("Invalid gamma code: malformed exponent encoding")]
    InvalidGammaCode,

    #[error("Buffer too short: need at least {expected} bits, got {actual}")]
    BufferTooShort { expected: usize, actual: usize },

    #[error("Invalid special value encoding")]
    InvalidSpecialValue,
}

/// Errors that can occur during encoding
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum EncodeError {
    #[error("Invalid significand: must be in range [1, 10), got {0}")]
    SignificandOutOfRange(String),

    #[error("Invalid decimal format: {0}")]
    InvalidFormat(String),
}

/// Result type for decoding operations
pub type DecodeResult<T> = Result<T, DecodeError>;

/// Result type for encoding operations
pub type EncodeResult<T> = Result<T, EncodeError>;
