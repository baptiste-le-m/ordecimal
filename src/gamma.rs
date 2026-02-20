use crate::error::DecodeError;
use crate::error::DecodeResult;

/// Utilities for working with bit sequences
pub struct BitWriter {
    bytes: Vec<u8>,
    bit_pos: usize, // Position within current byte (0-7)
}

impl BitWriter {
    #[must_use]
    pub fn new() -> Self {
        // Default capacity for typical use (sign + small exponent + small significand)
        Self::with_capacity(8)
    }

    /// Create a [`BitWriter`](Self) with pre-allocated capacity
    #[must_use]
    pub fn with_capacity(byte_capacity: usize) -> Self {
        Self {
            bytes: Vec::with_capacity(byte_capacity),
            bit_pos: 0,
        }
    }

    /// Write a single bit
    pub fn write_bit(&mut self, bit: bool) {
        if self.bit_pos == 0 {
            self.bytes.push(0);
        }

        if bit {
            let byte_idx = self.bytes.len() - 1;
            self.bytes[byte_idx] |= 1 << (7 - self.bit_pos);
        }

        self.bit_pos = (self.bit_pos + 1) % 8;
    }

    /// Write multiple bits from a u64 value.
    ///
    /// Packs bits into the current byte using shift+mask operations rather than
    /// looping one bit at a time. This matters because the two most frequent
    /// calls are tetrades (4 bits) and declets (10 bits).
    #[allow(clippy::cast_possible_truncation)]
    pub fn write_bits(&mut self, value: u64, num_bits: usize) {
        let mut remaining = num_bits;
        // Shift so the MSB of the value to write is at bit 7
        let mut val = value << (64 - num_bits);

        while remaining > 0 {
            if self.bit_pos == 0 {
                self.bytes.push(0);
            }

            let space = 8 - self.bit_pos; // free bits in current byte
            let write_count = remaining.min(space);

            // Extract `write_count` bits from the top of `val`
            let bits = (val >> (64 - write_count)) as u8;
            // Place them at the correct offset within the current byte
            let byte_idx = self.bytes.len() - 1;
            self.bytes[byte_idx] |= bits << (space - write_count);

            val <<= write_count;
            remaining -= write_count;
            self.bit_pos = (self.bit_pos + write_count) % 8;
        }
    }

    /// Get the resulting bytes
    #[must_use]
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Get current bytes (without consuming)
    #[cfg(test)]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

impl Default for BitWriter {
    fn default() -> Self {
        Self::new()
    }
}

pub struct BitReader<'a> {
    bytes: &'a [u8],
    bit_pos: usize, // Global bit position
}

impl<'a> BitReader<'a> {
    #[must_use]
    pub const fn new(bytes: &'a [u8]) -> Self {
        BitReader { bytes, bit_pos: 0 }
    }

    /// Read a single bit
    ///
    /// # Errors
    ///
    /// Returns [`DecodeError::UnexpectedEndOfInput`] if no bits remain.
    pub fn read_bit(&mut self) -> DecodeResult<bool> {
        let byte_idx = self.bit_pos / 8;
        let bit_offset = self.bit_pos % 8;

        if byte_idx >= self.bytes.len() {
            return Err(DecodeError::UnexpectedEndOfInput);
        }

        let bit = (self.bytes[byte_idx] >> (7 - bit_offset)) & 1 == 1;
        self.bit_pos += 1;

        Ok(bit)
    }

    /// Read multiple bits into a u64.
    ///
    /// Extracts bits in byte-aligned chunks using shift+mask rather than
    /// looping one bit at a time.
    ///
    /// # Errors
    ///
    /// Returns [`DecodeError::UnexpectedEndOfInput`] if fewer than `num_bits`
    /// remain, or [`DecodeError::InvalidGammaCode`] if `num_bits > 64`.
    pub fn read_bits(&mut self, num_bits: usize) -> DecodeResult<u64> {
        if num_bits > 64 {
            return Err(DecodeError::InvalidGammaCode);
        }

        let mut value = 0u64;
        let mut remaining = num_bits;

        while remaining > 0 {
            let byte_idx = self.bit_pos / 8;
            let bit_offset = self.bit_pos % 8;

            if byte_idx >= self.bytes.len() {
                return Err(DecodeError::UnexpectedEndOfInput);
            }

            let available = 8 - bit_offset; // bits left in this byte
            let read_count = remaining.min(available);

            // Extract `read_count` bits starting at `bit_offset`
            let shift = available - read_count;
            #[allow(clippy::cast_possible_truncation)]
            let mask = ((1u16 << read_count) - 1) as u8;
            let bits = (self.bytes[byte_idx] >> shift) & mask;

            value = (value << read_count) | u64::from(bits);
            self.bit_pos += read_count;
            remaining -= read_count;
        }

        Ok(value)
    }

    /// Peek at a bit without consuming it
    ///
    /// # Errors
    ///
    /// Returns [`DecodeError::UnexpectedEndOfInput`] if no bits remain.
    pub fn peek_bit(&self) -> DecodeResult<bool> {
        let byte_idx = self.bit_pos / 8;
        let bit_offset = self.bit_pos % 8;

        if byte_idx >= self.bytes.len() {
            return Err(DecodeError::UnexpectedEndOfInput);
        }

        Ok((self.bytes[byte_idx] >> (7 - bit_offset)) & 1 == 1)
    }

    /// Get current bit position
    #[must_use]
    pub const fn position(&self) -> usize {
        self.bit_pos
    }

    /// Check if there are more bits to read
    #[must_use]
    pub const fn has_bits(&self) -> bool {
        self.bit_pos < self.bytes.len() * 8
    }

    /// Get remaining bits count
    #[must_use]
    pub const fn remaining_bits(&self) -> usize {
        if self.bit_pos / 8 >= self.bytes.len() {
            0
        } else {
            self.bytes.len() * 8 - self.bit_pos
        }
    }

    /// Get the underlying bytes
    #[must_use]
    pub const fn bytes(&self) -> &[u8] {
        self.bytes
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_writer() {
        let mut writer = BitWriter::new();
        writer.write_bit(true);
        writer.write_bit(false);
        writer.write_bit(true);
        writer.write_bit(false);

        assert_eq!(writer.as_bytes()[0] & 0xF0, 0xA0); // 1010xxxx
    }

    #[test]
    fn test_bit_reader() {
        // Test reading bits
        let bytes = vec![0b1010_0101];
        let mut reader = BitReader::new(&bytes);

        assert!(reader.read_bit().unwrap()); // 1
        assert!(!reader.read_bit().unwrap()); // 0
        assert!(reader.read_bit().unwrap()); // 1
        assert!(!reader.read_bit().unwrap()); // 0
        assert!(!reader.read_bit().unwrap()); // 0
        assert!(reader.read_bit().unwrap()); // 1
        assert!(!reader.read_bit().unwrap()); // 0
        assert!(reader.read_bit().unwrap()); // 1
    }
}
