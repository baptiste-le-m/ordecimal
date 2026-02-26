//! Cross-validation tests ported from the C++ and Java implementations of
//! the decimalInfinite algorithm.
//!
//! Sources:
//! - C++ (original paper author): github.com/ghislainfourny/decimalgamma-cpp
//! - Java: github.com/RumbleDB/decimalgamma-java
//!
//! Note: The C++ implementation uses a slightly different complement for
//! negative multi-digit significands (`10 - first_digit` unconditionally),
//! while this implementation and the Java one follow the paper's definition
//! (true decimal subtraction `10.000... - significand`). For single-digit
//! significands, both approaches produce identical bit patterns.

use ordecimal::Decimal;

/// Convert bytes to a bit string like "10110001"
fn bits_string(bytes: &[u8]) -> String {
    bytes
        .iter()
        .flat_map(|b| {
            (0..8)
                .rev()
                .map(move |i| if (b >> i) & 1 == 1 { '1' } else { '0' })
        })
        .collect()
}

/// Convert a bit-string like "100100111" to byte encoding (padded with trailing zeros)
fn bits_to_bytes(bits: &str) -> Vec<u8> {
    let padded_len = bits.len().div_ceil(8) * 8;
    let mut bytes = Vec::with_capacity(padded_len / 8);
    let bits_iter = bits.chars().chain(std::iter::repeat('0'));
    for chunk in bits_iter.take(padded_len).collect::<Vec<_>>().chunks(8) {
        let mut byte = 0u8;
        for (i, &bit) in chunk.iter().enumerate() {
            if bit == '1' {
                byte |= 1 << (7 - i);
            }
        }
        bytes.push(byte);
    }
    bytes
}

/// Helper to assert encode-then-compare-bits and roundtrip
fn assert_encode_bits(input: &str, expected_bits: &str) {
    let value: Decimal = input.parse().unwrap();
    let expected = bits_to_bytes(expected_bits);
    assert_eq!(
        value.as_bytes(),
        &expected,
        "{} bit pattern mismatch:\n  got:      {}\n  expected: {}",
        input,
        bits_string(value.as_bytes()),
        expected_bits
    );
}

/// Helper to assert roundtrip: parse → encode → decode → to_plain_string matches
fn assert_roundtrip(input: &str) {
    let value: Decimal = input.parse().unwrap();
    let decoded = Decimal::from_bytes(value.as_bytes()).unwrap();
    assert_eq!(value, decoded, "roundtrip bytes mismatch for {}", input);

    // Also check plain-string roundtrip
    let plain = value.to_plain_string();
    let reparsed: Decimal = plain.parse().unwrap();
    assert_eq!(
        value.as_bytes(),
        reparsed.as_bytes(),
        "plain-string roundtrip mismatch for {}: got '{}' which re-encodes differently",
        input,
        plain
    );
}

// =============================================================================
// 1. Exact bit-pattern tests from C++ (positive numbers + single-digit negatives)
//    These match between all three implementations.
// =============================================================================

#[test]
fn test_cpp_exact_bits_zero() {
    assert_encode_bits("0", "10");
}

#[test]
fn test_cpp_exact_bits_small_positive_decimals() {
    assert_encode_bits("0.02", "10001110010");
    assert_encode_bits("0.2", "100100010");
}

#[test]
fn test_cpp_exact_bits_positive_integers_1_to_9() {
    // From C++ decimalgamma_test.cpp and paper Figure 10
    assert_encode_bits("1", "101000001");
    assert_encode_bits("2", "101000010");
    assert_encode_bits("3", "101000011");
    assert_encode_bits("4", "101000100");
    assert_encode_bits("5", "101000101");
    assert_encode_bits("6", "101000110");
    assert_encode_bits("7", "101000111");
    assert_encode_bits("8", "101001000");
    assert_encode_bits("9", "101001001");
}

#[test]
fn test_cpp_exact_bits_positive_integers_various() {
    assert_encode_bits("10", "101010001");
    assert_encode_bits("11", "1010100010001100100");
    assert_encode_bits("20", "101010010");
    assert_encode_bits("100", "10110000001");
    assert_encode_bits("200", "10110000010");
    assert_encode_bits("2000", "10110010010");
    assert_encode_bits("20000", "10110100010");
    assert_encode_bits("200000", "10110110010");
    assert_encode_bits("2000000", "1011100000010");
    assert_encode_bits("20000000", "1011100010010");
    assert_encode_bits("123456789", "1011100100001001110101010001101111101111010");
}

#[test]
fn test_cpp_exact_bits_negative_integers_single_digit() {
    // Single-digit significands: C++ and paper agree
    assert_encode_bits("-1", "000111001");
    assert_encode_bits("-2", "000111000");
    assert_encode_bits("-3", "000110111");
    assert_encode_bits("-4", "000110110");
    assert_encode_bits("-5", "000110101");
    assert_encode_bits("-6", "000110100");
    assert_encode_bits("-7", "000110011");
    assert_encode_bits("-8", "000110010");
    assert_encode_bits("-9", "000110001");
}

#[test]
fn test_cpp_exact_bits_negative_powers_of_ten() {
    // -10, -100, -1000 have single-digit significand (1), so all impls agree
    assert_encode_bits("-10", "000101001");
    assert_encode_bits("-100", "00001111001");
    assert_encode_bits("-1000", "00001101001");
}

// =============================================================================
// 2. Exact bit-pattern tests from Java (matches paper exactly)
//    These are the four worked examples from the paper.
// =============================================================================

#[test]
fn test_java_exact_bits_paper_examples() {
    // From Java DecimalGammaTest.java validateEncoding() and paper Figures 8-9
    assert_encode_bits("-103.2", "00001111000111100100");
    assert_encode_bits("-0.0405", "001100001011110110110");
    assert_encode_bits("0.707106", "100100111000100011100001111");
    assert_encode_bits("4005012345", "1011100110100000000010100000011000101011001");
}

#[test]
fn test_java_exact_bits_negative_large_integer() {
    // Java's encoding for -123456789 (differs from C++ in tetrade: 8 vs 9)
    // Java: "0000011011000101111110101101100000001101110"
    assert_encode_bits("-123456789", "0000011011000101111110101101100000001101110");
}

// =============================================================================
// 3. Roundtrip tests from C++ (all test vectors)
// =============================================================================

#[test]
fn test_roundtrip_cpp_vectors() {
    let test_cases = [
        "0",
        "0.02",
        "0.2",
        "1",
        "2",
        "3",
        "4",
        "5",
        "6",
        "7",
        "8",
        "9",
        "10",
        "11",
        "20",
        "100",
        "200",
        "2000",
        "20000",
        "200000",
        "2000000",
        "20000000",
        "123456789",
        "-1",
        "-2",
        "-3",
        "-4",
        "-5",
        "-6",
        "-7",
        "-8",
        "-9",
        "-10",
        "-100",
        "-1000",
        "-123456789",
    ];

    for case in &test_cases {
        assert_roundtrip(case);
    }
}

#[test]
fn test_roundtrip_paper_examples() {
    let test_cases = ["-103.2", "-0.0405", "0.707106", "4005012345"];
    for case in &test_cases {
        assert_roundtrip(case);
    }
}

// =============================================================================
// 4. Comparison tests from C++ (decimalgamma_test.cpp Comparison test)
// =============================================================================

#[test]
fn test_cpp_equality() {
    assert_eq!(
        "0".parse::<Decimal>().unwrap(),
        "0".parse::<Decimal>().unwrap()
    );
    assert_eq!(
        "1".parse::<Decimal>().unwrap(),
        "1".parse::<Decimal>().unwrap()
    );
    assert_eq!(
        "11234".parse::<Decimal>().unwrap(),
        "11234".parse::<Decimal>().unwrap()
    );
    assert_eq!(
        "-12341".parse::<Decimal>().unwrap(),
        "-12341".parse::<Decimal>().unwrap()
    );
    assert_eq!(
        "-12341.09237450928374509823745".parse::<Decimal>().unwrap(),
        "-12341.09237450928374509823745".parse::<Decimal>().unwrap()
    );

    // Very long number
    let long_num = "-12341234059823408923450923745092837450982374512341234059823408923450923745092837450982374";
    assert_eq!(
        long_num.parse::<Decimal>().unwrap(),
        long_num.parse::<Decimal>().unwrap()
    );

    // Non-equality
    assert_ne!(
        "1".parse::<Decimal>().unwrap(),
        "0".parse::<Decimal>().unwrap()
    );
    assert_ne!(
        "1".parse::<Decimal>().unwrap(),
        "-1".parse::<Decimal>().unwrap()
    );
}

#[test]
fn test_cpp_less_than() {
    let cases: &[(&str, &str)] = &[
        ("0", "1"),
        ("0", "0.1"),
        ("0", "12345"),
        ("-1", "0"),
        ("-123452", "0"),
        ("-0.023451", "0"),
        ("0.12345", "0.123456"),
    ];

    for (a, b) in cases {
        let da: Decimal = a.parse().unwrap();
        let db: Decimal = b.parse().unwrap();
        assert!(
            da < db,
            "{} < {} should be true, got {:?}",
            a,
            b,
            da.cmp(&db)
        );
        assert!(da <= db, "{} <= {} should be true", a, b);
        assert_eq!(
            da.cmp(&db),
            std::cmp::Ordering::Less,
            "{} should be strictly less than {}",
            a,
            b
        );
    }
}

#[test]
fn test_cpp_negative_comparisons() {
    // Negative vs positive with large numbers
    let neg: Decimal = "-0.12345".parse().unwrap();
    let pos: Decimal = "0.123420379485702394857023948572034958720349587234"
        .parse()
        .unwrap();
    assert!(neg < pos);
    assert!(neg <= pos);
    assert_eq!(neg.cmp(&pos), std::cmp::Ordering::Less);

    // Negative self-equality with <= and >=
    let neg2: Decimal = "-0.12345".parse().unwrap();
    assert!(neg >= neg2);
    assert!(neg <= neg2);
    assert_eq!(neg.cmp(&neg2), std::cmp::Ordering::Equal);
}

// =============================================================================
// 5. Java-inspired: integer neighbor ordering (exhaustive)
//    Ported from DecimalGammaTest.testIntegerNeighboursOrdered
// =============================================================================

#[test]
fn test_java_integer_neighbours_ordered() {
    // Test that for every pair of consecutive integers i, i+1, the encoding
    // of i is strictly less than the encoding of i+1.
    let range = 10_000; // Java uses 100_000, we use 10_000 for speed

    for i in -range..range {
        let a: Decimal = i.to_string().parse().unwrap();
        let b: Decimal = (i + 1).to_string().parse().unwrap();

        assert!(
            a < b,
            "order broken: {} should be < {}:\n  {}\n  {}",
            i,
            i + 1,
            bits_string(a.as_bytes()),
            bits_string(b.as_bytes())
        );
    }
}

// =============================================================================
// 6. Java-inspired: integer roundtrip (exhaustive)
//    Ported from DecimalGammaTest.testIntegerInverse
// =============================================================================

#[test]
fn test_java_integer_roundtrip() {
    let range = 10_000;

    for i in -range..range {
        let input = i.to_string();
        let value: Decimal = input.parse().unwrap();
        let plain = value.to_plain_string();

        assert_eq!(plain, input, "roundtrip failed for {}: got '{}'", i, plain);
    }
}

// =============================================================================
// 7. Java-inspired: fuzzy random ordering
//    Ported from DecimalGammaTest.testFuzzyOrdered
// =============================================================================

#[test]
fn test_fuzzy_ordering_lcg() {
    // Simple LCG PRNG for reproducibility (no dependency on rand crate)
    struct Lcg(u64);
    impl Lcg {
        fn next_u32(&mut self) -> u32 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (self.0 >> 33) as u32
        }
        fn next_f64(&mut self) -> f64 {
            (self.next_u32() as f64) / (u32::MAX as f64)
        }
        fn next_random(&mut self) -> f64 {
            let scale = (self.next_u32() % 10000) as f64;
            (self.next_f64() * 2.0 - 1.0) * scale
        }
    }

    let mut rng = Lcg(0x123);
    let iterations = 10_000;

    for _ in 0..iterations {
        let a = rng.next_random();
        let b = rng.next_random();

        // Skip pairs that are too close (floating-point string representation
        // might make them equal)
        if (a - b).abs() < 1e-10 {
            continue;
        }

        let da = Decimal::from(a);
        let db = Decimal::from(b);

        let expected = a.partial_cmp(&b).unwrap();
        let actual = da.cmp(&db);

        assert_eq!(
            actual,
            expected,
            "ordering mismatch for {} vs {}: expected {:?}, got {:?}\n  a: {}\n  b: {}",
            a,
            b,
            expected,
            actual,
            bits_string(da.as_bytes()),
            bits_string(db.as_bytes())
        );
    }
}

// =============================================================================
// 8. Java-inspired: fuzzy random roundtrip
//    Ported from DecimalGammaTest.testFuzzyInverse
// =============================================================================

#[test]
fn test_fuzzy_roundtrip_lcg() {
    struct Lcg(u64);
    impl Lcg {
        fn next_u32(&mut self) -> u32 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (self.0 >> 33) as u32
        }
        fn next_f64(&mut self) -> f64 {
            (self.next_u32() as f64) / (u32::MAX as f64)
        }
        fn next_random(&mut self) -> f64 {
            let scale = (self.next_u32() % 10000) as f64;
            (self.next_f64() * 2.0 - 1.0) * scale
        }
    }

    let mut rng = Lcg(0x456);
    let iterations = 10_000;

    for _ in 0..iterations {
        let val = rng.next_random();
        let decimal = Decimal::from(val);
        let decoded = Decimal::from_bytes(decimal.as_bytes()).unwrap();
        assert_eq!(
            decimal.as_bytes(),
            decoded.as_bytes(),
            "roundtrip failed for f64 value {}",
            val
        );
    }
}

// =============================================================================
// 9. Byte-level comparison order (from Java compareBytes)
//    Verifies that unsigned byte comparison gives the correct numeric order.
// =============================================================================

#[test]
fn test_byte_comparison_order() {
    let ordered = [
        "-1000000", "-100000", "-10000", "-1000", "-100", "-10", "-9", "-8", "-7", "-6", "-5",
        "-4", "-3", "-2", "-1", "-0.5", "-0.1", "-0.01", "-0.001", "0", "0.001", "0.01", "0.1",
        "0.5", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "100", "1000", "10000", "100000",
        "1000000",
    ];

    let encoded: Vec<(&str, Decimal)> = ordered
        .iter()
        .map(|s| (*s, s.parse::<Decimal>().unwrap()))
        .collect();

    for i in 1..encoded.len() {
        let (name_a, dec_a) = &encoded[i - 1];
        let (name_b, dec_b) = &encoded[i];

        // Decimal comparison
        assert!(
            dec_a < dec_b,
            "Decimal order broken: {} < {} failed",
            name_a,
            name_b
        );

        // Raw byte comparison (unsigned)
        assert!(
            dec_a.as_bytes() < dec_b.as_bytes(),
            "Byte order broken: {} < {} failed\n  {}\n  {}",
            name_a,
            name_b,
            bits_string(dec_a.as_bytes()),
            bits_string(dec_b.as_bytes())
        );
    }
}

// =============================================================================
// 10. Additional edge cases from C++ and Java
// =============================================================================

#[test]
fn test_very_long_number_roundtrip() {
    let long_pos =
        "12341234059823408923450923745092837450982374512341234059823408923450923745092837450982374";
    let long_neg = "-12341234059823408923450923745092837450982374512341234059823408923450923745092837450982374";

    assert_roundtrip(long_pos);
    assert_roundtrip(long_neg);

    // Order: negative < positive
    let dp: Decimal = long_pos.parse().unwrap();
    let dn: Decimal = long_neg.parse().unwrap();
    assert!(dn < dp);
}

#[test]
fn test_decimal_fractions_roundtrip() {
    let cases = [
        "0.1",
        "0.01",
        "0.001",
        "0.0001",
        "0.123456789",
        "0.000000001",
        "-0.1",
        "-0.01",
        "-0.001",
        "-0.123456789",
        "-0.000000001",
        "1.23",
        "12.345",
        "123.4567",
        "-1.23",
        "-12.345",
        "-123.4567",
    ];

    for case in &cases {
        assert_roundtrip(case);
    }
}

#[test]
fn test_powers_of_ten_ordering() {
    // Positive powers of ten
    let pos_powers: Vec<Decimal> = (0..20)
        .map(|e| format!("1{}", "0".repeat(e)).parse().unwrap())
        .collect();

    for i in 1..pos_powers.len() {
        assert!(
            pos_powers[i - 1] < pos_powers[i],
            "10^{} should be < 10^{}",
            i - 1,
            i
        );
    }

    // Negative powers of ten
    let neg_powers: Vec<Decimal> = (0..20)
        .map(|e| format!("-1{}", "0".repeat(e)).parse().unwrap())
        .collect();

    for i in 1..neg_powers.len() {
        assert!(
            neg_powers[i - 1] > neg_powers[i],
            "-10^{} should be > -10^{}",
            i - 1,
            i
        );
    }
}

#[test]
fn test_encoding_size_integers_1_to_9() {
    // Paper says integers 1-9 are encoded on 9 bits = 2 bytes (with padding)
    for i in 1..=9 {
        let value: Decimal = i.to_string().parse().unwrap();
        assert_eq!(
            value.as_bytes().len(),
            2,
            "Integer {} should encode to 2 bytes (9 bits), got {} bytes",
            i,
            value.as_bytes().len()
        );
    }
}
