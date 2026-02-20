use ordecimal::Decimal;

/// Helper: extract bits from encoded bytes as a string of '0' and '1'
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

/// Helper: convert a bit-string like "100100111" to the expected byte encoding
/// (padded with trailing zeros to a byte boundary, same as BitWriter output)
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

// =============================================================================
// Exact bit-pattern verification against the paper (Section 4, Figures 8-10)
// =============================================================================

#[test]
fn test_exact_bits_paper_example_1_neg_103_2() {
    // -103.2 = -1.032 × 10^2
    // s=-1, t=+1, e=2
    // S = 00
    // TE: e+2=4=100, N=3, negate=true (s≠t) → 001 11
    // M: 10-1.032 = 8.968 → tetrade 1000, declet 968 = 1111001000
    // Full: 00 001 11 1000 1111001000
    let expected = bits_to_bytes("00001111000111100100");
    let value: Decimal = "-103.2".parse().unwrap();
    assert_eq!(value.as_bytes(), &expected, "-103.2 bit pattern mismatch");
}

#[test]
fn test_exact_bits_paper_example_2_neg_0_0405() {
    // -0.0405 = -4.05 × 10^-2
    // s=-1, t=-1, e=2
    // S = 00
    // TE: e+2=4=100, N=3, negate=false (s==t) → 110 00
    // M: 10-4.05 = 5.95 → tetrade 0101, declet 950 = 1110110110
    // Full: 00 110 00 0101 1110110110
    let expected = bits_to_bytes("001100001011110110110");
    let value: Decimal = "-0.0405".parse().unwrap();
    assert_eq!(value.as_bytes(), &expected, "-0.0405 bit pattern mismatch");
}

#[test]
fn test_exact_bits_paper_example_3_pos_0_707106() {
    // 0.707106 = 7.07106 × 10^-1
    // s=+1, t=-1, e=1
    // S = 10
    // TE: e+2=3=11, N=2, negate=true (s≠t) → 01 0
    // M: tetrade 0111, declet 071=0001000111, declet 060=0000111100
    // Full: 10 01 0 0111 0001000111 0000111100
    let expected = bits_to_bytes("100100111000100011100001111");
    let value: Decimal = "0.707106".parse().unwrap();
    assert_eq!(value.as_bytes(), &expected, "0.707106 bit pattern mismatch");
}

#[test]
fn test_exact_bits_paper_example_4_pos_4005012345() {
    // 4005012345 = 4.005012345 × 10^9
    // s=+1, t=+1, e=9
    // S = 10
    // TE: e+2=11=1011, N=4, negate=false (s==t) → 1110 011
    // M: tetrade 0100, declets: 005=0000000101, 012=0000001100, 345=0101011001
    // Full: 10 1110 011 0100 0000000101 0000001100 0101011001
    let expected = bits_to_bytes("1011100110100000000010100000011000101011001");
    let value: Decimal = "4005012345".parse().unwrap();
    assert_eq!(
        value.as_bytes(),
        &expected,
        "4005012345 bit pattern mismatch"
    );
}

// =============================================================================
// Small integers from Figure 10
// =============================================================================

#[test]
fn test_exact_bits_small_integers() {
    // From Figure 10 of the paper
    // Integers 1-9: S(10) + TE(100) + tetrade = 9 bits each
    let cases = [
        ("1", "101000001"),  // 10 100 0001
        ("2", "101000010"),  // 10 100 0010
        ("3", "101000011"),  // 10 100 0011
        ("4", "101000100"),  // 10 100 0100
        ("5", "101000101"),  // 10 100 0101
        ("6", "101000110"),  // 10 100 0110
        ("7", "101000111"),  // 10 100 0111
        ("8", "101001000"),  // 10 100 1000
        ("9", "101001001"),  // 10 100 1001
        ("10", "101010001"), // 10 101 0001 (= 1.0 × 10^1)
    ];

    for (num, expected_bits) in &cases {
        let expected = bits_to_bytes(expected_bits);
        let value: Decimal = num.parse().unwrap();
        assert_eq!(
            value.as_bytes(),
            &expected,
            "integer {} bit pattern mismatch: got {}, expected {}",
            num,
            bits_string(value.as_bytes()),
            expected_bits
        );
    }
}

#[test]
fn test_exact_bits_small_negative_integers() {
    // From Figure 10 (negative side)
    // -1 through -9: S(00) + TE(011) + tetrade(complement) = 9 bits
    // complement: 10-N → tetrade
    let cases = [
        ("-1", "000111001"),  // 00 011 1001 (10-1=9)
        ("-2", "000111000"),  // 00 011 1000 (10-2=8)
        ("-3", "000110111"),  // 00 011 0111 (10-3=7)
        ("-4", "000110110"),  // 00 011 0110 (10-4=6)
        ("-5", "000110101"),  // 00 011 0101 (10-5=5)
        ("-6", "000110100"),  // 00 011 0100 (10-6=4)
        ("-7", "000110011"),  // 00 011 0011 (10-7=3)
        ("-8", "000110010"),  // 00 011 0010 (10-8=2)
        ("-9", "000110001"),  // 00 011 0001 (10-9=1)
        ("-10", "000101001"), // 00 010 1001 (10-1=9, exp=1)
    ];

    for (num, expected_bits) in &cases {
        let expected = bits_to_bytes(expected_bits);
        let value: Decimal = num.parse().unwrap();
        assert_eq!(
            value.as_bytes(),
            &expected,
            "integer {} bit pattern mismatch: got {}, expected {}",
            num,
            bits_string(value.as_bytes()),
            expected_bits
        );
    }
}

// =============================================================================
// Roundtrip tests
// =============================================================================

#[test]
fn test_roundtrip_paper_examples() {
    let test_cases = ["-103.2", "-0.0405", "0.707106", "4005012345"];

    for case in &test_cases {
        let original: Decimal = case.parse().unwrap();
        let encoded = original.as_bytes();
        let decoded = Decimal::from_bytes(encoded).unwrap();

        let orig_decoded = original.decode().unwrap();
        let dec_decoded = decoded.decode().unwrap();

        assert_eq!(
            orig_decoded.positive, dec_decoded.positive,
            "Sign mismatch for {}",
            case
        );
        assert_eq!(
            orig_decoded.exponent_positive, dec_decoded.exponent_positive,
            "Exp sign mismatch for {}",
            case
        );
        assert_eq!(
            orig_decoded.exponent, dec_decoded.exponent,
            "Exponent mismatch for {}",
            case
        );
        assert!(
            dec_decoded
                .significand
                .starts_with(&orig_decoded.significand),
            "Significand mismatch for {}: {:?} vs {:?}",
            case,
            orig_decoded.significand,
            dec_decoded.significand
        );
    }
}

// =============================================================================
// Order preservation
// =============================================================================

#[test]
fn test_order_preservation_detailed() {
    let test_numbers = [
        "-1000", "-100", "-10", "-5", "-1", "-0.5", "-0.1", "-0.01", "0", "0.01", "0.1", "0.5",
        "1", "5", "10", "100", "1000",
    ];

    let encoded_pairs: Vec<(&str, Decimal)> = test_numbers
        .iter()
        .map(|num| (*num, num.parse::<Decimal>().unwrap()))
        .collect();

    for i in 1..encoded_pairs.len() {
        let (num1, dec1) = &encoded_pairs[i - 1];
        let (num2, dec2) = &encoded_pairs[i];

        assert!(
            dec1 < dec2,
            "Order not preserved: {} < {} failed\n  {}\n  {}",
            num1,
            num2,
            bits_string(dec1.as_bytes()),
            bits_string(dec2.as_bytes())
        );
    }
}

// =============================================================================
// Special values (Figure 11)
// =============================================================================

#[test]
fn test_special_values_encoding() {
    // Figure 11 of the paper
    assert_eq!(
        Decimal::neg_infinity().as_bytes(),
        &[0b0000_0000],
        "-INF should be 00"
    );
    assert_eq!(
        Decimal::zero().as_bytes(),
        &[0b1000_0000],
        "+0 should be 10"
    );
    assert_eq!(
        Decimal::infinity().as_bytes(),
        &[0b1100_0000],
        "+INF should be 11"
    );
    assert_eq!(
        Decimal::nan().as_bytes(),
        &[0b1110_0000],
        "NaN should be 111"
    );
}

#[test]
fn test_special_values_ordering() {
    let neg_inf = Decimal::neg_infinity();
    let zero = Decimal::zero();
    let pos_inf = Decimal::infinity();

    assert!(neg_inf < zero);
    assert!(zero < pos_inf);
    assert!(neg_inf < pos_inf);

    // Regular numbers between specials
    let neg1: Decimal = "-1".parse().unwrap();
    let pos1: Decimal = "1".parse().unwrap();
    assert!(neg_inf < neg1);
    assert!(neg1 < zero);
    assert!(zero < pos1);
    assert!(pos1 < pos_inf);
}

#[test]
fn test_zero_encoding() {
    let zero: Decimal = "0".parse().unwrap();
    assert_eq!(
        zero.as_bytes(),
        &[0b1000_0000],
        "Zero should be encoded as 10 (padded)"
    );
}

#[test]
fn test_encoding_size_integers_1_to_9() {
    // Paper says integers 1-9 are encoded on 9 bits = 2 bytes (with padding)
    for i in 1..=9 {
        let value: Decimal = i.to_string().parse().unwrap();
        assert_eq!(
            value.as_bytes().len(),
            2,
            "Integer {} should encode to 2 bytes (9 bits)",
            i
        );
    }
}
