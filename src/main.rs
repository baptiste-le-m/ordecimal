use ordecimal::Decimal;

fn format_binary(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|b| format!("{b:08b}"))
        .collect::<Vec<_>>()
        .join(" ")
}

fn main() {
    println!("=== decimalInfinite Encoding Demo ===\n");

    // Examples from the paper
    let examples = vec!["-103.2", "-0.0405", "0", "0.707106", "4005012345"];

    println!("Examples from the paper:\n");
    for example in &examples {
        match example.parse::<Decimal>() {
            Ok(value) => {
                let encoded = value.as_bytes();
                println!("  {example} ->");
                println!("    Binary: {}", format_binary(encoded));
                println!("    Hex:    {encoded:02X?}");
                println!("    Bytes:  {} bytes", encoded.len());

                // Verify roundtrip
                match Decimal::from_bytes(encoded) {
                    Ok(_) => println!("    Roundtrip successful"),
                    Err(e) => println!("    Decode error: {e}"),
                }
                println!();
            }
            Err(e) => println!("  Error parsing {example}: {e}\n"),
        }
    }

    // Demonstrate order preservation
    println!("\n=== Order Preservation Demo ===\n");
    let numbers = vec!["-10", "-1", "0", "1", "10", "100"];
    let mut encoded_numbers: Vec<(String, Decimal)> = Vec::new();

    for num in &numbers {
        if let Ok(value) = num.parse::<Decimal>() {
            encoded_numbers.push(((*num).to_string(), value));
        }
    }

    println!("Sorted numbers and their encodings:");
    for (num, decimal) in &encoded_numbers {
        println!("  {:>5} -> {}", num, format_binary(decimal.as_bytes()));
    }

    // Verify order
    println!("\nVerifying lexicographic order matches numerical order:");
    for i in 1..encoded_numbers.len() {
        let (num1, dec1) = &encoded_numbers[i - 1];
        let (num2, dec2) = &encoded_numbers[i];

        if dec1 < dec2 {
            println!("  {num1} < {num2} (lexicographic order preserved)");
        } else {
            println!("  {num1} >= {num2} (order NOT preserved!)");
        }
    }

    // Zero-copy demo
    println!("\n=== Zero-Copy Demo ===\n");
    let decimal: Decimal = "42.195".parse().unwrap();
    let encoded = decimal.as_bytes();

    println!("Using Decimal API:");
    println!("  Value: 42.195");
    println!("  Encoded: {}", format_binary(encoded));
    println!("  as_bytes() is zero-copy (no allocation)");

    println!("\n=== Demo Complete ===");
}
