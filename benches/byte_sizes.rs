//! Encoded byte-size comparison: ordecimal vs decimal-bytes vs memcomparable.
//!
//! Prints a table showing how many bytes each library produces for the same
//! input values. Run with:
//!
//! ```sh
//! cargo bench --bench byte_sizes
//! ```

use decimal_bytes::Decimal as DbDecimal;
use memcomparable::Decimal as McDecimal;
use ordecimal::Decimal;
use std::str::FromStr;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_large_decimal(n: usize) -> String {
    let mut s = String::with_capacity(n + 1);
    for i in 0..n {
        if i == 3 {
            s.push('.');
        }
        s.push(char::from(b'0' + (((i % 9) + 1) as u8))); // 1-9 repeating
    }
    s
}

struct Row {
    input: String,
    ordecimal_bytes: usize,
    decimal_bytes_bytes: usize,
    memcomparable_result: McResult,
}

fn print_table(rows: &[Row]) {
    let max_input = rows
        .iter()
        .map(|r| r.input.len())
        .max()
        .unwrap_or(20)
        .max(20);

    println!(
        "{:<width$}  {:>12}  {:>14}  {:>14}",
        "input",
        "ordecimal",
        "decimal-bytes",
        "memcomparable",
        width = max_input
    );
    println!(
        "{:-<width$}  {:->12}  {:->14}  {:->14}",
        "",
        "",
        "",
        "",
        width = max_input
    );
    for row in rows {
        let mc_str = match &row.memcomparable_result {
            McResult::Ok(n) => format!("{} B", n),
            McResult::ParseError => "parse err".to_string(),
            McResult::Lossy(n) => format!("{} B *LOSSY*", n),
        };
        println!(
            "{:<width$}  {:>9} B   {:>11} B   {:>14}",
            row.input,
            row.ordecimal_bytes,
            row.decimal_bytes_bytes,
            mc_str,
            width = max_input
        );
    }
}

enum McResult {
    Ok(usize),
    /// Parse failed (e.g. scientific notation not supported by rust_decimal)
    ParseError,
    /// Parsed but silently lost precision (rust_decimal max ~29 digits)
    Lossy(usize),
}

/// Try to encode a string value with memcomparable, detecting precision loss.
fn mc_byte_size(input: &str) -> McResult {
    let d: McDecimal = match input.parse() {
        Ok(d) => d,
        Err(_) => return McResult::ParseError,
    };
    let encoded = match d.to_vec() {
        Ok(v) => v,
        Err(_) => return McResult::ParseError,
    };

    // Detect precision loss: decode back and check if the round-trip is lossy.
    // rust_decimal silently truncates to ~29 significant digits.
    if let McDecimal::Normalized(rd) = d {
        let displayed = rd.to_string();
        // Strip signs and leading zeros for comparison
        let orig_digits: String = input.chars().filter(|c| c.is_ascii_digit()).collect();
        let rt_digits: String = displayed.chars().filter(|c| c.is_ascii_digit()).collect();
        let orig_trimmed = orig_digits.trim_start_matches('0').trim_end_matches('0');
        let rt_trimmed = rt_digits.trim_start_matches('0').trim_end_matches('0');
        if orig_trimmed.len() > rt_trimmed.len() + 1 {
            return McResult::Lossy(encoded.len());
        }
    }

    McResult::Ok(encoded.len())
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let mut rows = Vec::new();

    // Helper: measure all three libraries for a string input
    let mut add_str = |label: &str, input: &str| {
        let ord = input.parse::<Decimal>().unwrap();
        let db = DbDecimal::from_str(input).unwrap();
        let mc = mc_byte_size(input);
        rows.push(Row {
            input: label.to_string(),
            ordecimal_bytes: ord.as_bytes().len(),
            decimal_bytes_bytes: db.as_bytes().len(),
            memcomparable_result: mc,
        });
    };

    // Regular values — increasing size
    add_str("\"0\"", "0");
    add_str("\"1\"", "1");
    add_str("\"-1\"", "-1");
    add_str("\"42\"", "42");
    add_str("\"-42\"", "-42");
    add_str("\"123.456789\"", "123.456789");
    add_str("\"-123.456789\"", "-123.456789");
    add_str("\"0.000001\"", "0.000001");
    add_str("\"9999999999\"", "9999999999");

    // DynamoDB-relevant sizes
    let ddb38 = make_large_decimal(38);
    add_str("DynamoDB 38 digits", &ddb38);

    let neg_ddb38 = format!("-{}", &ddb38);
    add_str("DynamoDB 38 digits (neg)", &neg_ddb38);

    // Scientific notation (DynamoDB-style)
    add_str("sci: \"1.5e3\"", "1.5e3");
    add_str("sci: \"1.5e-3\"", "1.5e-3");
    add_str("sci: \"1E-130\" (DDB min)", "1E-130");
    add_str(
        "sci: \"9.99...E+125\" (DDB max)",
        "9.9999999999999999999999999999999999999E+125",
    );
    add_str("sci: \"-2.5e4\"", "-2.5e4");

    // Larger values (beyond DynamoDB)
    let d100 = make_large_decimal(100);
    add_str("100 digits", &d100);

    let d1000 = make_large_decimal(1000);
    add_str("1000 digits", &d1000);

    // Special values
    rows.push(Row {
        input: "zero".to_string(),
        ordecimal_bytes: Decimal::zero().as_bytes().len(),
        decimal_bytes_bytes: DbDecimal::from_str("0").unwrap().as_bytes().len(),
        memcomparable_result: McResult::Ok(McDecimal::ZERO.to_vec().unwrap().len()),
    });
    rows.push(Row {
        input: "+infinity".to_string(),
        ordecimal_bytes: Decimal::infinity().as_bytes().len(),
        decimal_bytes_bytes: DbDecimal::infinity().as_bytes().len(),
        memcomparable_result: McResult::Ok(McDecimal::Inf.to_vec().unwrap().len()),
    });
    rows.push(Row {
        input: "-infinity".to_string(),
        ordecimal_bytes: Decimal::neg_infinity().as_bytes().len(),
        decimal_bytes_bytes: DbDecimal::neg_infinity().as_bytes().len(),
        memcomparable_result: McResult::Ok(McDecimal::NegInf.to_vec().unwrap().len()),
    });
    rows.push(Row {
        input: "NaN".to_string(),
        ordecimal_bytes: Decimal::nan().as_bytes().len(),
        decimal_bytes_bytes: DbDecimal::nan().as_bytes().len(),
        memcomparable_result: McResult::Ok(McDecimal::NaN.to_vec().unwrap().len()),
    });

    // Print
    println!();
    println!("Encoded byte size comparison: ordecimal vs decimal-bytes vs memcomparable");
    println!("=========================================================================");
    println!();
    print_table(&rows);
    println!();
}
