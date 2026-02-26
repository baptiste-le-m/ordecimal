//! Encoded byte-size comparison: ordecimal vs decimal-bytes.
//!
//! Prints a table showing how many bytes each library produces for the same
//! input values. Run with:
//!
//! ```sh
//! cargo bench --bench byte_sizes
//! ```

use decimal_bytes::Decimal as DbDecimal;
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
}

fn print_table(rows: &[Row]) {
    let max_input = rows
        .iter()
        .map(|r| r.input.len())
        .max()
        .unwrap_or(20)
        .max(20);

    println!(
        "{:<width$}  {:>15}  {:>15}  {:>10}",
        "input",
        "ordecimal",
        "decimal-bytes",
        "delta",
        width = max_input
    );
    println!(
        "{:-<width$}  {:->15}  {:->15}  {:->10}",
        "",
        "",
        "",
        "",
        width = max_input
    );
    for row in rows {
        let delta = row.ordecimal_bytes as isize - row.decimal_bytes_bytes as isize;
        let delta_str = if delta == 0 {
            "=".to_string()
        } else {
            format!("{:+}", delta)
        };
        println!(
            "{:<width$}  {:>12} B   {:>12} B   {:>10}",
            row.input,
            row.ordecimal_bytes,
            row.decimal_bytes_bytes,
            delta_str,
            width = max_input
        );
    }
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let mut rows = Vec::new();

    // Helper: measure both libraries for a string input
    let mut add_str = |label: &str, input: &str| {
        let ord = input.parse::<Decimal>().unwrap();
        let db = DbDecimal::from_str(input).unwrap();
        rows.push(Row {
            input: label.to_string(),
            ordecimal_bytes: ord.as_bytes().len(),
            decimal_bytes_bytes: db.as_bytes().len(),
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
    });
    rows.push(Row {
        input: "+infinity".to_string(),
        ordecimal_bytes: Decimal::infinity().as_bytes().len(),
        decimal_bytes_bytes: DbDecimal::infinity().as_bytes().len(),
    });
    rows.push(Row {
        input: "-infinity".to_string(),
        ordecimal_bytes: Decimal::neg_infinity().as_bytes().len(),
        decimal_bytes_bytes: DbDecimal::neg_infinity().as_bytes().len(),
    });
    rows.push(Row {
        input: "NaN".to_string(),
        ordecimal_bytes: Decimal::nan().as_bytes().len(),
        decimal_bytes_bytes: DbDecimal::nan().as_bytes().len(),
    });

    // Print
    println!();
    println!("Encoded byte size comparison: ordecimal vs decimal-bytes");
    println!("=========================================================");
    println!();
    print_table(&rows);
    println!();
}
