//! Allocation-counting benchmarks for ordecimal vs decimal-bytes.
//!
//! Measures the number of heap allocations and total bytes allocated for each
//! operation. Run with:
//!
//! ```sh
//! cargo bench --bench alloc
//! ```

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

use decimal_bytes::Decimal as DbDecimal;
use ordecimal::Decimal;
use std::str::FromStr;

// ---------------------------------------------------------------------------
// Counting allocator
// ---------------------------------------------------------------------------

struct CountingAllocator;

static ALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);
static ALLOC_BYTES: AtomicUsize = AtomicUsize::new(0);
static ACTIVE: AtomicUsize = AtomicUsize::new(0); // 0 = not counting

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        if ACTIVE.load(Ordering::Relaxed) != 0 {
            ALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
            ALLOC_BYTES.fetch_add(layout.size(), Ordering::Relaxed);
        }
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static A: CountingAllocator = CountingAllocator;

/// Reset counters, run `f`, return (allocs, bytes).
fn measure<F: FnOnce() -> T, T>(f: F) -> (T, usize, usize) {
    // Reset
    ALLOC_COUNT.store(0, Ordering::SeqCst);
    ALLOC_BYTES.store(0, Ordering::SeqCst);

    // Enable counting
    ACTIVE.store(1, Ordering::SeqCst);
    let result = f();
    ACTIVE.store(0, Ordering::SeqCst);

    let count = ALLOC_COUNT.load(Ordering::SeqCst);
    let bytes = ALLOC_BYTES.load(Ordering::SeqCst);
    (result, count, bytes)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_large_decimal(n: usize) -> String {
    let mut s = String::with_capacity(n + 1);
    for i in 0..n {
        if i == 3 {
            s.push('.');
        }
        s.push(char::from(b'0' + (((i % 9) + 1) as u8)));
    }
    s
}

struct Row {
    name: &'static str,
    lib: &'static str,
    allocs: usize,
    bytes: usize,
}

fn print_table(rows: &[Row]) {
    println!(
        "{:<45} {:<15} {:>8} {:>12}",
        "operation", "library", "allocs", "bytes"
    );
    println!("{:-<45} {:-<15} {:->8} {:->12}", "", "", "", "");
    for row in rows {
        println!(
            "{:<45} {:<15} {:>8} {:>12}",
            row.name, row.lib, row.allocs, row.bytes
        );
    }
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let mut rows = Vec::new();

    // -- Encoding ----------------------------------------------------------

    // FromStr small
    let (_, allocs, bytes) = measure(|| "42".parse::<Decimal>().unwrap());
    rows.push(Row {
        name: "FromStr small (\"42\")",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let (_, allocs, bytes) = measure(|| DbDecimal::from_str("42").unwrap());
    rows.push(Row {
        name: "FromStr small (\"42\")",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    // FromStr medium
    let (_, allocs, bytes) = measure(|| "123.456789".parse::<Decimal>().unwrap());
    rows.push(Row {
        name: "FromStr medium (\"123.456789\")",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let (_, allocs, bytes) = measure(|| DbDecimal::from_str("123.456789").unwrap());
    rows.push(Row {
        name: "FromStr medium (\"123.456789\")",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    // FromStr DynamoDB (38 digits)
    let dynamodb_str = make_large_decimal(38);
    let (_, allocs, bytes) = measure(|| dynamodb_str.as_str().parse::<Decimal>().unwrap());
    rows.push(Row {
        name: "FromStr DynamoDB (38 digits)",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let (_, allocs, bytes) = measure(|| DbDecimal::from_str(dynamodb_str.as_str()).unwrap());
    rows.push(Row {
        name: "FromStr DynamoDB (38 digits)",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    // FromStr large (100 digits)
    let large_str = make_large_decimal(100);
    let (_, allocs, bytes) = measure(|| large_str.as_str().parse::<Decimal>().unwrap());
    rows.push(Row {
        name: "FromStr large (100 digits)",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let (_, allocs, bytes) = measure(|| DbDecimal::from_str(large_str.as_str()).unwrap());
    rows.push(Row {
        name: "FromStr large (100 digits)",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    // FromStr very large (1000 digits)
    let very_large_str = make_large_decimal(1000);
    let (_, allocs, bytes) = measure(|| very_large_str.as_str().parse::<Decimal>().unwrap());
    rows.push(Row {
        name: "FromStr very large (1000 digits)",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let (_, allocs, bytes) = measure(|| DbDecimal::from_str(very_large_str.as_str()).unwrap());
    rows.push(Row {
        name: "FromStr very large (1000 digits)",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    // From<u64>
    let (_, allocs, bytes) = measure(|| Decimal::from(123_456_789_u64));
    rows.push(Row {
        name: "From<u64> (123456789)",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let (_, allocs, bytes) = measure(|| DbDecimal::from(123_456_789_u64));
    rows.push(Row {
        name: "From<u64> (123456789)",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    // From<f64>
    let (_, allocs, bytes) = measure(|| Decimal::from(123.456_789_f64));
    rows.push(Row {
        name: "From<f64> (123.456789)",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let (_, allocs, bytes) = measure(|| DbDecimal::try_from(123.456_789_f64).unwrap());
    rows.push(Row {
        name: "TryFrom<f64> (123.456789)",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    // Special values
    let (_, allocs, bytes) = measure(Decimal::nan);
    rows.push(Row {
        name: "nan()",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let (_, allocs, bytes) = measure(DbDecimal::nan);
    rows.push(Row {
        name: "nan()",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    let (_, allocs, bytes) = measure(Decimal::zero);
    rows.push(Row {
        name: "zero()",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let (_, allocs, bytes) = measure(|| DbDecimal::from_str("0").unwrap());
    rows.push(Row {
        name: "zero (from_str \"0\")",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    // -- Decoding ----------------------------------------------------------

    // ordecimal decode()
    let small: Decimal = "42".parse().unwrap();
    let (_, allocs, bytes) = measure(|| small.decode());
    rows.push(Row {
        name: "decode() small",
        lib: "ordecimal",
        allocs,
        bytes,
    });

    let medium: Decimal = "123.456789".parse().unwrap();
    let (_, allocs, bytes) = measure(|| medium.decode());
    rows.push(Row {
        name: "decode() medium",
        lib: "ordecimal",
        allocs,
        bytes,
    });

    let dynamodb: Decimal = dynamodb_str.parse().unwrap();
    let (_, allocs, bytes) = measure(|| dynamodb.decode());
    rows.push(Row {
        name: "decode() DynamoDB (38 digits)",
        lib: "ordecimal",
        allocs,
        bytes,
    });

    let large: Decimal = large_str.parse().unwrap();
    let (_, allocs, bytes) = measure(|| large.decode());
    rows.push(Row {
        name: "decode() large (100 digits)",
        lib: "ordecimal",
        allocs,
        bytes,
    });

    let very_large: Decimal = very_large_str.parse().unwrap();
    let (_, allocs, bytes) = measure(|| very_large.decode());
    rows.push(Row {
        name: "decode() very large (1000 digits)",
        lib: "ordecimal",
        allocs,
        bytes,
    });

    // -- Display -----------------------------------------------------------

    let (_, allocs, bytes) = measure(|| format!("{small}"));
    rows.push(Row {
        name: "Display small",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let db_small = DbDecimal::from_str("42").unwrap();
    let (_, allocs, bytes) = measure(|| format!("{db_small}"));
    rows.push(Row {
        name: "Display small",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    let (_, allocs, bytes) = measure(|| format!("{medium}"));
    rows.push(Row {
        name: "Display medium",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let db_medium = DbDecimal::from_str("123.456789").unwrap();
    let (_, allocs, bytes) = measure(|| format!("{db_medium}"));
    rows.push(Row {
        name: "Display medium",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    let (_, allocs, bytes) = measure(|| format!("{large}"));
    rows.push(Row {
        name: "Display large (100 digits)",
        lib: "ordecimal",
        allocs,
        bytes,
    });
    let db_large = DbDecimal::from_str(&large_str).unwrap();
    let (_, allocs, bytes) = measure(|| format!("{db_large}"));
    rows.push(Row {
        name: "Display large (100 digits)",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    // -- Comparison --------------------------------------------------------

    let a: Decimal = "123.456789".parse().unwrap();
    let b: Decimal = "987.654321".parse().unwrap();
    let (_, allocs, bytes) = measure(|| a.cmp(&b));
    rows.push(Row {
        name: "cmp (different)",
        lib: "ordecimal",
        allocs,
        bytes,
    });

    let db_a = DbDecimal::from_str("123.456789").unwrap();
    let db_b = DbDecimal::from_str("987.654321").unwrap();
    let (_, allocs, bytes) = measure(|| db_a.cmp(&db_b));
    rows.push(Row {
        name: "cmp (different)",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    let a_clone = a.clone();
    let (_, allocs, bytes) = measure(|| a.cmp(&a_clone));
    rows.push(Row {
        name: "cmp (equal)",
        lib: "ordecimal",
        allocs,
        bytes,
    });

    let db_a_clone = db_a.clone();
    let (_, allocs, bytes) = measure(|| db_a.cmp(&db_a_clone));
    rows.push(Row {
        name: "cmp (equal)",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    // -- Round-trip ---------------------------------------------------------

    let (_, allocs, bytes) = measure(|| {
        let d: Decimal = "123.456789".parse().unwrap();
        format!("{d}")
    });
    rows.push(Row {
        name: "roundtrip: str -> encode -> display",
        lib: "ordecimal",
        allocs,
        bytes,
    });

    let (_, allocs, bytes) = measure(|| {
        let d = DbDecimal::from_str("123.456789").unwrap();
        format!("{d}")
    });
    rows.push(Row {
        name: "roundtrip: str -> encode -> display",
        lib: "decimal-bytes",
        allocs,
        bytes,
    });

    let (_, allocs, bytes) = measure(|| {
        let d: Decimal = "123.456789".parse().unwrap();
        d.decode()
    });
    rows.push(Row {
        name: "roundtrip: str -> encode -> decode()",
        lib: "ordecimal",
        allocs,
        bytes,
    });

    // -- Print -------------------------------------------------------------

    println!();
    println!("ordecimal vs decimal-bytes allocation report");
    println!("=============================================");
    println!();
    print_table(&rows);
    println!();
}
