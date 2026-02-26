use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use decimal_bytes::Decimal as DbDecimal;
use ordecimal::Decimal;
use std::str::FromStr;

// ---------------------------------------------------------------------------
// Input generation
// ---------------------------------------------------------------------------

/// Build a decimal string of `n` significant digits: "1234567890123..." with a
/// decimal point after the third digit.
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

// ---------------------------------------------------------------------------
// Encoding benchmarks
// ---------------------------------------------------------------------------

fn bench_encode(c: &mut Criterion) {
    let mut g = c.benchmark_group("encode");

    // FromStr — varying sizes
    let small = "42";
    let medium = "123.456789";
    let dynamodb = make_large_decimal(38); // DynamoDB number precision limit
    let large = make_large_decimal(100);
    let very_large = make_large_decimal(1000);

    // -- ordecimal --

    g.bench_function("ordecimal/from_str/small", |b| {
        b.iter(|| black_box(small).parse::<Decimal>().unwrap());
    });
    g.bench_function("ordecimal/from_str/medium", |b| {
        b.iter(|| black_box(medium).parse::<Decimal>().unwrap());
    });
    g.bench_function("ordecimal/from_str/dynamodb_38d", |b| {
        b.iter(|| black_box(dynamodb.as_str()).parse::<Decimal>().unwrap());
    });
    g.bench_function("ordecimal/from_str/large_100d", |b| {
        b.iter(|| black_box(large.as_str()).parse::<Decimal>().unwrap());
    });
    g.bench_function("ordecimal/from_str/very_large_1000d", |b| {
        b.iter(|| black_box(very_large.as_str()).parse::<Decimal>().unwrap());
    });

    g.bench_function("ordecimal/from_u64", |b| {
        b.iter(|| Decimal::from(black_box(123_456_789_u64)));
    });

    g.bench_function("ordecimal/from_f64", |b| {
        b.iter(|| Decimal::from(black_box(123.456_789_f64)));
    });

    g.bench_function("ordecimal/special/nan", |b| {
        b.iter(Decimal::nan);
    });
    g.bench_function("ordecimal/special/zero", |b| {
        b.iter(Decimal::zero);
    });

    // -- decimal-bytes --

    g.bench_function("decimal_bytes/from_str/small", |b| {
        b.iter(|| DbDecimal::from_str(black_box(small)).unwrap());
    });
    g.bench_function("decimal_bytes/from_str/medium", |b| {
        b.iter(|| DbDecimal::from_str(black_box(medium)).unwrap());
    });
    g.bench_function("decimal_bytes/from_str/dynamodb_38d", |b| {
        b.iter(|| DbDecimal::from_str(black_box(dynamodb.as_str())).unwrap());
    });
    g.bench_function("decimal_bytes/from_str/large_100d", |b| {
        b.iter(|| DbDecimal::from_str(black_box(large.as_str())).unwrap());
    });
    g.bench_function("decimal_bytes/from_str/very_large_1000d", |b| {
        b.iter(|| DbDecimal::from_str(black_box(very_large.as_str())).unwrap());
    });

    g.bench_function("decimal_bytes/from_u64", |b| {
        b.iter(|| DbDecimal::from(black_box(123_456_789_u64)));
    });

    g.bench_function("decimal_bytes/try_from_f64", |b| {
        b.iter(|| DbDecimal::try_from(black_box(123.456_789_f64)).unwrap());
    });

    g.bench_function("decimal_bytes/special/nan", |b| {
        b.iter(DbDecimal::nan);
    });
    g.bench_function("decimal_bytes/special/zero", |b| {
        b.iter(|| DbDecimal::from_str("0").unwrap());
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// Decoding benchmarks
// ---------------------------------------------------------------------------

fn bench_decode(c: &mut Criterion) {
    let mut g = c.benchmark_group("decode");

    let small: Decimal = "42".parse().unwrap();
    let medium: Decimal = "123.456789".parse().unwrap();
    let dynamodb: Decimal = make_large_decimal(38).parse().unwrap();
    let large: Decimal = make_large_decimal(100).parse().unwrap();
    let very_large: Decimal = make_large_decimal(1000).parse().unwrap();

    // ordecimal: decode() — structured decode (no decimal-bytes equivalent)
    g.bench_function("ordecimal/decode/small", |b| {
        b.iter(|| black_box(&small).decode());
    });
    g.bench_function("ordecimal/decode/medium", |b| {
        b.iter(|| black_box(&medium).decode());
    });
    g.bench_function("ordecimal/decode/dynamodb_38d", |b| {
        b.iter(|| black_box(&dynamodb).decode());
    });
    g.bench_function("ordecimal/decode/large_100d", |b| {
        b.iter(|| black_box(&large).decode());
    });
    g.bench_function("ordecimal/decode/very_large_1000d", |b| {
        b.iter(|| black_box(&very_large).decode());
    });

    // Display — ordecimal
    g.bench_with_input(
        BenchmarkId::new("ordecimal/display", "small"),
        &small,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );
    g.bench_with_input(
        BenchmarkId::new("ordecimal/display", "medium"),
        &medium,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );
    g.bench_with_input(
        BenchmarkId::new("ordecimal/display", "dynamodb_38d"),
        &dynamodb,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );
    g.bench_with_input(
        BenchmarkId::new("ordecimal/display", "large_100d"),
        &large,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );
    g.bench_with_input(
        BenchmarkId::new("ordecimal/display", "very_large_1000d"),
        &very_large,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );

    // Display — decimal-bytes
    let db_small = DbDecimal::from_str("42").unwrap();
    let db_medium = DbDecimal::from_str("123.456789").unwrap();
    let db_dynamodb = DbDecimal::from_str(&make_large_decimal(38)).unwrap();
    let db_large = DbDecimal::from_str(&make_large_decimal(100)).unwrap();
    let db_very_large = DbDecimal::from_str(&make_large_decimal(1000)).unwrap();

    g.bench_with_input(
        BenchmarkId::new("decimal_bytes/display", "small"),
        &db_small,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );
    g.bench_with_input(
        BenchmarkId::new("decimal_bytes/display", "medium"),
        &db_medium,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );
    g.bench_with_input(
        BenchmarkId::new("decimal_bytes/display", "dynamodb_38d"),
        &db_dynamodb,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );
    g.bench_with_input(
        BenchmarkId::new("decimal_bytes/display", "large_100d"),
        &db_large,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );
    g.bench_with_input(
        BenchmarkId::new("decimal_bytes/display", "very_large_1000d"),
        &db_very_large,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );

    g.finish();
}

// ---------------------------------------------------------------------------
// Comparison benchmarks
// ---------------------------------------------------------------------------

fn bench_compare(c: &mut Criterion) {
    let mut g = c.benchmark_group("compare");

    // ordecimal
    let a: Decimal = "123.456789".parse().unwrap();
    let b: Decimal = "987.654321".parse().unwrap();
    let a_large: Decimal = make_large_decimal(100).parse().unwrap();
    let b_large: Decimal = make_large_decimal(100).replace('1', "2").parse().unwrap();

    let a_clone = a.clone();
    g.bench_function("ordecimal/cmp/equal", |bench| {
        bench.iter(|| black_box(&a).cmp(black_box(&a_clone)));
    });
    g.bench_function("ordecimal/cmp/different_medium", |bench| {
        bench.iter(|| black_box(&a).cmp(black_box(&b)));
    });
    g.bench_function("ordecimal/cmp/different_large", |bench| {
        bench.iter(|| black_box(&a_large).cmp(black_box(&b_large)));
    });

    // decimal-bytes
    let db_a = DbDecimal::from_str("123.456789").unwrap();
    let db_b = DbDecimal::from_str("987.654321").unwrap();
    let db_a_large = DbDecimal::from_str(&make_large_decimal(100)).unwrap();
    let db_b_large = DbDecimal::from_str(&make_large_decimal(100).replace('1', "2")).unwrap();

    let db_a_clone = db_a.clone();
    g.bench_function("decimal_bytes/cmp/equal", |bench| {
        bench.iter(|| black_box(&db_a).cmp(black_box(&db_a_clone)));
    });
    g.bench_function("decimal_bytes/cmp/different_medium", |bench| {
        bench.iter(|| black_box(&db_a).cmp(black_box(&db_b)));
    });
    g.bench_function("decimal_bytes/cmp/different_large", |bench| {
        bench.iter(|| black_box(&db_a_large).cmp(black_box(&db_b_large)));
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// Round-trip benchmarks
// ---------------------------------------------------------------------------

fn bench_roundtrip(c: &mut Criterion) {
    let mut g = c.benchmark_group("roundtrip");

    let dynamodb_rt = make_large_decimal(38);
    let inputs = [
        ("small", "42"),
        ("medium", "123.456789"),
        ("dynamodb_38d", dynamodb_rt.as_str()),
    ];

    for (name, input) in &inputs {
        // ordecimal: String -> Decimal -> Display -> String
        g.bench_with_input(
            BenchmarkId::new("ordecimal/str_encode_display", name),
            input,
            |b, &s| {
                b.iter(|| {
                    let d: Decimal = black_box(s).parse().unwrap();
                    format!("{d}")
                });
            },
        );

        // ordecimal: String -> Decimal -> decode()
        g.bench_with_input(
            BenchmarkId::new("ordecimal/str_encode_decode", name),
            input,
            |b, &s| {
                b.iter(|| {
                    let d: Decimal = black_box(s).parse().unwrap();
                    d.decode()
                });
            },
        );

        // decimal-bytes: String -> Decimal -> Display -> String
        g.bench_with_input(
            BenchmarkId::new("decimal_bytes/str_encode_display", name),
            input,
            |b, &s| {
                b.iter(|| {
                    let d = DbDecimal::from_str(black_box(s)).unwrap();
                    format!("{d}")
                });
            },
        );
    }

    g.finish();
}

// ---------------------------------------------------------------------------
// Criterion harness
// ---------------------------------------------------------------------------

criterion_group!(
    benches,
    bench_encode,
    bench_decode,
    bench_compare,
    bench_roundtrip
);
criterion_main!(benches);
