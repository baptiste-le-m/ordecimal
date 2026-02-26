use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use decimal_bytes::Decimal as DbDecimal;
use memcomparable::Decimal as McDecimal;
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

    // Scientific notation
    g.bench_function("ordecimal/from_str/sci_small", |b| {
        b.iter(|| black_box("1.5e3").parse::<Decimal>().unwrap());
    });
    g.bench_function("ordecimal/from_str/sci_neg_exp", |b| {
        b.iter(|| black_box("1.5e-3").parse::<Decimal>().unwrap());
    });
    g.bench_function("ordecimal/from_str/sci_dynamodb_min", |b| {
        b.iter(|| black_box("1E-130").parse::<Decimal>().unwrap());
    });
    g.bench_function("ordecimal/from_str/sci_dynamodb_max", |b| {
        b.iter(|| {
            black_box("9.9999999999999999999999999999999999999E+125")
                .parse::<Decimal>()
                .unwrap()
        });
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

    // Scientific notation
    g.bench_function("decimal_bytes/from_str/sci_small", |b| {
        b.iter(|| DbDecimal::from_str(black_box("1.5e3")).unwrap());
    });
    g.bench_function("decimal_bytes/from_str/sci_neg_exp", |b| {
        b.iter(|| DbDecimal::from_str(black_box("1.5e-3")).unwrap());
    });
    g.bench_function("decimal_bytes/from_str/sci_dynamodb_min", |b| {
        b.iter(|| DbDecimal::from_str(black_box("1E-130")).unwrap());
    });
    g.bench_function("decimal_bytes/from_str/sci_dynamodb_max", |b| {
        b.iter(|| {
            DbDecimal::from_str(black_box("9.9999999999999999999999999999999999999E+125")).unwrap()
        });
    });

    g.bench_function("decimal_bytes/special/nan", |b| {
        b.iter(DbDecimal::nan);
    });
    g.bench_function("decimal_bytes/special/zero", |b| {
        b.iter(|| DbDecimal::from_str("0").unwrap());
    });

    // -- memcomparable --
    // Note: memcomparable uses rust_decimal (~29 digits max) so large inputs are lossy.
    // We still benchmark them to show what happens.

    g.bench_function("memcomparable/from_str/small", |b| {
        b.iter(|| {
            McDecimal::from_str(black_box(small))
                .unwrap()
                .to_vec()
                .unwrap()
        });
    });
    g.bench_function("memcomparable/from_str/medium", |b| {
        b.iter(|| {
            McDecimal::from_str(black_box(medium))
                .unwrap()
                .to_vec()
                .unwrap()
        });
    });
    g.bench_function("memcomparable/from_str/dynamodb_38d_lossy", |b| {
        b.iter(|| {
            McDecimal::from_str(black_box(dynamodb.as_str()))
                .unwrap()
                .to_vec()
                .unwrap()
        });
    });

    g.bench_function("memcomparable/from_u64", |b| {
        b.iter(|| {
            McDecimal::Normalized(rust_decimal::Decimal::from(black_box(123_456_789_u64)))
                .to_vec()
                .unwrap()
        });
    });

    g.bench_function("memcomparable/special/nan", |b| {
        b.iter(|| McDecimal::NaN.to_vec().unwrap());
    });
    g.bench_function("memcomparable/special/zero", |b| {
        b.iter(|| McDecimal::ZERO.to_vec().unwrap());
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

    // ordecimal: decode() — structured decode
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

    // memcomparable: decode from bytes
    let mc_small_bytes = McDecimal::from_str("42").unwrap().to_vec().unwrap();
    let mc_medium_bytes = McDecimal::from_str("123.456789").unwrap().to_vec().unwrap();

    g.bench_function("memcomparable/decode/small", |b| {
        b.iter(|| McDecimal::from_slice(black_box(&mc_small_bytes)).unwrap());
    });
    g.bench_function("memcomparable/decode/medium", |b| {
        b.iter(|| McDecimal::from_slice(black_box(&mc_medium_bytes)).unwrap());
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

    // Display — memcomparable
    let mc_small = McDecimal::from_str("42").unwrap();
    let mc_medium = McDecimal::from_str("123.456789").unwrap();

    g.bench_with_input(
        BenchmarkId::new("memcomparable/display", "small"),
        &mc_small,
        |b, d| {
            b.iter(|| format!("{}", black_box(d)));
        },
    );
    g.bench_with_input(
        BenchmarkId::new("memcomparable/display", "medium"),
        &mc_medium,
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

    // memcomparable — compare as encoded bytes (the real use case)
    let mc_a_bytes = McDecimal::from_str("123.456789").unwrap().to_vec().unwrap();
    let mc_b_bytes = McDecimal::from_str("987.654321").unwrap().to_vec().unwrap();

    let mc_a_bytes_clone = mc_a_bytes.clone();
    g.bench_function("memcomparable/cmp_bytes/equal", |bench| {
        bench.iter(|| black_box(&mc_a_bytes).cmp(black_box(&mc_a_bytes_clone)));
    });
    g.bench_function("memcomparable/cmp_bytes/different_medium", |bench| {
        bench.iter(|| black_box(&mc_a_bytes).cmp(black_box(&mc_b_bytes)));
    });

    // memcomparable — compare as Decimal enum (derive Ord on rust_decimal)
    let mc_a = McDecimal::from_str("123.456789").unwrap();
    let mc_b = McDecimal::from_str("987.654321").unwrap();

    let mc_a_clone = mc_a;
    let mc_a2 = McDecimal::from_str("123.456789").unwrap();
    g.bench_function("memcomparable/cmp_enum/equal", |bench| {
        bench.iter(|| black_box(&mc_a2).cmp(black_box(&mc_a_clone)));
    });
    g.bench_function("memcomparable/cmp_enum/different_medium", |bench| {
        bench.iter(|| black_box(&mc_a2).cmp(black_box(&mc_b)));
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

    // memcomparable roundtrip: String -> McDecimal -> bytes -> McDecimal -> Display
    // Only for inputs that rust_decimal can handle without precision loss
    let mc_inputs = [("small", "42"), ("medium", "123.456789")];

    for (name, input) in &mc_inputs {
        g.bench_with_input(
            BenchmarkId::new("memcomparable/str_encode_decode_display", name),
            input,
            |b, &s| {
                b.iter(|| {
                    let d = McDecimal::from_str(black_box(s)).unwrap();
                    let encoded = d.to_vec().unwrap();
                    let decoded = McDecimal::from_slice(&encoded).unwrap();
                    format!("{decoded}")
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
