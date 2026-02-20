use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use ordecimal::Decimal;

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
    let large = make_large_decimal(100);
    let very_large = make_large_decimal(1000);

    g.bench_function("from_str/small", |b| {
        b.iter(|| black_box(small).parse::<Decimal>().unwrap());
    });
    g.bench_function("from_str/medium", |b| {
        b.iter(|| black_box(medium).parse::<Decimal>().unwrap());
    });
    g.bench_function("from_str/large_100d", |b| {
        b.iter(|| black_box(large.as_str()).parse::<Decimal>().unwrap());
    });
    g.bench_function("from_str/very_large_1000d", |b| {
        b.iter(|| black_box(very_large.as_str()).parse::<Decimal>().unwrap());
    });

    // From<u64>
    g.bench_function("from_u64", |b| {
        b.iter(|| Decimal::from(black_box(123_456_789_u64)));
    });

    // From<f64>
    g.bench_function("from_f64", |b| {
        b.iter(|| Decimal::from(black_box(123.456_789_f64)));
    });

    // Special values
    g.bench_function("special/nan", |b| {
        b.iter(Decimal::nan);
    });
    g.bench_function("special/zero", |b| {
        b.iter(Decimal::zero);
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
    let large: Decimal = make_large_decimal(100).parse().unwrap();
    let very_large: Decimal = make_large_decimal(1000).parse().unwrap();

    // decode() — structured decode
    g.bench_function("decode/small", |b| {
        b.iter(|| black_box(&small).decode());
    });
    g.bench_function("decode/medium", |b| {
        b.iter(|| black_box(&medium).decode());
    });
    g.bench_function("decode/large_100d", |b| {
        b.iter(|| black_box(&large).decode());
    });
    g.bench_function("decode/very_large_1000d", |b| {
        b.iter(|| black_box(&very_large).decode());
    });

    // Display — format back to string
    g.bench_with_input(BenchmarkId::new("display", "small"), &small, |b, d| {
        b.iter(|| format!("{}", black_box(d)));
    });
    g.bench_with_input(BenchmarkId::new("display", "medium"), &medium, |b, d| {
        b.iter(|| format!("{}", black_box(d)));
    });
    g.bench_with_input(BenchmarkId::new("display", "large_100d"), &large, |b, d| {
        b.iter(|| format!("{}", black_box(d)));
    });
    g.bench_with_input(
        BenchmarkId::new("display", "very_large_1000d"),
        &very_large,
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

    let a: Decimal = "123.456789".parse().unwrap();
    let b: Decimal = "987.654321".parse().unwrap();
    let a_large: Decimal = make_large_decimal(100).parse().unwrap();
    let b_large: Decimal = make_large_decimal(100).replace('1', "2").parse().unwrap();

    // Equal values
    let a_clone = a.clone();
    g.bench_function("cmp/equal", |bench| {
        bench.iter(|| black_box(&a).cmp(black_box(&a_clone)));
    });

    // Different values — medium
    g.bench_function("cmp/different_medium", |bench| {
        bench.iter(|| black_box(&a).cmp(black_box(&b)));
    });

    // Different values — large (100 digits)
    g.bench_function("cmp/different_large", |bench| {
        bench.iter(|| black_box(&a_large).cmp(black_box(&b_large)));
    });

    g.finish();
}

// ---------------------------------------------------------------------------
// Round-trip benchmarks
// ---------------------------------------------------------------------------

fn bench_roundtrip(c: &mut Criterion) {
    let mut g = c.benchmark_group("roundtrip");

    let inputs = [("small", "42"), ("medium", "123.456789")];

    for (name, input) in &inputs {
        // String -> Decimal -> Display -> String
        g.bench_with_input(
            BenchmarkId::new("str_encode_display", name),
            input,
            |b, &s| {
                b.iter(|| {
                    let d: Decimal = black_box(s).parse().unwrap();
                    format!("{d}")
                });
            },
        );

        // String -> Decimal -> decode()
        g.bench_with_input(
            BenchmarkId::new("str_encode_decode", name),
            input,
            |b, &s| {
                b.iter(|| {
                    let d: Decimal = black_box(s).parse().unwrap();
                    d.decode()
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
