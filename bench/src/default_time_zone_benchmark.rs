use criterion::{criterion_group, criterion_main, Criterion};
use jiff::tz::TimeZone;
use std::sync::RwLock;
use std::time::Instant;

fn default_time_zone_benchmark(c: &mut Criterion) {
    c.bench_function("Get default TimeZone::system()", |b| {
        b.iter(|| {
            TimeZone::system();
        })
    });

    c.bench_function("Clone a TimeZone", |b| {
        let tz = TimeZone::system();
        b.iter(|| {
            let _ = tz.clone();
        })
    });

    c.bench_function("Read lock", |b| {
        let cache: RwLock<usize> = RwLock::new(0);
        b.iter(|| {
            let a = cache.read().unwrap();
        })
    });

    c.bench_function("Instant::now", |b| {
        b.iter(|| {
            let _ = Instant::now();
        })
    });
}

criterion_group!(benches, default_time_zone_benchmark);
criterion_main!(benches);
