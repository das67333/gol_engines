use criterion::{criterion_group, criterion_main, Criterion};
use std::sync::atomic::{AtomicU64, Ordering};

fn bench_atomics(c: &mut Criterion) {
    let mut group = c.benchmark_group("atomics");

    let a = AtomicU64::new(0);
    group.bench_function("load", |b| {
        b.iter(|| {
            let _ = a.load(Ordering::Relaxed);
        });
    });

    group.bench_function("cmpxchg", |b| {
        b.iter(|| {
            let _ = a.compare_exchange(0, 1, Ordering::Relaxed, Ordering::Relaxed);
        });
    });

    group.finish();
}

criterion_group!(benches, bench_atomics);
criterion_main!(benches);
