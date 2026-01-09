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

    group.bench_function("cmpxchg_fail", |b| {
        b.iter(|| {
            a.compare_exchange(1, 2, Ordering::Relaxed, Ordering::Relaxed)
                .unwrap_err();
        });
    });

    group.bench_function("cmpxchg_success", |b| {
        let mut value = 0;
        a.store(value, Ordering::Relaxed);
        b.iter(|| {
            a.compare_exchange(value, value + 1, Ordering::Relaxed, Ordering::Relaxed)
                .unwrap();
            value += 1;
        });
    });

    group.finish();
}

criterion_group!(benches, bench_atomics);
criterion_main!(benches);
