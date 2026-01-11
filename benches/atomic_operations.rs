use criterion::{criterion_group, criterion_main, Criterion};
use std::sync::{self, atomic::{AtomicU64, Ordering}};

fn bench_atomics(c: &mut Criterion) {
    let mut group = c.benchmark_group("atomics");
    const ORDERING: Ordering = Ordering::SeqCst;

    group.bench_function("load", |b| {
        let a = AtomicU64::new(0);
        b.iter(|| {
            let _ = a.load(ORDERING);
        });
    });

    group.bench_function("cmpxchg_fail", |b| {
        let a = AtomicU64::new(0);
        b.iter(|| {
            a.compare_exchange(1, 2, ORDERING, ORDERING)
                .unwrap_err();
        });
    });

    group.bench_function("cmpxchg_success", |b| {
        let a = AtomicU64::new(0);
        let mut value = 0;
        b.iter(|| {
            a.compare_exchange(value, value + 1, ORDERING, ORDERING)
                .unwrap();
            value += 1;
        });
    });

    group.bench_function("fetch_add", |b| {
        let a = AtomicU64::new(0);
        b.iter(|| {
            a.fetch_add(1, ORDERING);
        });
    });

    group.bench_function("mutex_add", |b| {
        let m = sync::Mutex::new(0u64);
        b.iter(|| {
            let mut guard = m.lock().unwrap();
            *guard += 1;
        });
    });

    group.finish();
}

criterion_group!(benches, bench_atomics);
criterion_main!(benches);
