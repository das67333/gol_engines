#![feature(asm_experimental_arch)] // нужно для inline-asm
use criterion::{criterion_group, criterion_main, Criterion};
use libc::{clock_gettime, timespec, CLOCK_MONOTONIC_RAW};
use std::time::Duration;

// -------------------------------
// Вариант 1: clock_gettime
// -------------------------------
fn now_clock_gettime() -> Duration {
    unsafe {
        let mut ts: timespec = std::mem::zeroed();
        if clock_gettime(CLOCK_MONOTONIC_RAW, &mut ts) != 0 {
            panic!("clock_gettime failed");
        }
        Duration::new(ts.tv_sec as u64, ts.tv_nsec as u32)
    }
}

// -------------------------------
// Вариант 2: CNTVCT_EL0
// -------------------------------
#[inline(always)]
fn read_cntvct() -> u64 {
    let value: u64;
    unsafe {
        core::arch::asm!("mrs {0}, cntvct_el0", out(reg) value);
    }
    value
}

#[inline(always)]
fn read_cntfrq() -> u64 {
    let value: u64;
    unsafe {
        core::arch::asm!("mrs {0}, cntfrq_el0", out(reg) value);
    }
    value
}

fn now_cntvct() -> Duration {
    let freq = read_cntfrq();
    let ticks = read_cntvct();
    Duration::from_nanos(ticks * 1_000_000_000 / freq)
}

// -------------------------------
// Criterion бенчмарк
// -------------------------------
fn bench_time(c: &mut Criterion) {
    let mut group = c.benchmark_group("time_sources");

    group.bench_function("clock_gettime", |b| {
        b.iter(|| {
            let _ = now_clock_gettime();
        });
    });

    group.bench_function("cntvct_el0", |b| {
        b.iter(|| {
            let _ = now_cntvct();
        });
    });

    group.finish();
}

criterion_group!(benches, bench_time);
criterion_main!(benches);
