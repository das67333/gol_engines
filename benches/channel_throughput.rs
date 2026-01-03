use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use std::sync::Arc;
use std::thread;

// Let's model NodeIdx as a u32 for the benchmark.
type NodeIdx = u32;

const NUM_ITEMS: u64 = 1_000_000; // Total items to push/pop in one run.

/// The core logic for one benchmark run.
/// Spawns a configurable number of producer and consumer threads.
fn run_mpmc_test(num_producers: usize, num_consumers: usize) {
    let (sender, receiver) = crossbeam_channel::unbounded::<NodeIdx>();

    // --- Producer Threads ---
    let mut producer_handles = Vec::new();
    // Calculate items per producer, ensuring we send NUM_ITEMS in total.
    let items_per_producer = (NUM_ITEMS as f64 / num_producers as f64).ceil() as u64;

    for _ in 0..num_producers {
        let s = sender.clone();
        producer_handles.push(thread::spawn(move || {
            for i in 0..items_per_producer {
                s.send(i as NodeIdx).unwrap();
            }
        }));
    }
    // Drop the main sender so the channel closes once all producers are done.
    drop(sender);

    // --- Consumer Threads ---
    let mut consumer_handles = Vec::new();
    let receiver = Arc::new(receiver); // Share the receiver among consumers.

    for _ in 0..num_consumers {
        let r = Arc::clone(&receiver);
        consumer_handles.push(thread::spawn(move || {
            // Each consumer pulls items until the channel is empty and closed.
            while let Ok(_) = r.recv() {
                // In a real app, we'd do work here. For a throughput bench, we do nothing.
            }
        }));
    }

    // Wait for all threads to finish.
    for handle in producer_handles {
        handle.join().unwrap();
    }
    for handle in consumer_handles {
        handle.join().unwrap();
    }
}

/// The Criterion benchmark function.
fn mpmc_throughput_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("MPMC Channel Throughput");

    group.throughput(Throughput::Elements(NUM_ITEMS));

    let thread_counts = [1, 2, 4, 6, 8, 10, 12];

    for &threads in &thread_counts {
        let num_producers = threads;
        let num_consumers = threads;

        group.bench_with_input(
            BenchmarkId::new("channel", format!("{} Threads", threads)),
            &(num_producers, num_consumers),
            |b, &(p, c)| {
                b.iter(|| run_mpmc_test(p, c));
            },
        );
    }

    group.finish();
}

criterion_group!(benches, mpmc_throughput_benchmark);
criterion_main!(benches);
