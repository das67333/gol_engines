#!/usr/bin/env python3
"""Plot task duration distributions from engine log output.

Usage:
    python plot_task_durations.py <log_file> [--save <output.png>]

Parses lines like:
    Task duration distribution (12345 total, base=1.05):
        10.0ns..10.5ns -> 12345
        95.5ns..100.2ns -> 5000
        1.05us..1.10us -> 200
"""

import re
import sys
import argparse

import matplotlib.pyplot as plt
import matplotlib.ticker as ticker
import numpy as np


def parse_duration(s: str) -> float:
    """Parse a duration string like '1ns', '1.0us', '5.1ms', '1.23s' to nanoseconds."""
    s = s.strip()
    for suffix, mult in [("ns", 1), ("us", 1e3), ("ms", 1e6), ("s", 1e9)]:
        if s.endswith(suffix):
            return float(s[: -len(suffix)]) * mult
    raise ValueError(f"Unknown duration format: {s}")


def parse_log(path: str) -> list[tuple[float, float, int]]:
    """Parse log file, return list of (lo_ns, hi_ns, count) tuples."""
    bins = []
    in_section = False
    range_pattern = re.compile(r"^\t(.+?)\.\.(.+?) -> (\d+)$")

    with open(path) as f:
        for line in f:
            if "Task duration distribution" in line:
                in_section = True
                continue
            if in_section:
                m = range_pattern.match(line)
                if m:
                    lo = parse_duration(m.group(1))
                    hi = parse_duration(m.group(2))
                    count = int(m.group(3))
                    bins.append((lo, hi, count))
                else:
                    if bins:
                        break
    return bins


def format_time(ns: float) -> str:
    """Format nanoseconds as human-readable string."""
    if ns < 1e3:
        return f"{ns:.0f}ns"
    if ns < 1e6:
        return f"{ns / 1e3:.1f}us"
    if ns < 1e9:
        return f"{ns / 1e6:.1f}ms"
    return f"{ns / 1e9:.2f}s"


def plot(bins: list[tuple[float, float, int]], save_path: str | None = None):
    fig, ax = plt.subplots(figsize=(14, 6))

    centers = []
    widths = []
    counts = []
    for lo, hi, count in bins:
        centers.append(np.sqrt(lo * hi))  # geometric mean
        widths.append(hi - lo)
        counts.append(count)

    centers = np.array(centers)
    widths = np.array(widths)
    counts = np.array(counts)

    ax.bar(centers, counts, width=widths, align="center", edgecolor="steelblue",
           color="steelblue", alpha=0.8, linewidth=0.5)

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("Task duration")
    ax.set_ylabel("Count")
    ax.set_title("Task PROCESSING Duration Distribution")
    ax.grid(True, alpha=0.3, which="both")

    # Custom tick labels
    ax.xaxis.set_major_formatter(ticker.FuncFormatter(lambda x, _: format_time(x)))
    ax.xaxis.set_major_locator(ticker.LogLocator(base=10, numticks=15))

    total = counts.sum()
    median_idx = np.searchsorted(np.cumsum(counts), total / 2)
    p99_idx = np.searchsorted(np.cumsum(counts), total * 0.99)
    median_ns = centers[min(median_idx, len(centers) - 1)]
    p99_ns = centers[min(p99_idx, len(centers) - 1)]

    stats_text = (
        f"Total: {total:,}\n"
        f"Median: ~{format_time(median_ns)}\n"
        f"P99: ~{format_time(p99_ns)}"
    )
    ax.text(0.98, 0.95, stats_text, transform=ax.transAxes,
            verticalalignment="top", horizontalalignment="right",
            fontsize=10, fontfamily="monospace",
            bbox=dict(boxstyle="round,pad=0.5", facecolor="wheat", alpha=0.8))

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path, dpi=150)
        print(f"Saved to {save_path}")
    else:
        plt.show()


def main():
    parser = argparse.ArgumentParser(description="Plot task duration distributions")
    parser.add_argument("log_file", help="Path to engine log file")
    parser.add_argument("--save", help="Save plot to file instead of showing")
    args = parser.parse_args()

    bins = parse_log(args.log_file)
    if not bins:
        print("No task duration distribution found in log file.", file=sys.stderr)
        sys.exit(1)

    print(f"Parsed {len(bins)} non-zero bins, {sum(c for _, _, c in bins):,} total tasks")
    plot(bins, args.save)


if __name__ == "__main__":
    main()
