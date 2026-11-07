#!/bin/bash

# Benchmark script for gol_engines_cli update command
# Tests different GENS_LOG2 values

# Define the GENS_LOG2 values to test
GENS_LOG2_VALUES=(10 12 13)

echo "Starting benchmark for 0e0p-metaglider pattern"
echo "=============================================="

# Ensure the script is run as root
if [ "$EUID" -ne 0 ]; then
    echo "Please run this script as root"
    exit 1
fi

for GENS_LOG2 in "${GENS_LOG2_VALUES[@]}"; do
    echo "Running with GENS_LOG2=$GENS_LOG2"

    # Run the command
    nice -n -20 target/release/gol_engines_cli update \
        res/very_large_patterns/0e0p-metaglider.mc.gz \
        --output=res/temp.mc.gz \
        --population \
        --engine=hashlife \
        --workers=6 \
        --mem-limit-gib=24 \
        --gens-log2=$GENS_LOG2

    echo "----------------------------------------"
done

echo "Benchmark completed"
