#!/usr/bin/env bash
# Times linproof and Porcupine on the same histories:
#   - the 102 Jepsen etcd histories and 6 key-value histories shipped with Porcupine
#     (converted with tools/jepsen2jsonl.py), and
#   - larger generated histories (fixed seeds).
# Porcupine's time is measured in-process around porcupine.CheckOperations; linproof's
# "check" time is what the tool reports (parsing excluded), and "cli" is the wall time of
# the whole linproof process. Each figure is the median of RUNS runs.
# Run from the repository root: ./bench/run.sh
# Scratch files go to bench/out/ (ignored by git); the summary is written to bench/results.md.
set -euo pipefail

RUNS=${RUNS:-5}
bin=$(pwd)/.lake/build/bin/linproof
out=$(pwd)/bench/out
mkdir -p "$out/etcd" "$out/kv" "$out/gen"

(cd test/porcupine && go build -o "$out/porcupine-diff" .)
pd="$out/porcupine-diff"
dir=$(cd test/porcupine && go list -m -f '{{.Dir}}' github.com/anishathalye/porcupine)

for f in "$dir"/test_data/jepsen/etcd_*.log; do
  python3 tools/jepsen2jsonl.py "$f" > "$out/etcd/$(basename "$f" .log).jsonl"
done
for f in "$dir"/test_data/kv/*.txt; do
  python3 tools/jepsen2jsonl.py "$f" > "$out/kv/$(basename "$f" .txt).jsonl"
done

gen() { "$pd" gen -o "$out/gen/$1.jsonl" "${@:2}"; }
gen register-1k      -model register     -ops 1000   -procs 5  -values 50 -pending 0    -seed 1
gen register-10k     -model register     -ops 10000  -procs 5  -values 50 -pending 0    -seed 2
gen register-100k    -model register     -ops 100000 -procs 5  -values 50 -pending 0    -seed 3
gen cas-10k-crash    -model cas-register -ops 10000  -procs 5  -values 5  -pending 0.01 -seed 4
gen cas-100k-crash   -model cas-register -ops 100000 -procs 5  -values 5  -pending 0.01 -seed 4
gen cas-10k-bad      -model cas-register -ops 10000  -procs 5  -values 5  -pending 0    -seed 7 -corrupt
gen cas-10k-crash-bad -model cas-register -ops 10000 -procs 5  -values 5  -pending 0.01 -seed 4 -corrupt
gen kv-100k-100keys  -model kv -ops 100000 -procs 20 -keys 100 -pending 0.01           -seed 5

{
  echo "# Benchmark results"
  echo
  echo "$(date -u +%Y-%m-%d), $(sysctl -n machdep.cpu.brand_string 2>/dev/null || uname -m)," \
       "$(sysctl -n hw.ncpu 2>/dev/null || nproc) cores, $(sw_vers -productName 2>/dev/null || uname -s)" \
       "$(sw_vers -productVersion 2>/dev/null || uname -r); $(go version | cut -d' ' -f3);" \
       "$(lean --version | cut -d',' -f1). Median of $RUNS runs."
  echo
  echo "## Jepsen etcd histories (cas-register, 102 files)"
  "$pd" bench -linproof "$bin" -model cas-register -runs "$RUNS" "$out"/etcd/*.jsonl > "$out/etcd.txt"
  echo '```'
  head -1 "$out/etcd.txt"
  grep '^total' "$out/etcd.txt"
  echo '```'
  echo
  echo "The five slowest for linproof:"
  echo '```'
  head -1 "$out/etcd.txt"
  grep -v '^total' "$out/etcd.txt" | tail -n +2 | sort -k6 -n -r | head -5
  echo '```'
  echo
  echo "## Key-value histories (Porcupine's test data)"
  echo '```'
  "$pd" bench -linproof "$bin" -model kv -runs "$RUNS" "$out"/kv/*.jsonl
  echo '```'
  echo
  echo "## Generated histories"
  echo '```'
  "$pd" bench -linproof "$bin" -model register -runs "$RUNS" \
    "$out"/gen/register-1k.jsonl "$out"/gen/register-10k.jsonl "$out"/gen/register-100k.jsonl
  "$pd" bench -linproof "$bin" -model cas-register -runs "$RUNS" \
    "$out"/gen/cas-10k-crash.jsonl "$out"/gen/cas-100k-crash.jsonl "$out"/gen/cas-10k-bad.jsonl
  "$pd" bench -linproof "$bin" -model kv -runs "$RUNS" "$out"/gen/kv-100k-100keys.jsonl
  echo '```'
  echo
  echo "A violation hidden among operations that never returned (1 run, 30 s limit):"
  echo '```'
  "$pd" bench -linproof "$bin" -model cas-register -runs 1 -timeout 30s "$out"/gen/cas-10k-crash-bad.jsonl
  echo '```'
} | tee bench/results.md
