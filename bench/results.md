# Benchmark results

2026-10-01, Apple M5, 10 cores, macOS 27.0; go1.27.1; Lean (version 4.34.1. Median of 5 runs.

## Jepsen etcd histories (cas-register, 102 files)
```
file                             ops   verdict    porcupine     linproof linproof-cli
total                                             221.04 ms     37.45 ms    360.75 ms
```

The five slowest for linproof:
```
file                             ops   verdict    porcupine     linproof linproof-cli
etcd_080.jsonl                    84        ok      4.26 ms      9.25 ms     12.30 ms
etcd_099.jsonl                    82 VIOLATION     24.82 ms      6.16 ms     15.96 ms
etcd_057.jsonl                    81 VIOLATION     26.94 ms      5.49 ms     14.58 ms
etcd_040.jsonl                    83 VIOLATION      5.97 ms      3.91 ms     11.16 ms
etcd_007.jsonl                    81        ok     58.10 ms      2.98 ms      6.43 ms
```

## Key-value histories (Porcupine's test data)
```
file                             ops   verdict    porcupine     linproof linproof-cli
c01-bad.jsonl                     38 VIOLATION      0.02 ms      0.07 ms      2.73 ms
c01-ok.jsonl                      58        ok      0.05 ms      0.12 ms      2.91 ms
c10-bad.jsonl                    405 VIOLATION      0.06 ms      0.13 ms      3.98 ms
c10-ok.jsonl                     337        ok      0.12 ms      0.27 ms      3.96 ms
c50-bad.jsonl                   2024 VIOLATION      2.88 ms      7.73 ms     25.07 ms
c50-ok.jsonl                    1712        ok     25.46 ms     61.46 ms     71.54 ms
total                                              28.59 ms     69.78 ms    110.20 ms
```

## Generated histories
```
file                             ops   verdict    porcupine     linproof linproof-cli
register-1k.jsonl               1000        ok      0.67 ms      1.27 ms      5.91 ms
register-10k.jsonl             10000        ok     14.08 ms     13.04 ms     33.78 ms
register-100k.jsonl           100000        ok    757.34 ms    177.61 ms    372.68 ms
total                                             772.08 ms    191.92 ms    412.38 ms
file                             ops   verdict    porcupine     linproof linproof-cli
cas-10k-crash.jsonl            10000        ok     12.91 ms     21.14 ms     44.91 ms
cas-100k-crash.jsonl          100000        ok    549.43 ms    942.72 ms   1148.82 ms
cas-10k-bad.jsonl              10000 VIOLATION     50.96 ms     51.71 ms    134.84 ms
total                                             613.29 ms   1015.57 ms   1328.58 ms
file                             ops   verdict    porcupine     linproof linproof-cli
kv-100k-100keys.jsonl         100000        ok     24.11 ms    539.06 ms    812.56 ms
total                                              24.11 ms    539.06 ms    812.56 ms
```

A violation hidden among operations that never returned (1 run, 30 s limit):
```
file                             ops   verdict    porcupine     linproof linproof-cli
cas-10k-crash-bad.jsonl        10000         ?       > 30 s       > 30 s       > 30 s
total                                               0.00 ms      0.00 ms      0.00 ms  (files where a tool timed out are left out of the total)
```
