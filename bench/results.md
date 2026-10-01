# Benchmark results

2026-10-01, Apple M5, 10 cores, macOS 27.0; go1.27.1; Lean 4.34.1. Median of 5 runs; the machine was shared with other jobs.

## Jepsen etcd histories (cas-register, 102 files)
```
file                             ops   verdict    porcupine     linproof linproof-cli
total                                             305.91 ms    117.00 ms    561.42 ms
```

The five slowest for linproof:
```
file                             ops   verdict    porcupine     linproof linproof-cli
etcd_002.jsonl                    77        ok     93.94 ms     61.27 ms     65.35 ms
etcd_007.jsonl                    81        ok     63.61 ms     17.20 ms     20.95 ms
etcd_075.jsonl                    84        ok     22.04 ms      7.15 ms     13.08 ms
etcd_099.jsonl                    82 VIOLATION     51.13 ms      6.71 ms     22.01 ms
etcd_057.jsonl                    81 VIOLATION     39.69 ms      5.82 ms     16.32 ms
```

## Key-value histories (Porcupine's test data)
```
file                             ops   verdict    porcupine     linproof linproof-cli
c01-bad.jsonl                     38 VIOLATION      0.04 ms      0.16 ms      6.09 ms
c01-ok.jsonl                      58        ok      0.07 ms      0.18 ms      5.99 ms
c10-bad.jsonl                    405 VIOLATION      0.12 ms      0.21 ms      7.20 ms
c10-ok.jsonl                     337        ok      0.21 ms      0.42 ms      7.13 ms
c50-bad.jsonl                   2024 VIOLATION      4.04 ms     11.40 ms     40.47 ms
c50-ok.jsonl                    1712        ok     30.81 ms     69.39 ms     79.57 ms
total                                              35.30 ms     81.76 ms    146.45 ms
```

## Generated histories
```
file                             ops   verdict    porcupine     linproof linproof-cli
register-1k.jsonl               1000        ok      0.86 ms      1.33 ms      6.61 ms
register-10k.jsonl             10000        ok     16.67 ms     14.47 ms     36.70 ms
register-100k.jsonl           100000        ok    731.45 ms    172.12 ms    360.30 ms
total                                             748.98 ms    187.92 ms    403.61 ms
file                             ops   verdict    porcupine     linproof linproof-cli
cas-10k-crash.jsonl            10000        ok     13.19 ms     14.09 ms     37.23 ms
cas-100k-crash.jsonl          100000        ok    564.11 ms    401.33 ms    612.01 ms
cas-10k-bad.jsonl              10000 VIOLATION     77.25 ms     77.60 ms    207.30 ms
total                                             654.55 ms    493.02 ms    856.54 ms
file                             ops   verdict    porcupine     linproof linproof-cli
kv-100k-100keys.jsonl         100000        ok     36.65 ms    113.67 ms    380.68 ms
total                                              36.65 ms    113.67 ms    380.68 ms
```

A violation hidden among operations that never returned (1 run, 30 s limit):
```
file                             ops   verdict    porcupine     linproof linproof-cli
cas-10k-crash-bad.jsonl        10000         ?       > 30 s       > 30 s       > 30 s
total                                               0.00 ms      0.00 ms      0.00 ms  (files where a tool timed out are left out of the total)
```
