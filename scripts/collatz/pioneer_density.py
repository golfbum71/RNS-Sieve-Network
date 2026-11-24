# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 pioneer_density.py
"""How pioneers thin out, the way primes do.

A pioneer is an index that, when the rising tide reaches it, is dry and must
climb all the way to its own peak before touching the flood (the smallest
member of a mountain). Counts pioneers per doubling block of indices whose
peak reaches at least a given power of the starting index, and the gaps
between them.
"""
import math
from collatz_link_sieve import hub_step

K = 22
N = 1 << K
wet = {1}
pio = []          # (index, peak exponent)
for X in range(2, N + 1):
    if X in wet:
        continue
    n, hi, new, pk = X, X, [X], X
    while n not in wet:
        n, _ = hub_step(n)
        new.append(n)
        hi = max(hi, n)
    # peak before dropping below X
    m = X
    while m >= X:
        m, _ = hub_step(m)
        pk = max(pk, m)
    wet.update(new)
    if hi >= pk and pk > X:
        pio.append((X, math.log(pk) / math.log(X)))

print(f"hub indices up to 2^{K}: {len(pio)} pioneers in all")
cs = [1.25, 1.5, 1.75]
print("block of indices  | pioneers | peak >= n^1.25 | n^1.5 | n^1.75 | share of block")
for k in range(10, K):
    lo, hi = 1 << k, 1 << (k + 1)
    sel = [e for x, e in pio if lo <= x < hi]
    row = [sum(e >= c for e in sel) for c in cs]
    print(f"  2^{k:<2}..2^{k + 1:<2}      | {len(sel):>8} | {row[0]:>14} | {row[1]:>5} | {row[2]:>6} | {len(sel) / (hi - lo):.3f}")
big = [x for x, e in pio if e >= 1.5]
gaps = [b - a for a, b in zip(big, big[1:])]
print(f"\npioneers peaking at n^1.5 or more: {len(big)}; first {big[:8]}; "
      f"largest gap {max(gaps) if gaps else None}")
