# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 climb_bound.py
"""The fair game and how high numbers climb.

1. The loop odds over residues are 1/2, 1/4, 1/4 with multipliers 3/2, 3/4, 1/4,
   so the average multiplier is exactly 1 (the Lean claim fair_block is the
   exact block form). Doob's inequality then bounds the share of starts that
   ever climb to 2^d times their start by 2^-d. Measured for hub n from 2^16 to
   2^20.
2. Worst peak as a power of the start, for hub n up to 2^20 (about n^2).
"""
import math
from collatz_link_sieve import hub_step

print("average multiplier:", 0.5 * 1.5 + 0.25 * 0.75 + 0.25 * 0.25)

N, L = 1 << 20, 1 << 16
cnt = [0] * 12
tot = 0
for n in range(L, N):
    m, pk = n, n
    while m != 1:
        m, _ = hub_step(m)
        if m > pk:
            pk = m
        if m < n:
            break
    r = math.log2(pk / n)
    tot += 1
    for d in range(12):
        if r >= d:
            cnt[d] += 1
print("\nclimb >= 2^d x start: measured share vs bound 2^-d")
for d in range(12):
    print(f"{d:>3}: {cnt[d] / tot:.5f}  {2 ** -d:.5f}")

worst = {}
for n in range(2, N):
    m, pk = n, n
    while m != 1:
        m, _ = hub_step(m)
        pk = max(pk, m)
    band = int(math.log(n, 16)) if n >= 1024 else None
    if band is not None:
        e = math.log(pk) / math.log(n)
        if e > worst.get(band, (0, 0))[0]:
            worst[band] = (e, n)
print("\nworst peak exponent log(peak)/log(n) by range of n:")
for b in sorted(worst):
    print(f"  n from {max(16 ** b, 1024)} to {16 ** (b + 1) - 1}: {worst[b][0]:.3f} (n = {worst[b][1]})")
