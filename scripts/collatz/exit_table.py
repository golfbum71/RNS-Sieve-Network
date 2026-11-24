# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 exit_table.py
"""The exit table: where a run hands off.

A run of bad loops from 2^k*m (m odd) ends at the odd index 3^k*m. Its remainder
mod 16 decides the drop it takes and what the new index does next. Also checks
that run length k and m mod 4 decide the drop (3^k is 1 mod 4 for k even, 3 for
k odd), and that exits land in every row whatever the run length.
"""
from collections import Counter
from collatz_link_sieve import hub_step


def nxt_kind(n):
    if n % 2 == 0:
        return "run of exactly 1" if n % 4 == 2 else "run of 2 or more"
    return "x0.75 drop" if n % 4 == 1 else "x0.25 drop"


print("exit mod 16 | drop  | new index mod 4 | what happens next   (checked on exits up to 10^5)")
for r in range(1, 16, 2):
    seen = Counter()
    for e in range(r, 100000, 16):
        new, t = hub_step(e)
        seen[(t, new % 4, nxt_kind(new))] += 1
    (t, m4, nk), = seen.keys()
    print(f"{r:>11} | {'x0.75' if t == 'd' else 'x0.25'} | {m4:>15} | {nk}")

ok = True
rows = Counter()
for k in range(1, 12):
    for m in range(1, 4000, 2):
        e = 3 ** k * m
        drop = "d" if e % 4 == 1 else "D"
        rule = "d" if (k % 2 == 0) == (m % 4 == 1) else "D"
        ok &= drop == rule
        rows[(k % 4, e % 16)] += 1
print("\nDrop decided by run length parity and m mod 4:", ok)
print("Every exit row reached for each run length mod 4:",
      all(rows[(k4, r)] > 0 for k4 in range(4) for r in range(1, 16, 2)))
