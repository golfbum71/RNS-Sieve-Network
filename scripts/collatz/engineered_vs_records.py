# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 engineered_vs_records.py
"""Climb paid for by a number's own digits against climb after they are used up.

A bad loop uses one binary digit and multiplies by exactly 1.5; a drop uses two
and never raises the index. So from its own digits an index can climb at most
by 1.5 per digit: a pure run from 2^b reaches 3^b, about the 1.585 power. Record
climbers are split into the climb read from their own digits and the climb
after those digits ran out.
"""
import math
from collatz_link_sieve import hub_step

print("start      bits | climb from its own digits | climb after they ran out | total peak power")
for n in [14, 2296, 38836, 79744, 135136, 606208, 3315838, 9819200, 1 << 20, 3 * (1 << 19)]:
    b = math.log2(n)
    used, v, pk, pk_in = 0, n, n, n
    while v != 1:
        v, t = hub_step(v)
        used += 1 if t == "U" else 2
        if v > pk:
            pk = v
        if used <= b and v > pk_in:
            pk_in = v
    print(f"{n:>9} {b:6.1f} | x n^{math.log(pk_in / n) / math.log(n):.3f}              "
          f"| x n^{math.log(pk / pk_in) / math.log(n):.3f}               | n^{math.log(pk) / math.log(n):.3f}")
