# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 lyapunov_search.py
"""Searching for a Lyapunov score on the hub map.

A block is one run of bad loops plus the drop that ends it: from an index with
k factors of 2 (2^k times an odd number m), k bad loops reach 3^k*m, then one
drop. (An odd index is a block of a single drop.) A Lyapunov score would go
down over every block, or at least within a bounded number of blocks.

Candidate scores:  V(n) = log2(n) + a * (factors of 2 in n) + b * (factors of 3 in n)
The a term pre-charges a run before it happens; the b term credits the run
entries (multiples of 3 are reached from below). a = b = 0 is the plain size.

For each score: the share of indices whose score drops in one block, and the
largest number of blocks needed before the score first drops (the window).
A true Lyapunov score has window 1 everywhere; a useful one has a small window.
"""
import math
from collatz_link_sieve import hub_step

N = 1 << 18


def v(n, p):
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def block(n):
    while n % 2 == 0:
        n = 3 * n // 2
    return hub_step(n)[0]


BL = {}


def blk(n):
    if n not in BL:
        BL[n] = block(n)
    return BL[n]


def score(n, a, b):
    return math.log2(n) + a * v(n, 2) + b * v(n, 3)


def test(a, b, limit=400):
    one, worst, wn, total = 0, 0, 0, 0
    for n in range(2, N):
        s0 = score(n, a, b)
        m, j = n, 0
        while True:
            m = blk(m)
            j += 1
            if m == 1 or score(m, a, b) < s0 - 1e-12 or j > limit:
                break
        total += 1
        one += j == 1
        if j > worst:
            worst, wn = j, n
    return one / total, worst, wn


print(f"hub indices 2..{N}")
print(f"{'a (per 2)':>9} {'b (per 3)':>9} {'drops in 1 block':>17} {'worst window':>13}  worst index")
best = None
for a in [0, 0.2, 0.4, 0.585, 0.8, 1.0, 1.2]:
    for b in [-0.6, -0.3, 0, 0.3, 0.6]:
        sh, w, wn = test(a, b)
        print(f"{a:>9} {b:>9} {sh:>17.2%} {w:>13}  {wn}")
        if best is None or (w, -sh) < (best[0], -best[1]):
            best = (w, sh, a, b, wn)
print(f"\nsmallest worst window: {best[0]} blocks at a = {best[2]}, b = {best[3]} "
      f"(drops in one block for {best[1]:.1%}; worst index {best[4]})")

# Why no score of this kind can have window 1: after any block the next index
# can have any number of factors of 2, so the next block can climb by any amount.
print("\nnext block's run length after a drop (share of indices, all n < N):")
from collections import Counter
c = Counter(min(v(blk(n), 2), 8) for n in range(2, N))
print("  ", {k: f"{c[k] / (N - 2):.3f}" for k in sorted(c)})
