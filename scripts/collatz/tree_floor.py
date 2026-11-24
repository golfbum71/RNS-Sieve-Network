# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 tree_floor.py
"""A guaranteed floor for every backward tree, from the exact links alone.

Every ladder cycles through the remainders on division by 3, so on every ladder
a branch entry rung (remainder 1) is followed directly by a run entry rung
(remainder 0) -- the exit pair -- once every three rungs. That holds on the
ladder of every node, whatever its digits. Letting an adversary pick the worst
starting remainder at every node gives a tree size no real tree can fall below.

Room is measured in bits (t = log2(ceiling / value)). One ladder rung costs 2
bits; a run entry gains log2(3/2) bits; a branch entry costs log2(4/3) bits.
F(t) = the smallest tree any node with room t can have. The growth exponent of
F is a proved-in-principle floor: every tree below a ceiling holds at least
about (room)^alpha members.
"""
import math
from functools import lru_cache

UP = math.log2(1.5)      # run entry child: more room
DOWN = math.log2(4 / 3)  # branch entry child: less room
STEP = 0.01


@lru_cache(maxsize=None)
def F(k):
    t = k * STEP
    if t < 0:
        return 0
    best = None
    for phase in (1, 2):          # phase 0 puts a run entry at the node itself: never smaller
        total, i = 0, 0
        while 2 * i <= t:
            total += 1
            r = (phase - i) % 3
            if r == 0:
                total += F(math.floor((t - 2 * i + UP) / STEP))
            elif r == 1 and t - 2 * i - DOWN >= 0:
                total += F(math.floor((t - 2 * i - DOWN) / STEP))
            i += 1
        best = total if best is None else min(best, total)
    return best


import sys
sys.setrecursionlimit(1000000)
print("room (bits)   floor F    log2 F / room")
prev = None
for T in (10, 20, 30, 40, 50, 60, 70, 80):
    v = F(int(T / STEP))
    print(f"{T:>10} {v:>12} {math.log2(v) / T:>10.3f}")
for T1, T2 in ((40, 60), (60, 80)):
    a = (math.log2(F(int(T2 / STEP))) - math.log2(F(int(T1 / STEP)))) / (T2 - T1)
    print(f"growth exponent from {T1} to {T2} bits: {a:.4f}")


# ---- One more exact ternary digit: track every node's remainder on division by 9.
# Rung remainders mod 9 follow exactly (4v - 1); a child's remainder mod 3 follows
# exactly from its rung's remainder mod 9; only the child's next digit is left to
# the adversary.
@lru_cache(maxsize=None)
def F9(k, r9):
    t = k * STEP
    if t < 0:
        return 0
    total, i, r = 0, 0, r9
    while 2 * i <= t:
        total += 1
        if r % 3 == 0:
            c3 = (2 * (r // 3)) % 3
            kk = math.floor((t - 2 * i + UP) / STEP)
            # a child with more room than this node: use the mod-3 floor F, which
            # holds for every node, so the recursion only ever goes down in room
            total += F(kk) if kk >= k else min(F9(kk, c3 + 3 * j) for j in range(3))
        elif r % 3 == 1 and t - 2 * i - DOWN >= 0:
            c3 = (r // 3 + 1) % 3
            total += min(F9(math.floor((t - 2 * i - DOWN) / STEP), c3 + 3 * j) for j in range(3))
        r = (4 * r - 1) % 9
        i += 1
    return total


def G9(T):
    k = int(T / STEP)
    # the root may be any remainder except a multiple of 3 run-entry chain at the top;
    # take the smallest over roots whose rung 0 is not a run entry (as above)
    return min(F9(k, r) for r in range(9) if r % 3 != 0)


print("\nwith remainders on division by 9 exact:")
for T1, T2 in ((20, 30), (30, 40)):
    a = (math.log2(G9(T2)) - math.log2(G9(T1))) / (T2 - T1)
    print(f"growth exponent from {T1} to {T2} bits: {a:.4f}")
