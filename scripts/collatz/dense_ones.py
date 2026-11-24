# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 dense_ones.py
"""Engineering climbers by their digits: do dense binary ones make big mountains?

Builds random odd Collatz starting numbers of a fixed size whose last two
binary digits are 01 (so the first run is just one step, and trailing ones do
not help), with every other digit a 1 with a chosen probability. Measures how
high they climb, in bits above the start, and how often they reach the 1.3
power of the start.
"""
import math
import random

random.seed(21)


def climb_bits(x):
    pk = x
    while x != 1:
        x = 3 * x + 1 if x & 1 else x >> 1
        if x > pk:
            pk = x
    return pk


B = 48
N = 6000
print(f"{B}-bit odd numbers ending in binary 01, {N} per row")
print("ones probability | mean climb (bits) | share reaching x^1.3 | share reaching x^1.5")
for p in (0.3, 0.5, 0.7, 0.85, 0.95):
    cl, a, b = [], 0, 0
    for _ in range(N):
        bitsx = [1] + [1 if random.random() < p else 0 for _ in range(B - 3)] + [0, 1]
        x = int("".join(map(str, bitsx)), 2)
        pk = climb_bits(x)
        c = math.log2(pk / x)
        cl.append(c)
        e = math.log(pk) / math.log(x)
        a += e >= 1.3
        b += e >= 1.5
    print(f"{p:>16} | {sum(cl) / N:>17.2f} | {a / N:>20.2%} | {b / N:>20.2%}")
