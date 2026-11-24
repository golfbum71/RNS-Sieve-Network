# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 climber_digits.py
"""Is something in a big climber's digits that sets it apart?

Takes every odd Collatz starting number x (hub index n = (x + 1)/2) in one size
band, ranks them by how high they climb (peak as a power of the start), and
compares the top climbers with everyone in the band on many digit features:
binary length, ones density, trailing ones, longest block of ones, number of
blocks, ternary digits, remainders on division by 3, 9, 27, 7, 5.
A feature that sets the climbers apart shows a 'lift' far from 1.
"""
import math
from collections import Counter, defaultdict
from collatz_link_sieve import hub_step

LO, HI = 1 << 20, 1 << 21          # hub indices in this band
TOP = 0.001                        # top 0.1% climbers


def peak_power(n):
    m, pk = n, n
    while m != 1:
        m, _ = hub_step(m)
        if m > pk:
            pk = m
    return math.log(pk) / math.log(n)


def bits(x):
    return bin(x)[2:]


def tern(x):
    d = []
    while x:
        d.append(x % 3)
        x //= 3
    return d


def features(x):
    b = bits(x)
    t = tern(x)
    ones = b.count("1")
    blocks = [len(s) for s in b.split("0") if s]
    return {
        "binary length mod 2": len(b) % 2,
        "binary length mod 3": len(b) % 3,
        "ones density (tenths)": int(10 * ones / len(b)),
        "trailing ones (cap 6)": min(len(b) - len(b.rstrip("1")), 6),
        "longest block of ones (cap 8)": min(max(blocks), 8),
        "number of blocks of ones (fifths of length)": int(5 * len(blocks) / len(b)),
        "share of digit 2 in base 3 (tenths)": int(10 * t.count(2) / len(t)),
        "x mod 3": x % 3,
        "x mod 9": x % 9,
        "x mod 27 (top)": x % 27,
        "x mod 7": x % 7,
        "x mod 5": x % 5,
    }


rows = []
for n in range(LO, HI):
    rows.append((peak_power(n), 2 * n - 1))
rows.sort(reverse=True)
k = int(TOP * len(rows))
top = [x for _, x in rows[:k]]
everyone = [x for _, x in rows]
print(f"hub indices {LO}..{HI} (Collatz numbers {2 * LO - 1}..{2 * HI - 1}); "
      f"top {k} climbers reach n^{rows[k - 1][0]:.3f} to n^{rows[0][0]:.3f}\n")

ft = defaultdict(Counter)
fa = defaultdict(Counter)
for x in top:
    for f, v in features(x).items():
        ft[f][v] += 1
for x in everyone:
    for f, v in features(x).items():
        fa[f][v] += 1
for f in fa:
    lifts = []
    for v, c in fa[f].items():
        pa = c / len(everyone)
        pt = ft[f][v] / len(top)
        if pa >= 0.002:
            lifts.append((pt / pa, v, pt, pa))
    lifts.sort(reverse=True)
    hi_ = lifts[0]
    lo_ = lifts[-1]
    print(f"{f:<44} strongest lift {hi_[0]:5.2f} at {hi_[1]!s:<3} ({hi_[2]:.1%} vs {hi_[3]:.1%}); "
          f"weakest {lo_[0]:4.2f} at {lo_[1]!s:<3} ({lo_[2]:.1%} vs {lo_[3]:.1%})")
