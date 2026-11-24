# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 sub_peaks.py
"""Smaller peaks inside a mountain.

A mountain is everything that climbs to peak P without passing it (the backward
tree of P below P). Inside it, a smaller peak is a member q where a run ends:
q is odd and was reached by a bad loop, so its run entry 2q/3 is also a member.
Each smaller peak has its own sub-mountain (its backward tree below q), which
lies entirely inside the big mountain, so the mountains nest.

Measures, for giant mountains and for many random ones: how many smaller peaks a
mountain of a given size has, how big their sub-mountains are, and how the
sub-mountain sizes are spread (count of sub-peaks at least a given size).
"""
import math
import random
from collections import Counter


def tree(v, B, cap=5_000_000):
    seen = {v}
    st = [v]
    while st:
        u = st.pop()
        ps = [4 * u - 1] + ([2 * u // 3] if u % 3 == 0 else []) + ([(4 * u - 1) // 3] if u % 3 == 1 else [])
        for w in ps:
            if w < B and w not in seen:
                seen.add(w)
                st.append(w)
    return seen


def mountain(P):
    m = tree(P, P)
    m.discard(P)
    return m


def sub_peaks(M):
    # A member q that ends a run is odd and divisible by 3; its run entry 2q/3 is
    # below q and steps onto it, so it is always a member too. So the smaller
    # peaks are exactly the members leaving remainder 3 on division by 6.
    return [q for q in M if q % 2 == 1 and q % 3 == 0 and (2 * q // 3) in M]


def analyse(P, show=True):
    M = mountain(P)
    peaks = sub_peaks(M)
    sizes = [len(tree(q, q)) - 1 for q in peaks]   # members strictly below q climbing to q
    if show:
        S = len(M)
        print(f"\npeak {P}: mountain size {S}, smaller peaks {len(peaks)} "
              f"(one per {S / max(1, len(peaks)):.2f} members)")
        c = sorted(sizes, reverse=True)
        print("   largest sub-mountains:", c[:8])
        for t in (1, 4, 16, 64, 256, 1024):
            print(f"   sub-mountains with at least {t:>4} members: {sum(s >= t for s in sizes):>6}"
                  f"   (x size/t = {sum(s >= t for s in sizes) * t / S:.3f})")
    return len(M), len(peaks), sizes


def main():
    for P in [4108012983, 2867062959, 413685225, 261804123, 20168811, 1358937]:
        analyse(P)

    random.seed(12)
    print("\nrandom peaks (odd multiples of 3) near 2^30 with mountains of at least 20 members:")
    pairs = []
    tries = 0
    while len(pairs) < 300 and tries < 200000:
        tries += 1
        P = 6 * random.randrange((1 << 29) // 6, (1 << 30) // 6) + 3
        M = mountain(P)
        if len(M) >= 20:
            pairs.append((len(M), len(sub_peaks(M))))
    pairs.sort()
    for lo, hi in [(20, 40), (40, 100), (100, 300), (300, 10**9)]:
        sel = [(s, k) for s, k in pairs if lo <= s < hi]
        if sel:
            print(f"   size {lo}-{hi if hi < 10**9 else 'up'}: {len(sel)} mountains, "
                  f"members per smaller peak {sum(s for s, _ in sel) / max(1, sum(k for _, k in sel)):.2f}")


if __name__ == "__main__":
    main()
