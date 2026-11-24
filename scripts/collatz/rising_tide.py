# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 rising_tide.py [N]
"""The rising tide.

Go up the hub indices 1, 2, 3, ... in order. The flood is every value on the
path of any index already done. When the tide reaches index X:
  * X may already be wet: some smaller index's path passed through it;
  * otherwise follow X until its path touches the flood (it then shares that
    path down to 1), and add the new stretch of path to the flood.
Compared with the usual rule (follow X until it drops below X), the flood
links X to a smaller number's path as soon as the two meet, usually well
below X's peak.
"""
import sys
from collatz_link_sieve import hub_step

N = int(sys.argv[1]) if len(sys.argv) > 1 else 1 << 20
wet = {1}
already = 0
steps_flood, steps_drop = [], []
over_flood, over_peak = [], []
worst = []
for X in range(2, N + 1):
    # usual rule: steps until below X, and the peak on the way
    n, s, pk = X, 0, X
    while n >= X:
        n, _ = hub_step(n)
        s += 1
        pk = max(pk, n)
    steps_drop.append(s)
    over_peak.append(pk / X)
    if X in wet:
        already += 1
        steps_flood.append(0)
        over_flood.append(1.0)
        continue
    n, s, hi, new = X, 0, X, [X]
    while n not in wet:
        n, _ = hub_step(n)
        s += 1
        hi = max(hi, n)
        new.append(n)
    wet.update(new)
    steps_flood.append(s)
    over_flood.append(hi / X)
    worst.append((hi / X, X, s, pk / X))

tot = N - 1
q = lambda L, f: sorted(L)[int(f * (len(L) - 1))]
print(f"hub indices 2..{N}")
print(f"already wet when the tide arrives: {already} ({already / tot:.1%})")
print(f"loops needed      flood: mean {sum(steps_flood) / tot:.2f}, 99% {q(steps_flood, .99)}, max {max(steps_flood)}")
print(f"                  drop below start: mean {sum(steps_drop) / tot:.2f}, 99% {q(steps_drop, .99)}, max {max(steps_drop)}")
print(f"height needed (x start)  flood: 99% {q(over_flood, .99):.2f}, max {max(over_flood):.1f}")
print(f"                         peak before dropping: 99% {q(over_peak, .99):.2f}, max {max(over_peak):.1f}")
print(f"size of the flood: {len(wet)} values")
dry = len(worst)
no_climb = sum(1 for h, X, s_, p in worst if h == 1.0)
below_peak = sum(1 for h, X, s_, p in worst if 1.0 < h < p)
pioneers = sum(1 for h, X, s_, p in worst if h > 1.0 and h >= p)
print(f"dry indices: {dry} ({dry / tot:.1%}); of these")
print(f"   reach the flood without climbing at all: {no_climb} ({no_climb / tot:.1%} of all)")
print(f"   climb, but meet the flood below their peak: {below_peak} ({below_peak / tot:.1%} of all)")
print(f"   must climb all the way to their peak (mountain pioneers): {pioneers} ({pioneers / tot:.2%} of all)")
print("hardest dry indices (height to reach the flood, loops, peak before dropping, all x start):")
for h, X, s, p in sorted(worst, reverse=True)[:8]:
    print(f"   X={X:<8} flood at {h:7.1f}x after {s:3} loops   (peak {p:7.1f}x)")
