# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 pioneer_staircase.py
"""The pioneer's staircase: the smaller peaks on a giant mountain's pioneer's climb, which of them it is also the pioneer of (exactly its new highs), and sub-mountain sizes by depth below the peak."""
import sys, math; sys.path.insert(0,'.')
from sub_peaks import mountain, tree
from collatz_link_sieve import hub_step
from collections import defaultdict
for P in [4108012983, 2867062959, 413685225, 20168811]:
    M = mountain(P); pio = min(M)
    # local peaks on the pioneer's climb
    n, path = pio, []
    while n != P:
        m, t = hub_step(n)
        if t != 'U' and n % 2 == 1 and n % 3 == 0 and n != pio: pass
        path.append(n); n = m
    peaks = [q for q in path if q % 6 == 3 and (2*q//3) in M]
    same = sum(1 for q in peaks if min(tree(q, q)) == pio)
    print(f"peak {P}: pioneer {pio}; smaller peaks on its climb {len(peaks)}; pioneer is also the pioneer of {same} of them")
    # other sub-mountains' pioneers: where do they join (as a share of P)?
    # sub-mountain sizes by depth band below P
    band = defaultdict(list)
    for q in M:
        if q % 6 == 3:
            band[int(math.log2(P / q))].append(len(tree(q, q)) - 1)
    print("   band below peak: smaller peaks, mean sub-mountain size, share with 16+ members")
    for j in sorted(band)[:12]:
        L = band[j]
        print(f"   {j:>3}: {len(L):>6} {sum(L)/len(L):8.2f} {sum(s >= 16 for s in L)/len(L):8.3%}")
