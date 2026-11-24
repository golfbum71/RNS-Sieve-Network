# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 cover_height.py
"""How high must 1's tree reach to cover every forced escape route?

For each member n of the linking sieve's open classes (problem areas), follow
the loops its digits force. The forced stretch lands on 1's tree grown up to a
cap exactly when the cap is at least the highest value on the route to 1 from
the end of the forced stretch. That needed cap is reported as a power of n
(log of the cap over log of n), by sieve depth and by size of n. A proof along
these lines needs this power to stay below a fixed number.
"""
import math
import sys
import collatz_link_sieve as S

X = 1 << (int(sys.argv[1]) if len(sys.argv) > 1 else 24)


def pathmax(v):
    hi = v
    while v != 1:
        v, _ = S.hub_step(v)
        if v > hi:
            hi = v
    return hi


rules = [S.rule_mod3_entry, S.rule_half_pair]
open_cls, M = [0, 1, 2], 3
by_size = {}
print(f"members up to 2^{X.bit_length() - 1}")
print(f"{'depth':>5} {'members':>8} {'median power':>13} {'99% power':>10} {'max power':>10}  worst n")
for K in range(0, 21):
    keep = []
    for a in open_cls:
        if any(r(a, M) for r in rules):
            continue
        if S.run_class(a, M, True, True)[0] == "open":
            keep.append(a)
    if K >= 8 and K % 2 == 0:
        pw = []
        for a in keep:
            L = len(S.run_class(a, M)[1])
            for n in range(a if a else M, X + 1, M):
                if n < 16:
                    continue
                v = n
                for _ in range(L):
                    v, _ = S.hub_step(v)
                e = math.log(pathmax(v)) / math.log(n)
                pw.append((e, n))
                if K == 16:
                    b = n.bit_length() - 1
                    by_size[b] = max(by_size.get(b, (0, 0)), (e, n))
        pw.sort()
        es = [e for e, _ in pw]
        print(f"{K:>5} {len(pw):>8} {es[len(es) // 2]:>13.3f} {es[int(.99 * (len(es) - 1))]:>10.3f} "
              f"{es[-1]:>10.3f}  {pw[-1][1]}")
    open_cls = [x for a in keep for x in (a, a + M)]
    M *= 2
print("\ndepth 16, largest needed power by size of n:")
for b in sorted(by_size):
    if b >= 10:
        print(f"   n in 2^{b}..2^{b + 1}: {by_size[b][0]:.3f}  (n = {by_size[b][1]})")
