# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 staircase_steps.py
"""The steps of the staircase: what happens between one record peak and the next.

Every climb sets records R1 < R2 < ... < R_last (each the end of a run). After a
record, the path goes into a valley (the back side of that peak, through its
foothills) and either climbs above the record again (the next step of the
staircase) or never does (the record was the final peak).

For every record of every hub index in a band (up to its final peak):
  * the record's ending: remainder on division by 16 (the exit table row),
    the run that reached it, its factors of 3;
  * for records that are passed again: the valley's depth below the record,
    its loops, and the run that breaks out above the record.
Compared between records that continue and final peaks.
"""
import math
from collections import Counter
from collatz_link_sieve import hub_step

LO, HI = 1 << 18, 1 << 19


def v(n, p):
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


cont, final = Counter(), Counter()
cont_run, final_run = Counter(), Counter()
cont3, final3 = Counter(), Counter()
depth, valley_loops, breakout = Counter(), Counter(), Counter()
valley_mix = Counter()
first_after = {"cont": Counter(), "final": Counter()}

for n0 in range(LO, HI):
    # walk to the final peak, remembering loops
    m, seq, vals = n0, [], [n0]
    while m != 1:
        m, t = hub_step(m)
        seq.append(t)
        vals.append(m)
    top = max(range(len(vals)), key=lambda i: vals[i])
    # records up to the final peak, with the run length that reached each
    recs, hi, k = [], n0, 0
    for i in range(1, top + 1):
        k = k + 1 if seq[i - 1] == "U" else 0
        if vals[i] > hi:
            hi = vals[i]
            if i < len(seq) and seq[i] != "U":       # a record that ends a run
                recs.append((i, k))
    for j, (i, k) in enumerate(recs):
        R = vals[i]
        row = R % 16
        nxt = seq[i] if i < len(seq) else None
        if j + 1 < len(recs):
            i2 = recs[j + 1][0]
            cont[row] += 1
            cont_run[min(k, 6)] += 1
            cont3[min(v(R, 3) - k, 3)] += 1
            first_after["cont"][nxt] += 1
            lo = min(vals[i:i2 + 1])
            depth[min(int(math.log2(R / lo)), 6)] += 1
            # loops spent below the record before the breakout, and the breakout run
            j2 = i
            while vals[j2] <= R:
                j2 += 1
            valley_loops[min(j2 - i, 12)] += 1
            for t in seq[i:j2]:
                valley_mix[t] += 1
            kk, p = 0, j2 - 1
            while p >= 0 and seq[p] == "U":
                kk += 1
                p -= 1
            breakout[min(kk, 6)] += 1
        else:
            final[row] += 1
            final_run[min(k, 6)] += 1
            final3[min(v(R, 3) - k, 3)] += 1
            first_after["final"][nxt] += 1


def share(c):
    t = sum(c.values())
    return {k: f"{c[k] / t:.2f}" for k in sorted(c, key=str)}


tc, tf = sum(cont.values()), sum(final.values())
print(f"hub indices {LO}..{HI}: {tc} records passed again, {tf} final peaks\n")
print("record's remainder on division by 16 -> share continuing / share final / ratio")
for r in sorted(set(cont) | set(final)):
    a, b = cont[r] / tc, final[r] / tf
    print(f"   {r:>2}: {a:6.1%}  {b:6.1%}  {a / b if b else float('inf'):5.2f}")
print("\nrun that reached the record (length): continuing", share(cont_run))
print("                                      final     ", share(final_run))
print("extra factors of 3 in the record beyond the run: continuing", share(cont3))
print("                                                 final     ", share(final3))
print("loop right after the record: continuing", share(first_after["cont"]),
      "| final", share(first_after["final"]))
print("\nvalleys between records:")
print("   depth below the record (bits):", share(depth))
print("   loops spent below the record:", share(valley_loops))
tv = sum(valley_mix.values())
print(f"   loop mix in the valley: bad {valley_mix['U'] / tv:.1%}, x0.75 {valley_mix['d'] / tv:.1%}, "
      f"x0.25 {valley_mix['D'] / tv:.1%}")
print("   length of the run that breaks out above the record:", share(breakout))
