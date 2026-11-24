"""
Funnel depth test on the hub n-map.

A peak P is a run exit (odd multiple of 3). Its funnel is everything that climbs
to P and no higher: grow backward from P with the linking rules, keeping only
values below P:
    ladder     v <- 4v - 1          (up)
    d entry    v <- (4v - 1)/3      (up,   v = 1 mod 3)
    run entry  v <- 2v/3            (down, v = 0 mod 3)
The funnel's smallest member n_min is the deepest start that peaks at P.
Exponent e = log(n_min)/log(P).  "Peak <= n^2" is the same as e >= 1/2.

Usage: python3 funnels.py
"""
import math
import random


def funnel(P, cap=3_000_000):
    seen = {P}
    stack = [P]
    lo = P
    while stack:
        v = stack.pop()
        preds = [4 * v - 1]
        r = v % 3
        if r == 0:
            preds.append(2 * v // 3)
        elif r == 1 and v > 1:
            preds.append((4 * v - 1) // 3)
        for w in preds:
            if w < P and w not in seen:
                seen.add(w)
                stack.append(w)
                if w < lo:
                    lo = w
                if len(seen) > cap:
                    return lo, len(seen), False
    return lo, len(seen) - 1, True


def report(label, peaks):
    rows = []
    for P in peaks:
        lo, size, done = funnel(P)
        if size and lo < P:
            rows.append((math.log(lo) / math.log(P), P, lo, size, done))
    rows.sort()
    es = [r[0] for r in rows]
    print(f"\n{label}: {len(rows)} funnels")
    print(f"  exponent e  min {es[0]:.3f}   median {es[len(es)//2]:.3f}   "
          f"share with e < 0.5: {sum(e < .5 for e in es)/len(es):.2%}")
    print("  deepest funnels (e, peak P, smallest member, funnel size):")
    for e, P, lo, size, done in rows[:6]:
        print(f"    {e:.3f}  {P:>14}  {lo:>10}  {size:>8}{'' if done else ' (capped)'}")
    return rows


def main():
    random.seed(1)
    # 1) every possible peak up to 2^18
    report("All run exits P < 2^18", [P for P in range(3, 1 << 18, 6)])
    # 2) random run exits at larger scales
    for b in (24, 30, 36):
        lo, hi = 1 << (b - 1), 1 << b
        ps = [6 * random.randrange(lo // 6, hi // 6) + 3 for _ in range(400)]
        report(f"400 random run exits near 2^{b}", ps)
    # 3) the shared peaks of the top climbers found earlier
    report("Top climbers' shared peaks",
           [413685225, 98879859, 466387227, 4108012983, 261804123,
            20168811, 17726337, 2867062959, 1135023, 1358937, 1605987])


if __name__ == "__main__":
    main()
