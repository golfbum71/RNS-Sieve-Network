# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 climb_loops.py
"""How the record climbs move through the three loops.

Takes the top climbers among hub indices 2^20..2^21 and follows each from its
start to its peak, splitting the climb into the part read from its own digits
and the part after (bits used up: a bad loop uses 1, a drop uses 2). For each
part: the share of each loop, how long the runs are, the drop that follows each
run, and the common two-block patterns. Compared with ordinary paths.
"""
import math
from collections import Counter
from collatz_link_sieve import hub_step

LO, HI, TOP = 1 << 20, 1 << 21, 200


def climb(n):
    """loops from n to its peak, each tagged with whether n's own bits decide it."""
    b = math.log2(n)
    m, used, seq, pk, pk_at = n, 0, [], n, 0
    while m != 1:
        m2, t = hub_step(m)
        seq.append((t, used < b))
        used += 1 if t == "U" else 2
        m = m2
        if m > pk:
            pk, pk_at = m, len(seq)
    return seq[:pk_at], math.log(pk) / math.log(n)


ranked = sorted(((climb(n)[1], n) for n in range(LO, HI)), reverse=True)[:TOP]
print(f"top {TOP} climbers among hub indices {LO}..{HI}: peaks n^{ranked[-1][0]:.2f} to n^{ranked[0][0]:.2f}")


def summarize(label, seqs):
    loops = Counter()
    runs = Counter()
    drops_after_run = Counter()
    blocks = Counter()
    for s in seqs:
        k, prev_block = 0, None
        for t in s:
            loops[t] += 1
            if t == "U":
                k += 1
            else:
                runs[min(k, 6)] += 1
                drops_after_run[t] += 1
                blk = f"U{k}{t}"
                if prev_block:
                    blocks[(prev_block, blk)] += 1
                prev_block = blk
                k = 0
    tot = sum(loops.values())
    tr = sum(runs.values())
    print(f"\n{label}: {tot} loops")
    print(f"   bad loops {loops['U'] / tot:.1%}, x0.75 drops {loops['d'] / tot:.1%}, "
          f"x0.25 drops {loops['D'] / tot:.1%}")
    print("   runs before each drop (length: share):",
          {k: f"{runs[k] / tr:.2f}" for k in sorted(runs)})
    td = sum(drops_after_run.values())
    print(f"   drop after a run: x0.75 {drops_after_run['d'] / td:.1%}, x0.25 {drops_after_run['D'] / td:.1%}")
    tb = sum(blocks.values())
    print("   commonest pairs of blocks:",
          ", ".join(f"{a}+{b} {c / tb:.1%}" for (a, b), c in blocks.most_common(5)))


own, after = [], []
for _, n in ranked:
    s, _ = climb(n)
    own.append([t for t, o in s if o])
    after.append([t for t, o in s if not o])
summarize("record climbs, loops decided by their own digits", own)
summarize("record climbs, loops after their own digits ran out", after)

# ordinary paths for comparison: the first 60 loops of every 500th index
ordinary = []
for n in range(LO, HI, 500):
    m, s = n, []
    for _ in range(60):
        if m == 1:
            break
        m, t = hub_step(m)
        s.append(t)
    ordinary.append(s)
summarize("ordinary paths (first 60 loops)", ordinary)
