"""Pioneer, peak and tide (notes section 26).

For every pioneer below LIMIT (odd, smallest number whose highest odd value
is its peak, peak above it) this checks:
  1. a peak that tops the first climb ends in exactly (ones - 1) ternary 2s;
  2. the exit index 3^(ones-1) * (odd part), on division by 16, against
     whether the path climbs above that first peak later;
  3. the tide (first value below the pioneer) comes right after a halving,
     never before 3^(odd steps) < 2^(halvings), and with a balance
     (halvings - 1.585 * odd steps) between 0 and 1 bit.
"""
import math, collections, sys
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
L3 = math.log2(3)

def col(v): return v // 2 if v % 2 == 0 else 3 * v + 1

def odd_peak(x):
    v, p = x, x
    while v != 1:
        v = col(v)
        if v % 2 and v > p: p = v
    return p

first = {}
for x in range(3, LIMIT, 2):
    p = odd_peak(x)
    if p > x and p not in first: first[p] = x
pioneers = sorted(first.values())

def t2(v):
    k = 0
    while v % 3 == 2: v //= 3; k += 1
    return k

sig_bad = 0; exits = collections.Counter(); tide_bad = 0; bal = []
for x in pioneers:
    j = 0
    while (x + 1) >> j & 1 == 0: j += 1
    m = (x + 1) >> j
    top = 2 * 3 ** (j - 1) * m - 1
    p = odd_peak(x)
    if p == top and t2(p) != j - 1: sig_bad += 1
    exits[(3 ** (j - 1) * m % 16, p != top)] += 1
    v, u, k, prev = x, 0, 0, None
    while v >= x:
        prev = v
        if v % 2: v = 3 * v + 1; u += 1
        else: v //= 2; k += 1
    B = k - L3 * u
    if prev % 2 or not (0 < B <= 1): tide_bad += 1
    bal.append(B)

print(f"pioneers below {LIMIT:,}: {len(pioneers):,}")
print("first-climb peaks without exactly (ones-1) ternary 2s:", sig_bad)
print("exit index mod 16: [peak is first climb, climbs higher later]")
for r in range(1, 16, 2): print(f"  {r:2}: {exits[(r, False)]:7,} {exits[(r, True)]:7,}")
print("tides not right after a halving or with balance outside (0, 1]:", tide_bad)
print(f"balance at tide: {min(bal):.3f} to {max(bal):.3f}")
