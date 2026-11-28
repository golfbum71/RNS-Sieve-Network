"""Shadows of the negative cycles (notes section 31).

The map x -> x/2, 3x+1 has, besides 1 -> 4 -> 2 -> 1, the cycles of -1, -5 and
-17 on the negative numbers. A positive number that agrees with a cycle member
in its last binary digits follows that cycle while the agreement lasts, scaled
by the cycle's 3^(odd steps) / 2^(halvings): 3/2 for -1, 9/8 for -5,
2187/2048 for -17. Checks the hand-offs and which sliver endings are shadows.
"""
import sys
def col(v): return v // 2 if v % 2 == 0 else 3 * v + 1

def cycle(a):
    seen, v = [], a
    while v not in seen: seen.append(v); v = col(v)
    c = seen[seen.index(v):]
    return c, sum(1 for w in c if w % 2), sum(1 for w in c if w % 2 == 0)

for a in (-1, -5, -17):
    c, u, k = cycle(a)
    print(f"cycle of {a}: {c}  odd steps {u}, halvings {k}, factor 3^{u}/2^{k} = {3**u / 2**k:.4f}")
    # hand-off: x = a + 2^k * y  ->  after u + k steps: a + 3^u * y
    for y in range(1, 20000):
        x = a + 2 ** k * y
        if x <= 0: continue
        v = x
        for _ in range(u + k): v = col(v)
        assert v == a + 3 ** u * y, (a, y)
    print("  hand-off checked for y < 20000")

# the sliver endings on division by 32 are the shadows of the negative cycles
negs = sorted({w for a in (-1, -5, -17) for w in cycle(a)[0] if w % 2})
ends = {a % 32: a for a in negs}
print("odd negative-cycle members and their last 5 binary digits:")
for e, a in sorted(ends.items()): print(f"  {a:5} ends ...{e:05b}")
