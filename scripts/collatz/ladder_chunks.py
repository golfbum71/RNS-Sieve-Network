"""
Grow ladder-chunks backward from n = 1 on the hub n-map and measure coverage.

Hub map (h = 6n - 2):  n even -> 3n/2,  n=1 mod 4 -> (3n+1)/4,  n=3 mod 4 -> (n+1)/4
Backward rules:
    ladder       v <- 4v - 1            (always; x0.25 loop)
    run entry    v <- 2v/3              (v = 0 mod 3; x1.5 loop, comes from BELOW)
    d entry      v <- (4v - 1)/3        (v = 1 mod 3; x0.75 loop)

Generation 0 = the full ladder of 1. Generation g+1 = side branches (run / d
entries) off generation-g nodes, plus their full ladders. Nodes are kept up to
CAP (> X) because run entries shrink numbers and can feed back below X.

Usage: python3 ladder_chunks.py [X] [CAP_FACTOR]
"""
import sys
from array import array

X = int(sys.argv[1]) if len(sys.argv) > 1 else 1 << 16
CAP = X * (int(sys.argv[2]) if len(sys.argv) > 2 else 256)

seen = bytearray(CAP + 1)


def ladder(v, out):
    while v <= CAP and not seen[v]:
        seen[v] = 1
        out.append(v)
        v = 4 * v - 1


frontier = array("q")
ladder(1, frontier)
covered = sum(1 for v in frontier if v <= X)
print(f"X = {X} (Collatz values up to {6*X-2}),  cap = {CAP}")
print(f"{'gen':>4} {'new nodes':>11} {'covered<=X':>11} {'fraction':>9}  smallest uncovered")
g = 0
while frontier:
    first_gap = next((n for n in range(1, X + 1) if not seen[n]), None)
    print(f"{g:>4} {len(frontier):>11} {covered:>11} {covered/X:>9.4f}  {first_gap}")
    nxt = array("q")
    for v in frontier:
        r = v % 3
        if r == 0:
            w = 2 * v // 3
            if not seen[w]:
                ladder(w, nxt)
        elif r == 1 and v > 1:
            w = (4 * v - 1) // 3
            if w <= CAP and not seen[w]:
                ladder(w, nxt)
    covered += sum(1 for v in nxt if v <= X)
    frontier = nxt
    g += 1

missing = [n for n in range(1, X + 1) if not seen[n]]
print(f"\nNot reached within cap: {len(missing)}  (first few: {missing[:10]})")
