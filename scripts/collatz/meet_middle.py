"""
Meet in the middle on the hub n-map.

Backward: grow ladder-chunks from n = 1, recording the generation each node joins.
Forward:  take the sieve's open classes (problem areas, with mod-3, coalescence
          and pairing rules on) and push every member n <= X forward until it
          lands on a chunk node of generation <= G.

For each G, report how many forward loops the problem numbers need, so you can
see how the two sides share the distance.

Usage: python3 meet_middle.py [X] [K] [CAP_FACTOR]
"""
import sys
from array import array
import collatz_link_sieve as S

X = int(sys.argv[1]) if len(sys.argv) > 1 else 1 << 16
K = int(sys.argv[2]) if len(sys.argv) > 2 else 12
CAP = X * (int(sys.argv[3]) if len(sys.argv) > 3 else 256)

# ---------------------------------------------------------------- backward
gen = bytearray([255]) * (CAP + 1)          # 255 = not reached


def ladder(v, g, out):
    while v <= CAP and gen[v] == 255:
        gen[v] = min(g, 254)
        out.append(v)
        v = 4 * v - 1


frontier = array("q")
ladder(1, 0, frontier)
g = 0
while frontier:
    g += 1
    nxt = array("q")
    for v in frontier:
        r = v % 3
        if r == 0:
            ladder(2 * v // 3, g, nxt)
        elif r == 1 and v > 1:
            w = (4 * v - 1) // 3
            if w <= CAP:
                ladder(w, g, nxt)
    frontier = nxt
maxgen = g - 1

# ----------------------------------------------------------- problem areas
rules = [S.rule_mod3_entry, S.rule_half_pair]
open_cls, M = [0, 1, 2], 3
for k in range(K + 1):
    keep = []
    for a in open_cls:
        if any(r(a, M) for r in rules):
            continue
        if S.run_class(a, M, True, True)[0] == "open":
            keep.append(a)
    if k == K:
        open_cls = keep
        break
    open_cls = [x for a in keep for x in (a, a + M)]
    M *= 2
problem = [n for a in open_cls for n in range(a if a else M, X + 1, M)]

# ---------------------------------------------------------------- forward


def in_chunk(v, G):
    return v <= CAP and gen[v] <= G


def forward_to(n, G, boost=False, limit=100000):
    """Loops until n's path provably joins a chunk of generation <= G.
    boost=True adds two checks that reach past the cap at the climbers' peaks:
      run walk-back : v = 0 mod 3 sits inside a run; walk the run back
                      (v -> 2v/3 -> ...) to its smaller entries
      exit pairing  : a run from w that exits by the x0.25 loop merges one
                      loop later with the run from w/2
    RESULT: these add nothing here. A chunk node's whole path to 1 already
    lies under the cap, so any merge partner in a chunk implies the merge
    point is in the chunk too. The climbers are limited by their peak."""
    run_start = None
    prev_even = False
    for s in range(limit):
        if in_chunk(n, G):
            return s
        if boost:
            u = n
            while u % 3 == 0 and u > 1:
                u = 2 * u // 3
                if in_chunk(u, G):
                    return s
            if n % 2 == 1 and n % 4 == 3 and run_start and run_start % 2 == 0:
                if in_chunk(run_start // 2, G):
                    return s + 1        # merge point is one loop ahead
        if n % 2 == 0:
            if not prev_even:
                run_start = n
            prev_even = True
        else:
            prev_even = False
            run_start = run_start if run_start else None
        n_next, t = S.hub_step(n)
        if t != "U" and not prev_even:
            run_start = None
        n = n_next
    return None


print(f"Hub n <= {X} (Collatz <= {6*X-2}); chunk cap {CAP}; chunks fill by gen {maxgen}")
print(f"Problem areas: {len(open_cls)} open classes mod {M} "
      f"({len(open_cls)/M:.2%}), {len(problem)} numbers <= X\n")
for boost in (False, True):
    print("WITH peak linking (run walk-back + exit pairing)" if boost else "PLAIN meet")
    print(f"{'G':>4} {'chunk<=X':>9} {'max fwd':>8} {'mean fwd':>9} {'99% fwd':>8} {'max G+fwd':>10}  hardest n")
    for G in [0, 10, 20, 30, 40, 50, 60, 80, 100, maxgen]:
        steps = [(forward_to(n, G, boost), n) for n in problem]
        vals = sorted(s for s, _ in steps)
        worst = max(steps)
        inX = sum(1 for n in range(1, X + 1) if gen[n] <= G)
        print(f"{G:>4} {inX/X:>9.2%} {worst[0]:>8} {sum(vals)/len(vals):>9.1f} "
              f"{vals[int(.99*len(vals))]:>8} {G+worst[0]:>10}  {worst[1]}")
    print()
