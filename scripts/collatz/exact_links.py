"""
Bringing the exact links back: which of them make real Collatz trees narrower
than random branching models?

Backward rules on the hub n-map (room = ceiling / root):
    ladder     u <- 4u - 1                    every rung
    run entry  u <- 2u/3        if u = 0 mod 3  (goes down)
    d entry    u <- (4u - 1)/3  if u = 1 mod 3  (goes up)

Exact facts in the linking framework:
  * Ladder cycle: 4u - 1 = u - 1 (mod 3), so rung residues cycle r, r-1, r-2.
  * Pairing = ladder cycle: if rung M = 1 mod 3 opens a d entry x = (4M-1)/3,
    the next rung 4M - 1 = 0 mod 3 opens a run entry 2(4M-1)/3 = 2x.
    The siblings x and 2x are exactly the run-exit pair (n, 2n).

Three trees are compared on C = tree size / room:
  REAL     exact integers
  MODEL A  every rung gets an independent random residue mod 3 (no exact links)
  MODEL B  rung residues follow the exact ladder cycle (so pairing is exact);
           each new branch starts with a random residue
  MODEL B9 like B, but each new branch's residue is computed exactly from the
           parent's residue mod 9 (one more ternary digit of exactness)
  Model positions use 4u-1 ~ 4u etc.; room is measured in log2.
"""
import math
import random
import statistics as st

ROOM = 2 ** 10
SAMPLES = 4000
CAP = 400_000
random.seed(11)


def real_tree(v):
    B = v * ROOM
    seen = {v}
    stack = [v]
    while stack:
        u = stack.pop()
        preds = [4 * u - 1]
        if u % 3 == 0:
            preds.append(2 * u // 3)
        elif u % 3 == 1:
            preds.append((4 * u - 1) // 3)
        for w in preds:
            if w < B and w not in seen:
                seen.add(w)
                stack.append(w)
                if len(seen) > CAP:
                    return len(seen)
    return len(seen)


def model_tree(mode):
    """Log-scale model. Node = (log2 size relative to root, residue info)."""
    top = math.log2(ROOM)
    count = 0
    # state: (position, residue mod 3, residue mod 9 or None)
    v9 = random.randrange(9)
    stack = [(0.0, v9 % 3, v9)]
    while stack:
        pos, r, r9 = stack.pop()
        # walk this node's ladder
        p = pos
        rr, rr9 = r, r9
        while p < top:
            count += 1
            if count > CAP:
                return count
            res = random.randrange(3) if mode == "A" else rr
            if res == 0:
                child = p + math.log2(2 / 3)
                if mode == "B9":
                    c3 = (2 * (rr9 // 3)) % 3          # exact from u mod 9
                    c9 = c3 + 3 * random.randrange(3)  # next digit unknown
                    stack.append((child, c3, c9))
                else:
                    stack.append((child, random.randrange(3), None))
            elif res == 1:
                child = p + math.log2(4 / 3)
                if child < top:
                    if mode == "B9":
                        c3 = (rr9 // 3 + 1) % 3            # (4u-1)/3 = 4q+1, exact from u mod 9
                        c9 = c3 + 3 * random.randrange(3)  # next digit unknown
                        stack.append((child, c3, c9))
                    else:
                        stack.append((child, random.randrange(3), None))
            # next rung: 4u - 1
            p += 2.0
            if mode != "A":
                rr = (rr - 1) % 3
                if rr9 is not None:
                    rr9 = (4 * rr9 - 1) % 9
    return count


def summarize(name, sizes):
    C = sorted(s / ROOM for s in sizes)
    n = len(C)
    q = lambda f: C[int(f * (n - 1))]
    print(f"{name:<9} mean {st.mean(C):6.2f}   sd {st.pstdev(C):7.2f}   "
          f"median {q(.5):5.2f}   90% {q(.9):6.2f}   99% {q(.99):7.2f}   "
          f"P(C>10) {sum(c > 10 for c in C)/n:6.2%}   P(C=0~) {sum(c < .05 for c in C)/n:5.1%}")


real = [real_tree(random.randrange(1 << 39, 1 << 40)) for _ in range(SAMPLES)]
summarize("REAL", real)
for mode in ("A", "B", "B9"):
    summarize("MODEL " + mode, [model_tree(mode) for _ in range(SAMPLES)])
