"""
Chasing the tail: how many exact ternary digits does it take for model trees
to match the giants in real Collatz trees?

Model BJ tracks every node's residue mod 3^J exactly:
    ladder     4u - 1      exact mod 3^J (no digit lost)
    run entry  2u/3        divides by 3 -> loses the top digit, refilled at random
    d entry    (4u - 1)/3  same
Positions are tracked in log2 (4u-1 ~ 4u). J = 1 is the exact ladder cycle with
pairing (MODEL B before); larger J adds exact digits. REAL uses true integers.
"""
import math
import random

ROOM = 2 ** 10
TOP = math.log2(ROOM)
SAMPLES = 10000
CAP = 400_000
L23, L43 = math.log2(2 / 3), math.log2(4 / 3)


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


def model_tree(J):
    mod = 3 ** J
    top_digit = 3 ** (J - 1)
    count = 0
    stack = [(0.0, random.randrange(mod))]
    while stack:
        p, r = stack.pop()
        while p < TOP:
            count += 1
            if count > CAP:
                return count
            if r % 3 == 0:
                c = (2 * (r // 3)) % top_digit + top_digit * random.randrange(3)
                stack.append((p + L23, c))
            elif r % 3 == 1 and p + L43 < TOP:
                c = ((4 * r - 1) // 3) % top_digit + top_digit * random.randrange(3)
                stack.append((p + L43, c))
            p += 2.0
            r = (4 * r - 1) % mod
    return count


def row(name, sizes):
    C = sorted(s / ROOM for s in sizes)
    n = len(C)
    q = lambda f: C[int(f * (n - 1))]
    tail = lambda t: sum(c > t for c in C) / n
    print(f"{name:<8} median {q(.5):5.2f}  90% {q(.9):5.2f}  99% {q(.99):6.2f}  "
          f"99.9% {q(.999):7.2f}   C>10 {tail(10):6.2%}  C>30 {tail(30):6.2%}  C>100 {tail(100):6.3%}")


if __name__ == "__main__":
    random.seed(3)
    row("REAL", [real_tree(random.randrange(1 << 39, 1 << 40)) for _ in range(SAMPLES)])
    for J in (1, 2, 3, 4, 6, 8):
        row(f"B{J}", [model_tree(J) for _ in range(SAMPLES)])
