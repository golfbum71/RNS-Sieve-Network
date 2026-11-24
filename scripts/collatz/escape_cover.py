# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md).
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 escape_cover.py
"""Do the branches of 1's tree cover the places the digits force an escape to go?

1. Grow the chunk of 1's tree below a cap C backward from 1 with the three
   linking rules (ladder 4v-1, run entry 2v/3, branch entry (4v-1)/3).
2. Take the linking sieve's open classes at depth K (the only places a smallest
   runaway could hide) and their members up to X.
3. For each member, follow only the loops its residue FORCES (the class's known
   prefix: the loops decided by the digits the class fixes), and ask whether
   that forced stretch touches the chunk of 1's tree.

If the covered share heads to 100% as K grows, the branches of 1 are sitting on
the forced escape routes.
"""
import sys
from array import array
import collatz_link_sieve as S

C = 1 << int(sys.argv[1]) if len(sys.argv) > 1 else 1 << 24
X = 1 << int(sys.argv[2]) if len(sys.argv) > 2 else 1 << 20

inchunk = bytearray(C + 1)
stack = array("q", [1])
inchunk[1] = 1
while stack:
    v = stack.pop()
    for w in ([4 * v - 1] + ([2 * v // 3] if v % 3 == 0 else [])
              + ([(4 * v - 1) // 3] if v % 3 == 1 and v > 1 else [])):
        if w <= C and not inchunk[w]:
            inchunk[w] = 1
            stack.append(w)
print(f"chunk of 1's tree below 2^{C.bit_length() - 1}: {sum(inchunk)} values")

rules = [S.rule_mod3_entry, S.rule_half_pair]
open_cls, M = [0, 1, 2], 3
print(f"{'depth':>5} {'open classes':>12} {'members<=X':>10} {'forced loops':>12} "
      f"{'covered in forced stretch':>26} {'escape above cap':>16}")
for K in range(0, 21):
    keep = []
    for a in open_cls:
        if any(r(a, M) for r in rules):
            continue
        if S.run_class(a, M, True, True)[0] == "open":
            keep.append(a)
    if K >= 8 and K % 2 == 0:
        mem = cov = above = 0
        loops = 0
        for a in keep:
            L = len(S.run_class(a, M)[1])          # loops forced by the class
            for n in range(a if a else M, X + 1, M):
                mem += 1
                loops += L
                v, hit, hi = n, False, False
                for _ in range(L + 1):
                    if v > C:
                        hi = True
                    elif inchunk[v]:
                        hit = True
                        break
                    v, _ = S.hub_step(v)
                cov += hit
                above += (not hit) and hi
        print(f"{K:>5} {len(keep):>12} {mem:>10} {loops / max(1, mem):>12.1f} "
              f"{cov / max(1, mem):>26.2%} {above / max(1, mem):>16.2%}")
    open_cls = [x for a in keep for x in (a, a + M)]
    M *= 2
