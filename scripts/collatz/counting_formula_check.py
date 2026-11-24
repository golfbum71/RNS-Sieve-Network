# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 counting_formula_check.py
"""The exact ladder-sum counting formula checked against brute-force tree counts."""
import sys
sys.setrecursionlimit(100000)
def T(v,B):
    """Exact count of the backward tree of v below B, by ladders.
    Rungs: r_i = 4^i (v - 1/3) + 1/3 = (4^i (3v-1) + 1)/3, residue r_i = v - i (mod 3)."""
    total=0
    i=0
    while True:
        r=(4**i*(3*v-1)+1)//3
        if r>=B: break
        total+=1
        if r%3==0: total+=T(2*r//3,B)
        elif r%3==1:
            c=(4*r-1)//3
            if c<B: total+=T(c,B)
        i+=1
    return total
def brute(v,B):
    seen={v};st=[v]
    while st:
        u=st.pop()
        for w in [4*u-1]+([2*u//3] if u%3==0 else [])+([(4*u-1)//3] if u%3==1 else []):
            if w<B and w not in seen: seen.add(w);st.append(w)
    return len(seen)
import random; random.seed(1)
ok=0
for _ in range(300):
    v=random.randrange(10**6,10**9); B=v*random.choice([16,256,4096])
    ok+= T(v,B)==brute(v,B)
print("formula matches brute force:",ok,"/300")
for P in [4108012983,2867062959,20168811]:
    F=T(2*P//3,P)
    print(P, "funnel via formula:",F)
