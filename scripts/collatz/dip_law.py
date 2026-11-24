# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 dip_law.py
"""How far backward trees dip below their root: about 4x rarer per extra bit, independent of room."""
import random, math
def dip(v,B):
    seen={v};st=[v];lo=v
    while st:
        u=st.pop()
        ps=[4*u-1]+([2*u//3] if u%3==0 else [])+([(4*u-1)//3] if u%3==1 else [])
        for w in ps:
            if w<B and w not in seen:
                seen.add(w);st.append(w)
                if w<lo: lo=w
    return math.log2(v/lo), len(seen)
random.seed(4)
for lr,N in ((8,6000),(10,4000),(12,2000)):
    R=2**lr; ds=[]; 
    for _ in range(N):
        v=random.randrange(1<<39,1<<40); d,s=dip(v,v*R); ds.append((d,s/R))
    line=[]
    for t in (1,2,3,4,5,6,7,8):
        line.append(f"{sum(d>=t for d,_ in ds)/N:.4f}")
    # C conditional on dip
    import statistics
    lo=[c for d,c in ds if d<1]; hi=[c for d,c in ds if d>=3]
    print(f"room 2^{lr}: P(dip>=1..8) =",line, f"| mean C dip<1: {statistics.mean(lo):.2f}, dip>=3: {statistics.mean(hi):.2f}")
