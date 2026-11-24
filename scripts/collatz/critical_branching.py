# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 critical_branching.py
"""The critical exponent: tree size divided by room stays flat (exponent exactly 1), and the deepest member drags a tree proportional to its room."""
import math, random
def subtree(v,B,cap=5_000_000):
    seen={v};st=[v]
    while st:
        u=st.pop()
        ps=[4*u-1]+([2*u//3] if u%3==0 else [])+([(4*u-1)//3] if u%3==1 and u>1 else [])
        for w in ps:
            if w<B and w not in seen:
                seen.add(w);st.append(w)
                if len(seen)>cap: return None
    return len(seen)
# solve exponent equation (3/2)^s = 3(1-2^-s)
f=lambda s:(1.5)**s-3*(1-2**-s)
print("exponent eq at s=1:",f(1.0), " s=0.9:",round(f(0.9),4)," s=1.1:",round(f(1.1),4))
random.seed(5)
print("\nroom x = B/v : mean subtree size / x   (v random ~2^40, 300 samples each)")
for lx in range(4,18,2):
    x=2**lx; tot=0
    for _ in range(300):
        v=random.randrange(1<<39,1<<40)
        tot+=subtree(v,v*x)
    print(f"  x=2^{lx:<3} mean size {tot/300:>12.1f}   size/x = {tot/300/x:.4f}")
# deepest-member check on deep funnels
print("\nDeep funnels: subtree of smallest member m (below P) vs room P/m")
for P,m in [(2867062959,79744),(4108012983,135136),(261804123,38836),(1358937,2296),(17726337,13312),(212823,910),(1539,14)]:
    s=subtree(m,P); F=subtree(P,P)
    print(f"  P={P:<11} m={m:<7} P/m={P/m:>9.0f}  subtree(m)={s:>7}  ratio={s/(P/m):.3f}  funnel={F-1}  funnel/(P/m)={(F-1)/(P/m):.3f}")
