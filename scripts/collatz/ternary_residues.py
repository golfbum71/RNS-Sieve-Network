# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 ternary_residues.py
"""What drives the branching constant C: residues mod 2^j explain nothing, residues mod 3^j more and more; C by factors of 3; the tail."""
import random, math
from collections import defaultdict
def subtree(v,B):
    seen={v};st=[v]
    while st:
        u=st.pop()
        ps=[4*u-1]+([2*u//3] if u%3==0 else [])+([(4*u-1)//3] if u%3==1 and u>1 else [])
        for w in ps:
            if w<B and w not in seen: seen.add(w);st.append(w)
    return len(seen)
random.seed(7)
X=2**10; N=12000
data=[]
for _ in range(N):
    v=random.randrange(1<<39,1<<40)
    data.append((v,subtree(v,v*X)/X))
allC=[c for _,c in data]; mu=sum(allC)/N; var=sum((c-mu)**2 for c in allC)/N
print(f"room 2^10, {N} random v: mean C {mu:.3f}, sd {var**.5:.3f}, max {max(allC):.2f}")
def explain(key,name):
    g=defaultdict(list)
    for v,c in data: g[key(v)].append(c)
    between=sum(len(L)*(sum(L)/len(L)-mu)**2 for L in g.values())/N
    return between/var, g
for name,key in [("v mod 2",lambda v:v%2),("v mod 4",lambda v:v%4),("v mod 16",lambda v:v%16),
                 ("v mod 3",lambda v:v%3),("v mod 9",lambda v:v%9),("v mod 27",lambda v:v%27),("v mod 81",lambda v:v%81),("v mod 243",lambda v:v%243)]:
    r,g=explain(key,name)
    top=sorted(((sum(L)/len(L),k) for k,L in g.items()),reverse=True)
    print(f"{name:>10}: explains {r:6.1%} of variation   best class {top[0][1]} (C={top[0][0]:.2f})  worst {top[-1][1]} (C={top[-1][0]:.2f})")
r,g=explain(lambda v:v%3,"")
for k in range(3): print("  v≡%d mod 3: mean C %.3f"%(k,sum(g[k])/len(g[k])))

def tern(v,k=10):
    d=[]
    for _ in range(k): d.append(str(v%3)); v//=3
    return ''.join(reversed(d))
def v3(v):
    k=0
    while v%3==0: v//=3;k+=1
    return k
def mintree(v,B):
    seen={v};st=[v];lo=v
    while st:
        u=st.pop()
        ps=[4*u-1]+([2*u//3] if u%3==0 else [])+([(4*u-1)//3] if u%3==1 and u>1 else [])
        for w in ps:
            if w<B and w not in seen: seen.add(w);st.append(w);lo=min(lo,w)
    return lo
print("\nTop outliers: C, last 10 ternary digits of v, smallest node / v")
for v,c in sorted(data,key=lambda t:-t[1])[:8]:
    print(f"  C={c:8.2f}  ...{tern(v)}  v3={v3(v)}  depth below v: 2^{math.log2(v/mintree(v,v*X)):.1f}")
# tail
cs=sorted(allC,reverse=True)
print("\nTail P(C>c):", [(c,round(sum(x>c for x in allC)/N,4)) for c in (3,10,30,100,300)])
# grouped by v3
g=defaultdict(list)
for v,c in data: g[min(v3(v),5)].append(c)
print("mean C by number of factors of 3 in v:",{k:round(sum(L)/len(L),2) for k,L in sorted(g.items())})
