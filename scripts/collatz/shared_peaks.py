# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 shared_peaks.py
"""Family size of each peak against the run length into it, and the check that a family is exactly the backward tree below the peak."""
import os
import sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collatz_link_sieve import hub_step
from collections import defaultdict, Counter
N=1<<20
fam=defaultdict(list); runk={}
for n in range(2,N):
    m=n;pk=n;run=0;rk=0
    while m!=1:
        m,t=hub_step(m); run=run+1 if t=='U' else 0
        if m>pk: pk=m; rk=run
    if pk>n: fam[pk].append(n); runk[pk]=rk
def v3(x):
    k=0
    while x%3==0: x//=3;k+=1
    return k
# family size vs run length into peak
by=defaultdict(list)
for p,L in fam.items(): by[min(runk[p],12)].append(len(L))
print("run k into peak: #peaks, mean family size, max")
for k in sorted(by): print(k,len(by[k]),round(sum(by[k])/len(by[k]),2),max(by[k]))
# basin prediction: count ancestors of P below P (backward tree), compare with family size for big families
def basin(P,limit=200000):
    st=[P];cnt=0;seen={P}
    while st:
        v=st.pop()
        for w in ([2*v//3] if v%3==0 else [])+([(4*v-1)//3] if v%3==1 and v>1 else [])+[4*v-1]:
            if w<P and w not in seen:
                seen.add(w); st.append(w); cnt+=1
                if cnt>limit: return cnt
    return cnt
big=sorted(fam.items(),key=lambda kv:-len(kv[1]))[:8]
print("\npeak(hub n), k, family size (n<2^20), full basin below P, basin members < 2^20")
for p,L in big:
    st=[p];seen={p};inr=0
    while st:
        v=st.pop()
        for w in ([2*v//3] if v%3==0 else [])+([(4*v-1)//3] if v%3==1 and v>1 else [])+[4*v-1]:
            if w<p and w not in seen: seen.add(w); st.append(w); inr+= w<N
    print(p,runk[p],len(L),len(seen)-1,inr)
