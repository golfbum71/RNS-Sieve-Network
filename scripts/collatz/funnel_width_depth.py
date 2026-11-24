# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 funnel_width_depth.py
"""Funnel depth (bits below the peak) against funnel width, over about 255,000 funnels."""
import os
import sys, math, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from funnels import funnel
random.seed(2)
peaks=list(range(3,1<<20,6))
for b in (24,28,32,36,40):
    peaks += [6*random.randrange((1<<(b-1))//6,(1<<b)//6)+3 for _ in range(3000)]
peaks += [413685225,98879859,466387227,4108012983,261804123,20168811,17726337,2867062959,1135023,1358937,1605987]
rows=[]
for P in peaks:
    lo,S,done=funnel(P)
    if S>=1 and lo<P:
        rows.append((math.log2(S),math.log2(P/lo),P,lo,S))
# envelope: max depth for each size band
from collections import defaultdict
band=defaultdict(list)
for ls,d,P,lo,S in rows: band[int(ls)].append((d,P,lo,S))
print("log2(size) band | #funnels | max depth log2(P/min) | ratio maxdepth/log2size | avg depth")
for k in sorted(band):
    v=band[k]; md=max(v)
    print(f"{k:>3} {len(v):>7} {md[0]:>8.2f} {md[0]/max(k,1):>8.2f} {sum(x[0] for x in v)/len(v):>8.2f}   P={md[1]} min={md[2]} S={md[3]}")
# least squares on all
n=len(rows); mx=sum(r[0] for r in rows)/n; my=sum(r[1] for r in rows)/n
b=sum((r[0]-mx)*(r[1]-my) for r in rows)/sum((r[0]-mx)**2 for r in rows)
print("fit depth ~ %.2f + %.2f*log2(size)"%(my-b*mx,b))
# size vs P: how big can funnels be
print("max log2(S)/log2(P) among P>2^16:", max((r[0]/math.log2(r[2]),r[2]) for r in rows if r[2]>1<<16))
