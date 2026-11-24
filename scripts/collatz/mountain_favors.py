# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 mountain_favors.py
"""Rising tide with credit: each index is credited to the earlier path it first links into; links per path-owner grouped by how high the owner climbed."""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collatz_link_sieve import hub_step
from collections import Counter
N=1<<20
owner={1:1}; climb={1:1.0}; credit=Counter()
for X in range(2,N+1):
    if X in owner:
        credit[owner[X]]+=1; continue
    n=X; hi=X; new=[X]
    while n not in owner:
        n,_=hub_step(n); hi=max(hi,n); new.append(n)
    credit[owner[n]]+=1
    for w in new[:-1]: owner[w]=X
    climb[X]=hi/X
tot=N-1
bands=[(1,2),(2,8),(8,64),(64,1024),(1024,10**9)]
print("owners grouped by how high their own climb went (x their start):")
for lo,hi in bands:
    own=[o for o in climb if lo<=climb[o]<hi]
    got=sum(credit[o] for o in own)
    print(f"  climb {lo}-{hi if hi<10**9 else 'up'}x: {len(own):>7} path-owners, link {got:>7} indices ({got/tot:.1%}), {got/max(1,len(own)):.2f} each")
print("top path-owners:", [(o, credit[o], round(climb[o])) for o,_ in credit.most_common(8)])
