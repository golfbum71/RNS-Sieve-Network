# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 climber_profile.py
"""Profile of the 2,000 highest climbers among hub n from 1,024 to 2^20 against all n: residues of n, peak residues, run into the peak, shared peaks, peak timing."""
import os
import math, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collatz_link_sieve import hub_step
from collections import Counter
N=1<<20
rows=[]
for n in range(2,N):
    m=n;pk=n;i=0;ipk=0;prev=None;run=0;runpk=0;tp=''
    seq=[]
    while m!=1:
        m2,t=hub_step(m)
        run = run+1 if t=='U' else 0
        m=m2;i+=1
        if m>pk: pk=m;ipk=i;runpk=run
    rows.append((math.log(pk)/math.log(n),n,pk,ipk,i,runpk))
rows.sort(reverse=True)
top=[r for r in rows if r[1]>=1024][:2000]   # top climbers, n>=1024
allr=[r for r in rows if r[1]>=1024]
def dist(f,R): 
    c=Counter(f(r) for r in R); t=len(R); return {k:round(v/t,3) for k,v in sorted(c.items())}
def v2(x):
    k=0
    while x%2==0: x//=2;k+=1
    return k
print("exp range top:",round(top[-1][0],3),"-",round(top[0][0],3))
for name,f in [("n mod 3",lambda r:r[1]%3),("n mod 4",lambda r:r[1]%4),("n mod 16",lambda r:r[1]%16),
               ("v2(n) capped 4",lambda r:min(v2(r[1]),4)),
               ("peak mod 4",lambda r:r[2]%4),("peak mod 9",lambda r:r[2]%9),("run length into peak (cap 6)",lambda r:min(r[5],6))]:
    print(name,"\n  top:",dist(f,top),"\n  all:",dist(f,allr))
pc=Counter(r[2] for r in top)
print("distinct peaks among top 2000:",len(pc)); print("most shared peaks (hub n, Collatz value, count):",[(p,6*p-2,c) for p,c in pc.most_common(8)])
print("peak position as fraction of path: top",round(sum(r[3]/r[4] for r in top)/len(top),3),"all",round(sum(r[3]/r[4] for r in allr)/len(allr),3))
print("path length: top",round(sum(r[4] for r in top)/len(top),1),"all",round(sum(r[4] for r in allr)/len(allr),1))
# trailing ones in binary of original odd x=2n-1
def t1(x):
    k=0
    while x&1: x>>=1;k+=1
    return k
print("trailing 1-bits of odd x=2n-1: top",dist(lambda r:min(t1(2*r[1]-1),8),top),"\n  all",dist(lambda r:min(t1(2*r[1]-1),8),allr))
