# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 glide_bits.py
"""How long climbs last in loops and in bits used, against the bits of the start (worst ratios up to 2^21)."""
import math
def step(n):
    if n%2==0: return 3*n//2,'U',2
    if n%4==1: return (3*n+1)//4,'D75',2
    return (n+1)//4,'D25',2
# bits consumed: U=1, drops=2
def glide(n0):
    n=n0; bits=0; loops=0; pat=[]
    while True:
        m,t,_=step(n); bits+= 1 if t=='U' else 2; loops+=1; pat.append(t); n=m
        if n<n0: return loops,bits,pat
best=[]
for n0 in range(2,2_000_000):
    l,b,p=glide(n0)
    r=b/math.log2(n0)
    best.append((r,n0,l,b))
best.sort(reverse=True)
for r,n0,l,b in best[:8]: print(n0,6*n0-2,l,b,round(math.log2(n0),1),round(r,1))
# worst-case 1.125 block chains: max consecutive (U,D75) pairs
