# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 interval_owners.py
"""Every number between a trunk run's start and its peak, classified by its own highest point: this peak, higher peaks, lower peaks, or its own peak."""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collatz_link_sieve import hub_step
def v3(x):
    k=0
    while x%3==0: x//=3;k+=1
    return k
def peak(n):
    pk=n
    while n!=1:
        n,_=hub_step(n)
        if n>pk: pk=n
    return pk
for P,k in [(1358937,4),(212823,2),(1605987,6)]:
    m=P//3**k; w=2**k*m
    assert 3**k*m==P and hub_step(w)[0]==3*w//2
    tot=0; mine=0; higher=0; lower=0; own=0
    for n in range(w,P+1):
        pk=peak(n); tot+=1
        if pk==P: mine+=1
        elif pk>P: higher+=1
        else:
            lower+=1
            if pk==n: own+=1
    print(f"peak {P} (run of {k} from {w}): {tot} numbers in between")
    print(f"   climb to this peak: {mine} ({mine/tot:.3%})  belong to higher peaks: {higher} ({higher/tot:.1%})  to lower peaks: {lower} ({lower/tot:.1%}), of which are their own peak: {own} ({own/tot:.1%})")
