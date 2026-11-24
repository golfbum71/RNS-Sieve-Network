# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 doubling_chain.py
"""Do the exit-pair merge points of one doubling chain (m, 2m, 4m, ...) meet quickly? (They do not: no bound.)"""
import os
import sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collatz_link_sieve import hub_step
def traj(n,lim=100000):
    d={};i=0
    while n not in d and i<lim:
        d[n]=i; n,_=hub_step(n); i+=1
    return d
def merge(a,b):
    da=traj(a); n=b;i=0
    while n not in da: n,_=hub_step(n); i+=1
    return n,da[n],i
# For odd m, chain 2^k m: where does member k merge with member k+2 (the next pair)?
import statistics
for m in [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31]:
    row=[]
    for k in range(1,12):
        v,ia,ib=merge(2**k*m,2**(k+2)*m)
        row.append(f"{ia-(k)}/{ib-(k+2)}")  # loops after each run ends
    print(m,row)
