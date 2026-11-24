# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 mountain_slope.py
"""Climbers per one-bit band below a peak: average peaks and the giant mountains (halving per bit)."""
import math, random
def members(P,cap=3_000_000):
    seen={P};st=[P]
    while st:
        v=st.pop()
        ps=[4*v-1]+([2*v//3] if v%3==0 else [])+([(4*v-1)//3] if v%3==1 else [])
        for w in ps:
            if w<P and w not in seen: seen.add(w);st.append(w)
    seen.discard(P); return seen
def profile(P,J=20):
    prof=[0]*J
    for w in members(P):
        j=int(math.log2(P/w))
        if j<J: prof[j]+=1
    return prof
random.seed(8)
J=14
for b in (24,32,40):
    tot=[0]*J; N=4000
    for _ in range(N):
        P=6*random.randrange((1<<(b-1))//6,(1<<b)//6)+3
        pr=profile(P,J)
        for j in range(J): tot[j]+=pr[j]
    avg=[t/N for t in tot]
    print(f"random peaks ~2^{b}: avg climbers per depth band j (P/2^(j+1)..P/2^j):")
    print("   "+"  ".join(f"{a:.4f}" for a in avg[:9]))
    print("   ratio band j/j+1:","  ".join(f"{avg[j]/avg[j+1]:.2f}" for j in range(7) if avg[j+1]>0))
print("\nGiant funnels (members per depth band):")
for P in [2867062959,4108012983,413685225,261804123,20168811,1358937]:
    pr=profile(P,20)
    last=max(j for j in range(20) if pr[j])
    print(f"  P={P:<11}", pr[:last+1])
