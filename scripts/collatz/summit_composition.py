# Part of the CollatzHub notes (docs/COLLATZ_NOTES.md), session of 2026-11-24.
# Copyright (c) 2026 Geoffrey Fischer. Apache 2.0. Run from this folder: python3 summit_composition.py
"""Which loop each mountain member takes, band by band, and the share in exit pairs (x, 2x)."""
import math
def members(P):
    seen={P};st=[P]
    while st:
        v=st.pop()
        ps=[4*v-1]+([2*v//3] if v%3==0 else [])+([(4*v-1)//3] if v%3==1 else [])
        for w in ps:
            if w<P and w not in seen: seen.add(w);st.append(w)
    seen.discard(P); return seen
def kind(u):  # forward loop taken by u
    return 'U' if u%2==0 else ('d' if u%4==1 else 'D')
for P in [4108012983,2867062959,413685225,20168811,1358937]:
    S=members(P); J=10
    print(f"\nP={P}  funnel size {len(S)}")
    print(" band | members |  run(U)  d-branch  ladder(D) | in a pair (x,2x) | top-of-run members")
    for j in range(J):
        B=[u for u in S if int(math.log2(P/u))==j]
        if not B: break
        k={'U':0,'d':0,'D':0}
        for u in B: k[kind(u)]+=1
        paired=sum(1 for u in B if (kind(u)=='d' and 2*u in S) or (u%2==0 and kind(u//2)=='d' and u//2 in S))
        print(f" {j:>4} | {len(B):>7} | {k['U']/len(B):6.1%} {k['d']/len(B):8.1%} {k['D']/len(B):9.1%} | {paired/len(B):14.1%} |")
    # overall pairing coverage
    tot=sum(1 for u in S if (kind(u)=='d' and 2*u in S) or (u%2==0 and kind(u//2)=='d' and u//2 in S))
    print(f" overall share in a pair: {tot/len(S):.1%}")
