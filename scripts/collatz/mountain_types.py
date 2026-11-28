"""Mountain types (notes section 28): every odd number below 2^22 is grouped by the
shape of its trip to the tide (climbs and drops). Prints the steps to the tide for
each count of odd steps, the number of shapes (OEIS A100982), and each shape with
the binary ending that produces it."""
import collections, math
def run(x):
    v=x; u=k=c=0; word=""
    while v>=x:
        if v%2: v=3*v+1; u+=1; c=3*c+2**k; word+="u"
        else: v//=2; k+=1; word+="d"
    return u,k,c,word
LIM=2**22
byu=collections.defaultdict(set); bad=0
for x in range(3,LIM,2):
    u,k,c,w=run(x)
    if k!=math.floor(u*math.log2(3))+1: bad+=1
    byu[u].add((w,(-c*pow(3,-u,2**k))%2**k,k))
print("tides not at the balance point:",bad)
for u in range(1,11): print(u, "steps", u+math.floor(u*math.log2(3))+1, "shapes", len(byu[u]))
def pretty(w):
    # turn word into blocks "climb j, drop d"
    out=[];i=0
    while i<len(w):
        j=0
        while i<len(w) and w[i]=="u":
            j+=1;i+=1
            if i<len(w) and w[i]=="d" and (i+1>=len(w) or w[i+1]=="u"): i+=1  # single halving: climb continues
            else: break
        d=0
        while i<len(w) and w[i]=="d": d+=1;i+=1
        out.append(f"{j}↑{d}↓")
    return " ".join(out)
for u in range(2,6):
    for w,r,k in sorted(byu[u],key=lambda t:t[1]):
        print(u, pretty(w), "ends", format(r,f"0{k}b"))
