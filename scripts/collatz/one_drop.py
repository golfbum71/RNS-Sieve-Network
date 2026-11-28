"""One-drop mountains (notes section 27).

x = 2^j * m - 1 (m odd, j trailing ones) climbs to 3^j * m - 1. Let h be the
fewest halvings with 3^j < 2^(j+h). Then x meets the tide (drops below
itself) in one drop, after exactly 2j + h steps, exactly when the last h
binary digits of m are those of the 2-adic number 1/3^j. After its first
digit those repeat with period 2 * 3^(j-1). Checks both directions for many m.
"""
def col(v): return v // 2 if v % 2 == 0 else 3 * v + 1

def tide(x):
    v, s = x, 0
    while v >= x: v = col(v); s += 1
    return s, v

def two_adic(q, digits):            # last `digits` binary digits of 1/q, q odd
    return pow(q, -1, 2 ** digits)

print(" j   h  digits m must end in   digits of 1/3^j repeat every")
for j in range(1, 15):
    h = next(h for h in range(60) if 3 ** j < 2 ** (j + h))
    r = two_adic(3 ** j, h)
    bad = 0
    for m in range(1, 6000, 2):
        x = 2 ** j * m - 1
        if x < 3: continue
        s, v = tide(x)
        one = s == 2 * j + h
        big = (2 ** (j + h) - 3 ** j) * m >= 2 ** h
        if big and (one != (m % 2 ** h == r)): bad += 1
        if one and v != (3 ** j * m - 1) // 2 ** h: bad += 1
    period = 2 * 3 ** (j - 1)
    print(f"{j:2} {h:3}  {format(r, f'0{h}b'):>18}   {period:8}   failures: {bad}")
