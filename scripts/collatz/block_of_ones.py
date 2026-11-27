"""Blocks of ones in the row number (notes section 25).

A 6n+1 number whose row n ends in a 0 then L binary ones is handed down
three ones at a time (five steps each, n + 1 grows by 9/8), then finishes
with a fixed drop. Checks the hand-off formula and which block lengths
always end below the start, then checks every settled number up to a limit
against its real path.
"""
import random

def col(x): return x // 2 if x % 2 == 0 else 3 * x + 1

def info(x):
    n = (x - 1) // 6
    L = 0
    while (n + 1) >> L & 1 == 0: L += 1
    m = (n + 1) >> L
    t, left = L // 3, L % 3
    nt = 9 ** t * m * 2 ** left - 1
    d = (27 * nt + 7) // 8 if left == 2 else (9 * nt + 2) // 2 if left == 0 else None
    return L, t, nt, d

random.seed(1)
print("block  hand-offs  ones left  always below start?")
for L in range(2, 30):
    ok = True
    for _ in range(2000):
        m = 2 * random.randrange(1, 10 ** 15) + 1
        x = 6 * (2 ** L * m - 1) + 1
        _, t, nt, d = info(x)
        y = x
        for _ in range(5 * t): y = col(y)
        assert y == 6 * nt + 1          # the hand-off chain
        if d is None or d >= x: ok = False
    print(f"{L:5}  {L // 3:9}  {L % 3:9}  {'yes' if ok else 'no'}")

LIMIT, hit = 3_000_000, 0
for x in range(7, LIMIT, 6):
    n = (x - 1) // 6
    if n % 2 == 0: continue
    L, t, nt, d = info(x)
    if L not in (2, 3, 5, 6, 8, 11, 14): continue
    v = x
    while v != d: v = col(v)
    assert d < x
    hit += 1
print(f"settled below {LIMIT:,}: {hit:,}, all reach the predicted value below their start")
