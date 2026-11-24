"""
Collatz linking sieve on the hub map (Geo's 6n-2 framework).

Every hub number is h = 6n - 2. Following h until it returns to the hub
gives three loops, chosen by n:

    n even        -> 3n/2       (U : the 6n-1 "bad" loop,     x1.5 )
    n = 1 mod 4   -> (3n+1)/4   (d : 6n+2 -> 6n+1 loop,       x0.75)
    n = 3 mod 4   -> (n+1)/4    (D : 6n+2 double-divide loop, x0.25)

Conjecture in this form: every positive n reaches the fixed point n = 1.

The sieve tracks a whole residue class  n = M*t + a  (t >= 1) symbolically
as  alpha*t + beta.  A class is:
    DOWN   - every member provably drops below its start (block pattern
             is fixed by the residue and nets down),
    LINKED - closed by a linking rule (see LINK RULES below),
    OPEN   - the residue runs out of bits before the class is settled;
             it is split in two (next binary digit) and tried again.

The OPEN classes are the "problem areas". Add linking rules to close them.
Strong induction makes this sound: if every smaller n reaches 1, a class
that drops below its start, or is entered from a smaller n, does too.
Members below M (t = 0) are checked directly.

Usage:
    python3 collatz_link_sieve.py --K 20
    python3 collatz_link_sieve.py --K 20 --mod3     # adds the mod-3 link
    python3 collatz_link_sieve.py --K 20 --mod3 --coalesce   # adds coalescence
    python3 collatz_link_sieve.py --K 20 --mod3 --coalesce --pair  # + run-exit pairing
"""
import argparse
from collections import Counter


# ---------------------------------------------------------------- hub map
def hub_step(n):
    if n % 2 == 0:
        return 3 * n // 2, "U"
    if n % 4 == 1:
        return (3 * n + 1) // 4, "d"
    return (n + 1) // 4, "D"


def reaches_one(n, limit=10_000):
    for _ in range(limit):
        if n == 1:
            return True
        n, _ = hub_step(n)
    return False


# ------------------------------------------------------------- LINK RULES
# Each rule gets (a, M) for the class n = M*t + a and returns a short name
# if it closes the class, else None. Add your own here.

def rule_mod3_entry(a, M):
    """n = 0 mod 3 is entered from the smaller hub value 2n/3 by a U loop,
    so it is already covered once every smaller n is."""
    if M % 3 == 0 and a % 3 == 0:
        return "entered from 2n/3"
    return None


def rule_half_pair(a, M):
    """Run-exit pairing. An even hub n = 2^k*m (m odd) exits its run at 3^k*m;
    n/2 exits at 3^(k-1)*m. If 3^(k-1)*m = 1 mod 4, n/2 takes the x0.75 loop,
    n takes the x0.25 loop, and both land on (3^k*m + 1)/4 -- they merge.
    n/2 < n, so n is covered. Needs k and m mod 4 fixed by the residue."""
    if a == 0 or a % 2:
        return None
    k = (a & -a).bit_length() - 1
    if M % (1 << (k + 2)):
        return None
    m4 = (a >> k) % 4
    if (pow(3, k - 1, 4) * m4) % 4 == 1:
        return "merges with n/2 at run exit"
    return None


# -------------------------------------------------------- class tracking
def run_class(a, M, coalesce=False, pair_path=False):
    """Follow n = M*t + a (t >= 1). Returns (status, signature)."""
    alpha, beta = M, a
    sig = []
    run_start = None                        # (alpha, beta) where current run began
    while True:
        if alpha % 2:                       # parity of n unknown
            return "open", sig
        if beta % 2 == 0:                   # n even -> U
            if not sig or sig[-1] != "U":
                run_start = (alpha, beta)
            alpha, beta = 3 * alpha // 2, 3 * beta // 2
            sig.append("U")
        else:
            if alpha % 4:                   # n mod 4 unknown
                return "open", sig
            if beta % 4 == 1:
                alpha, beta = 3 * alpha // 4, (3 * beta + 1) // 4
                sig.append("d")
            else:
                # EXIT PAIRING along the path: a run that exits by D merges
                # with the run from half its start value (which exits by d).
                if pair_path and sig and sig[-1] == "U" and run_start:
                    ha, hb = run_start[0] // 2, run_start[1] // 2
                    if (run_start[0] % 2 == 0 and run_start[1] % 2 == 0
                            and ha < M and (M - ha) + (a - hb) > 0):
                        sig.append("D")
                        return "pair", sig
                alpha, beta = alpha // 4, (beta + 1) // 4
                sig.append("D")
        # below start for every t >= 1 ?
        if alpha < M and (M - alpha) + (a - beta) > 0:
            return "down", sig
        # COALESCENCE LINK: the current value v = alpha*t + beta has another
        # predecessor m (not the value we just came from) with m < start.
        # m's path runs through v, so n merges into a smaller number's path.
        if coalesce:
            last = sig[-1]
            cands = []
            if alpha % 3 == 0:                      # v mod 3 is known
                r = beta % 3
                if r == 0 and last != "U":          # m = 2v/3 via U
                    cands.append((2 * alpha // 3, 2 * beta // 3))
                if r == 1 and last != "d":          # m = (4v-1)/3 via d
                    cands.append((4 * alpha // 3, (4 * beta - 1) // 3))
            if last != "D":                         # m = 4v-1 via D
                cands.append((4 * alpha, 4 * beta - 1))
            for ma, mb in cands:
                if ma < M and (M - ma) + (a - mb) > 0 and ma + mb >= 1:
                    return "merge", sig


def compress(sig):
    """U,U,U,d,U,D -> U3 d U1 D  (runs written as U<k>)."""
    out, k = [], 0
    for s in sig:
        if s == "U":
            k += 1
        else:
            if k:
                out.append(f"U{k}")
                k = 0
            out.append(s)
    if k:
        out.append(f"U{k}")
    return " ".join(out)


# ------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--K", type=int, default=20, help="max binary depth")
    ap.add_argument("--mod3", action="store_true", help="work mod 3*2^K and use the mod-3 link")
    ap.add_argument("--coalesce", action="store_true",
                    help="close classes whose path merges with a smaller number's path")
    ap.add_argument("--pair", action="store_true",
                    help="close even n that merge with n/2 right after the run exit")
    ap.add_argument("--top", type=int, default=12)
    ap.add_argument("--prefix", type=int, default=4, help="blocks shown per pattern")
    args = ap.parse_args()

    rules = [rule_mod3_entry] if args.mod3 else []
    if args.pair:
        rules.append(rule_half_pair)
    base = 3 if args.mod3 else 1

    # Depth 0: classes mod base
    open_classes = list(range(base))
    M = base
    rule_hits = Counter()
    print(f"{'K':>3} {'modulus':>12} {'open':>10} {'open fraction':>14}")
    for K in range(0, args.K + 1):
        survivors = []
        for a in open_classes:
            closed = False
            for r in rules:
                name = r(a, M)
                if name:
                    rule_hits[name] += 1
                    closed = True
                    break
            if closed:
                continue
            status, _ = run_class(a, M, args.coalesce, args.pair)
            if status == "pair":
                rule_hits["exit pairs with smaller run"] += 1
            if status == "merge":
                rule_hits["coalesces into smaller path"] += 1
            if status == "open":
                survivors.append(a)
        print(f"{K:>3} {M:>12} {len(survivors):>10} {len(survivors)/M:>14.6f}")
        if K == args.K:
            break
        open_classes = [x for a in survivors for x in (a, a + M)]
        M *= 2

    # Members below the final modulus (t = 0) checked directly
    bad_small = [n for n in range(1, M) if not reaches_one(n)]
    print(f"\nDirect check of n < {M}: {'all reach 1' if not bad_small else bad_small[:10]}")
    if rule_hits:
        print("Classes closed by link rules:", dict(rule_hits))

    # What the open classes look like: block pattern before bits ran out
    pats = Counter(" ".join(compress(run_class(a, M)[1]).split()[:args.prefix])
                   for a in survivors)
    print(f"\nMost common opening patterns (first {args.prefix} blocks) among the "
          f"{len(survivors)} open classes at K={args.K}:")
    for p, c in pats.most_common(args.top):
        print(f"  {c:>8}  {p}")
    runs = Counter()
    for a in survivors:
        s = compress(run_class(a, M)[1])
        for tok in s.split():
            if tok.startswith("U"):
                runs[int(tok[1:])] += 1
    print("\nRun lengths inside open classes (k: count):",
          dict(sorted(runs.items())))
    print("\nSmallest open residues:", sorted(survivors)[:15])


if __name__ == "__main__":
    main()
