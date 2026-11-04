/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# LehmerSplit — Lehmer's even split

If one wheel leaves remainder 1 on division by a chosen number of intervals,
the survivors of the combined cycle split evenly across that many equal
intervals: the survivors up to the end of the `a`-th interval (rounded down)
are exactly `a` shares of the cycle's survivors. With wheels 2 and 3 frozen,
each column splits evenly when that wheel also leaves remainder 1 on division
by 6.

Proof: `RNSSolutions/LehmerSplit.lean`, which assumes four claims of
`UniformSubdivision` and nothing else. Metadata: `formalization.yaml`.

Source: D. H. Lehmer, "The distribution of totatives", Canad. J. Math. 7
(1955), Theorem 4 (the whole-count form). `UniformSubdivision`'s
`uniform_subdivision` is the case of the rotating prime minus one intervals.
-/

namespace RNS.LehmerSplit

/-- **Lehmer's even split.** If the wheel `p` added to the wheels `W` leaves
remainder 1 on division by `k`, then `k` times the survivors up to the end of
the `a`-th of `k` equal intervals equals `a` times the survivors of the whole
cycle. -/
def lehmer_even_split : Prop :=
  ∀ (W : Finset Nat) (p k a : Nat), p.Prime → (∀ q ∈ W, q.Prime) → p ∉ W → p % k = 1 →
    k * (survivors_upto (insert p W) (a * (W.prod id * p) / k)).card
      = a * (survivors_upto (insert p W) (W.prod id * p)).card

/-- **Lehmer's even split, within one column.** With wheels 2 and 3 frozen, if
the wheel `p` leaves remainder 1 on division by `k` and by 6, each column
splits evenly across the `k` intervals. -/
def lehmer_even_split_column : Prop :=
  ∀ (W : Finset Nat) (p k a r : Nat), p.Prime → (∀ q ∈ W, q.Prime) → p ∉ W →
    2 ∈ W → 3 ∈ W → p % k = 1 → p % 6 = 1 →
    k * (column_survivors_upto (insert p W) r (a * (W.prod id * p) / k)).card
      = a * (column_survivors_upto (insert p W) r (W.prod id * p)).card

end RNS.LehmerSplit
