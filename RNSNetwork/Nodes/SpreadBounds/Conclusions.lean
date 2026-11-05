/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# SpreadBounds — how unevenly survivors can spread

Any two stretches of the same length hold survivor counts differing by at
most two to the number of wheels. Each way of choosing some of the wheels
contributes the number of multiples of their product in the stretch, and two
stretches of the same length hold the same number of multiples of any number,
give or take one; there are two to the number of wheels such choices.

With wheels 2 and 3 frozen, the two columns' survivor counts up to any point
differ by at most two to the number of remaining wheels: each choice of the
other wheels contributes multiples split between the two columns, and those
split evenly, give or take one.

Proof: `RNSSolutions/SpreadBounds.lean`, which assumes `Sawtooth`'s
`legendre_count` and `column_legendre_count` and nothing else. Metadata: `formalization.yaml`.

Source: D. H. Lehmer, "The distribution of totatives", Canad. J. Math. 7
(1955), Theorems 9-10 (for intervals of the cycle; stated here for any two
stretches of equal length).
-/

namespace RNS.SpreadBounds

/-- **The spread bound.** For prime wheels `W` and two stretches of the same
length `L`, one after position `x` and one after position `y`, the survivors
in the first exceed the survivors in the second by at most two to the number
of wheels. (Swapping the two stretches gives the bound in the other
direction.) -/
def interval_spread_bound : Prop :=
  ∀ (W : Finset Nat) (x y L : Nat), (∀ q ∈ W, q.Prime) →
    ((survivors_upto W (x + L)).card : Int) - (survivors_upto W x).card
      ≤ ((survivors_upto W (y + L)).card : Int) - (survivors_upto W y).card + 2 ^ W.card

/-- **The column-imbalance bound.** For prime wheels `W` including 2 and 3 and
any bound `x`, the survivors up to `x` in the 6n-1 column and in the 6n+1
column differ by at most two to the number of wheels other than 2 and 3, in
either direction. -/
def column_imbalance_bound : Prop :=
  ∀ (W : Finset Nat) (x : Nat), (∀ q ∈ W, q.Prime) → 2 ∈ W → 3 ∈ W →
    ((column_survivors_upto W 5 x).card : Int)
        ≤ (column_survivors_upto W 1 x).card + 2 ^ (W.card - 2) ∧
      ((column_survivors_upto W 1 x).card : Int)
        ≤ (column_survivors_upto W 5 x).card + 2 ^ (W.card - 2)

end RNS.SpreadBounds
