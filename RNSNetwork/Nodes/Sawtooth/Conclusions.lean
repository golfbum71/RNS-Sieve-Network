/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# Sawtooth — the survivor count minus its proportional share

The survivors up to any point equal a signed count over the ways of choosing
some of the wheels: for each choice, the bound divided by the product of the
chosen wheels (rounded down), with sign plus for an even number of wheels
chosen and minus for an odd number (Legendre's inclusion-exclusion).

Taking the bound to be a fraction of the cycle, the survivors up to it, minus
their proportional share, become a signed sum of remainders: for each choice
of wheels, the fraction's numerator times the product of the wheels NOT
chosen, divided by the fraction's denominator, contributes its remainder.
Stated multiplied through by the denominator, so everything stays a whole
number.

Each choice of wheels corresponds to one divisor of the cycle, and its sign is
the Möbius function of that divisor, so this is the identity Germain writes
with the Möbius function and fractional parts; the remainder divided by the
denominator is the fractional part.

Proof: `RNSSolutions/Sawtooth.lean`. Metadata: `formalization.yaml`.

Source: J. Germain, "The distribution of totatives", Canad. Math. Bull. 48
(2005), the identity behind Theorem 1.1. `GermainCriterion` rests on it.
-/

namespace RNS.Sawtooth

/-- **Legendre's count.** For prime wheels `W` and a bound `x`, the survivors
from 1 to `x` number the signed sum, over every choice `S` of some of the
wheels, of `x` divided by the product of the chosen wheels (rounded down),
with sign `(-1)` to the number chosen. -/
def legendre_count : Prop :=
  ∀ (W : Finset Nat) (x : Nat), (∀ q ∈ W, q.Prime) →
    ((survivors_upto W x).card : Int)
      = ∑ S ∈ W.powerset, (-1 : Int) ^ S.card * ((x / S.prod id : Nat) : Int)

/-- **The sawtooth identity.** For prime wheels `W`, a number of equal
intervals `k` and a count of intervals `a`: `k` times the survivors up to `a`
`k`-ths of the cycle (rounded down), minus `a` times the survivors of the
whole cycle, equals minus the signed sum, over every choice `S` of some of the
wheels, of the remainder of `a` times the product of the wheels not chosen, on
division by `k`. -/
def sawtooth_identity : Prop :=
  ∀ (W : Finset Nat) (k a : Nat), (∀ q ∈ W, q.Prime) →
    (k : Int) * (survivors_upto W (a * W.prod id / k)).card
        - (a : Int) * (survivors_upto W (W.prod id)).card
      = - ∑ S ∈ W.powerset, (-1 : Int) ^ S.card * ((a * (W \ S).prod id % k : Nat) : Int)

/-- **An even split, read off the remainders.** The survivors up to `a`
`k`-ths of the cycle are exactly `a` shares of the cycle's survivors (the form
`LehmerSplit` uses) precisely when the signed sum of remainders in
`sawtooth_identity` is zero. -/
def even_split_iff_remainders_cancel : Prop :=
  ∀ (W : Finset Nat) (k a : Nat), (∀ q ∈ W, q.Prime) →
    (k * (survivors_upto W (a * W.prod id / k)).card
        = a * (survivors_upto W (W.prod id)).card
      ↔ ∑ S ∈ W.powerset, (-1 : Int) ^ S.card * ((a * (W \ S).prod id % k : Nat) : Int) = 0)

/-- **Legendre's count, within one column.** For prime wheels `W` including 2
and 3, a column `r` (1 for 6n+1, 5 for 6n-1) and a bound `x`: the column's
survivors from 1 to `x` number the signed sum, over every choice `S` of some
of the wheels other than 2 and 3, of how many multipliers from 1 to `x`
divided by the product of the chosen wheels put that product's multiple in
column `r`. -/
def column_legendre_count : Prop :=
  ∀ (W : Finset Nat) (r x : Nat), (∀ q ∈ W, q.Prime) → 2 ∈ W → 3 ∈ W → (r = 1 ∨ r = 5) →
    ((column_survivors_upto W r x).card : Int)
      = ∑ S ∈ ((W.erase 2).erase 3).powerset, (-1 : Int) ^ S.card *
          (((Finset.Icc 1 (x / S.prod id)).filter (fun m => (S.prod id * m) % 6 = r)).card : Int)

end RNS.Sawtooth
