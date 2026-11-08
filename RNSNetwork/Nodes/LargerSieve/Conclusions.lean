/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# LargerSieve — Gallagher's larger sieve: when each wheel leaves few positions

The small sieves (Brun, Selberg) are for wheels that block few positions. The
larger sieve is for the opposite case: a set of numbers in a window of length
`N` that occupies only a few positions on each wheel. Wheels may be prime
powers here, each weighted by the logarithm of its prime (the von Mangoldt
weight; any other modulus has weight 0).

Count the pairs of members that sit at the same position of a wheel, with the
wheel's weight. From below: on a wheel where the set occupies few positions,
many pairs must share one (Cauchy–Schwarz). From above: a pair of the same
member counts every wheel, and two different members differ by less than
`N`, so the weights of the wheels dividing their difference add up to at
most the logarithm of `N`. Comparing the two gives Gallagher's bound: the set
has at most (total weight minus log N) over (total of weight over occupied
positions minus log N) members, when that denominator is positive.

So if every wheel leaves at most `G` positions open and the wheels' total
weight over `G` exceeds the logarithm of the window, the set is at most
(total weight minus log N) over (total weight over `G` minus log N).
Gallagher (1971); Odlyzko's thesis, Theorem 5.1 and Corollary 5.4.

Proof: `RNSSolutions/LargerSieve.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.LargerSieve

/-- The number of positions the set `A` occupies on the wheel of size `q`. -/
def classes (A : Finset Nat) (q : Nat) : Nat := (A.image (fun a => a % q)).card

/-- **Gallagher's larger sieve.** For a set `A` inside a window of length `N`
(`M ≤ a < M + N`) and any finite set `S` of wheel sizes, weighted by the von
Mangoldt function: if the sum of weight over occupied positions exceeds
`log N`, then `A` has at most (total weight − log N) / (sum of weight over
occupied positions − log N) members. -/
def larger_sieve : Prop :=
  ∀ (A S : Finset Nat) (M N : Nat), (∀ a ∈ A, M ≤ a ∧ a < M + N) →
    Real.log N < ∑ q ∈ S, ArithmeticFunction.vonMangoldt q / (classes A q : ℝ) →
    (A.card : ℝ) ≤ (∑ q ∈ S, ArithmeticFunction.vonMangoldt q - Real.log N) /
      (∑ q ∈ S, ArithmeticFunction.vonMangoldt q / (classes A q : ℝ) - Real.log N)

/-- **Few open positions on every wheel.** If `A` occupies at most `G ≥ 1`
positions on every wheel of `S` and the total weight over `G` exceeds
`log N`, then `A` has at most (total weight − log N) / (total weight / G −
log N) members. -/
def larger_sieve_few : Prop :=
  ∀ (A S : Finset Nat) (M N G : Nat), (∀ a ∈ A, M ≤ a ∧ a < M + N) → 1 ≤ G →
    (∀ q ∈ S, classes A q ≤ G) →
    Real.log N < (∑ q ∈ S, ArithmeticFunction.vonMangoldt q) / G →
    (A.card : ℝ) ≤ (∑ q ∈ S, ArithmeticFunction.vonMangoldt q - Real.log N) /
      ((∑ q ∈ S, ArithmeticFunction.vonMangoldt q) / G - Real.log N)

end RNS.LargerSieve
