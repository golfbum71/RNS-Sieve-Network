/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.Finset.Powerset

/-!
# BrunPureSieve — truncated inclusion–exclusion for the wheels

Count the survivors of a set of prime wheels among the positions 1 to `N` by
inclusion–exclusion: start with all positions, take away the multiples of
each wheel, add back the multiples of each pair, and so on. Brun's pure sieve
stops this early. Stopping after the sets of at most an even number of wheels
gives at least the true survivor count; stopping after an odd number gives at
most the true count (the Bonferroni inequalities). Going all the way gives the
count exactly (Legendre's identity).

Brun's pure sieve is where modern sieve theory starts, and the even/odd
alternation is the basic upper- and lower-bound pair behind the fundamental
lemma. Here everything is exact and finite.

Proof: `RNSSolutions/BrunPureSieve.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.BrunPureSieve

/-- Inclusion–exclusion stopped after the sets of at most `t` wheels: over the
sets `D` of at most `t` wheels, plus or minus (by the parity of the size of
`D`) the number of multiples of the product of `D` among 1 to `N`. -/
def truncated_count (W : Finset Nat) (N t : Nat) : ℤ :=
  ∑ D ∈ W.powerset.filter (fun D => D.card ≤ t), (-1 : ℤ) ^ D.card * ((N / D.prod id : Nat) : ℤ)

/-- **Stopping at an even number of wheels overcounts** (Bonferroni). -/
def bonferroni_even : Prop :=
  ∀ (W : Finset Nat) (N t : Nat), (∀ q ∈ W, q.Prime) → Even t →
    ((survivors_upto W N).card : ℤ) ≤ truncated_count W N t

/-- **Stopping at an odd number of wheels undercounts** (Bonferroni). -/
def bonferroni_odd : Prop :=
  ∀ (W : Finset Nat) (N t : Nat), (∀ q ∈ W, q.Prime) → Odd t →
    truncated_count W N t ≤ ((survivors_upto W N).card : ℤ)

/-- **Going all the way is exact** (Legendre's identity). -/
def legendre_exact : Prop :=
  ∀ (W : Finset Nat) (N t : Nat), (∀ q ∈ W, q.Prime) → W.card ≤ t →
    ((survivors_upto W N).card : ℤ) = truncated_count W N t

end RNS.BrunPureSieve
