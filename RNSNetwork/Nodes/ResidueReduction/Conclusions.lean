/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.TeamShift.Conclusions
import Mathlib.Algebra.GCDMonoid.Multiset

/-!
# ResidueReduction — only the remainders matter: a residue sieve for the lonely runner

The runner to be lonely stands still; the others have the speeds in `S`. Pick a
wheel `p` and the modulus `(number of runners) * p`. At a time with that modulus
as denominator, a runner's place depends only on its speed's remainder for the
modulus (`far_mod`). So a finite check over lists of remainders decides every
set of speeds at once.

The residue check (`residue_check`): every list of remainders, as many as the
moving runners, none a multiple of the wheel, and with every list-but-one
sharing no factor with the modulus, has a lonely time with that denominator.
If the check passes, then every set of speeds that is never lonely (with the
speeds sharing no common factor) has a speed divisible by the wheel
(`residue_check_forces_divisor`). Lists that fail the sharing condition are
handled by `TeamShift`, given the conjecture for one runner fewer.

Rosenfeld 2025, Lemma 6 (arXiv 2509.14111): the main lemma behind every record
from eight runners on. With enough wheels forced to divide the product of the
speeds, Rosenfeld's size bound (Corollary 3, cited, not proved here) rules a
counterexample out.

Proof: `RNSSolutions/ResidueReduction.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.ResidueReduction

open RNS.PileUpLock

/-- **Only the remainder matters.** Being at least `1 / n` of a lap from the
start at the point `y / m` depends only on the remainder of `y` for `m`. -/
def far_mod : Prop :=
  ∀ (n m : ℕ) (y : ℤ), far n m (y % (m : ℤ)) ↔ far n m y

/-- **The residue check for `k` moving runners and the wheel `p`.** Every list
(multiset) of `k` remainders for the modulus `(k + 1) * p`, none a multiple of
`p`, such that leaving out any one entry the rest share no factor with the
modulus, has a lonely time with denominator `(k + 1) * p`. A finite condition. -/
def residue_check (k p : ℕ) : Prop :=
  ∀ R : Multiset ℤ, Multiset.card R = k →
    (∀ r ∈ R, 0 ≤ r ∧ r < (((k + 1) * p : ℕ) : ℤ) ∧ ¬ (p : ℤ) ∣ r) →
    (∀ r ∈ R, Int.gcd (R.erase r).gcd (((k + 1) * p : ℕ) : ℤ) = 1) →
    ∃ t : ℤ, ∀ r ∈ R, far (k + 1) ((k + 1) * p) (r * t)

/-- **A passing residue check forces the wheel into every counterexample.** For
at least three moving runners, if the Lonely Runner Conjecture holds for one
runner fewer and the residue check for `p` passes, then any `k` distinct nonzero
speeds with no common factor that never give a lonely moment include a speed
divisible by `p`. -/
def residue_check_forces_divisor : Prop :=
  ∀ (k p : ℕ), 3 ≤ k → 0 < p → lonely_runner_upto (k - 1) → residue_check k p →
    ∀ S : Finset ℤ, S.card = k → 0 ∉ S → S.gcd id = 1 → ¬ has_lonely_time S →
      ∃ v ∈ S, (p : ℤ) ∣ v

end RNS.ResidueReduction
