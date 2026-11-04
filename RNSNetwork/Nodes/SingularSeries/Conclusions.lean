/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# SingularSeries — the correction constant exists and is positive

Each wheel's correction factor differs from 1 by an amount that shrinks like
one over the wheel size squared, so the product over all wheels converges;
for an admissible pattern the result is strictly positive. The exact
surviving fraction of the cycle equals the correction product times the
naive guess that each offset is blocked independently.

Proof: `RNSSolutions/SingularSeries.lean`. Only the local-density claim
assumes another node's claim (`SurvivorCount.general_survivor_count`).
Metadata: `formalization.yaml`.

Source of record: `rns_sieve_6.lean`, Part B Steps 3 and 4. The same
convergence and positivity results are packaged separately, Comparator-ready,
in the `HardyLittlewood` repository.
-/

namespace RNS.SingularSeries

/-- **Each correction factor is close to 1.** For a nonempty pattern there is
a constant such that, at every wheel larger than all the offsets, the
correction factor differs from 1 by at most that constant divided by the
wheel size squared. -/
def delta_bound : Prop :=
  ∀ T : Finset Nat, 1 ≤ T.card → ∃ C : Real, 0 ≤ C ∧
    ∀ p : Nat, p.Prime → (∀ t ∈ T, t < p) →
      |singular_series_factor T p - 1| ≤ C / (p : Real) ^ 2

/-- **The product over all wheels converges.** For a nonempty pattern, the
infinite product of the correction factors over all primes converges. -/
def factor_multipliable : Prop :=
  ∀ T : Finset Nat, 1 ≤ T.card →
    Multipliable (fun p : Nat.Primes => singular_series_factor T p)

/-- **The Hardy–Littlewood constant is positive.** For a nonempty admissible
pattern, the product of all the correction factors is strictly positive. -/
def hardy_littlewood_constant_pos : Prop :=
  ∀ T : Finset Nat, is_admissible T → 1 ≤ T.card → 0 < hardy_littlewood_constant T

/-- **Exact local density.** For a nonempty admissible pattern, the fraction
of the combined cycle that survives every active wheel equals the product of
those wheels' correction factors times the naive guess, the product of
(1 minus one over the wheel size) raised to the number of offsets. -/
def local_density_factorization : Prop :=
  ∀ (T : Finset Nat) (limit : Nat), is_admissible T → 1 ≤ T.card →
    ((wheel_survivors_gen T limit).card : Real) / (primorial_modulus limit : Real)
      = (∏ q ∈ active_primes limit, singular_series_factor T q)
        * ∏ q ∈ active_primes limit, (1 - 1 / (q : Real)) ^ T.card

end RNS.SingularSeries
