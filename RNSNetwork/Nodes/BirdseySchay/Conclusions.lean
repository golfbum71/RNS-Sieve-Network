/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.HardyLittlewood.Conclusions
import RNSNetwork.Nodes.TwinConstant.Conclusions
import Mathlib.NumberTheory.Harmonic.EulerMascheroni  -- `Real.eulerMascheroniConstant`
import Mathlib.NumberTheory.PrimeCounting             -- `Nat.primeCounting`, `Nat.nth`
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# BirdseySchay — the twin share carried below the ceiling

Birdsey and Schay (arXiv:1906.09220, 2019) count the twin primes below the
square of a prime by a heuristic. In the network's words: the twin pairs below
the next prime's square number about e^γ/2, times the twin share for the wheels
up to that prime (the twin survivors of the cycle as a fraction of all
survivors, the product of (wheel − 2)/(wheel − 1) over the wheels from 3 up),
times the number of primes below the square. The single factor e^γ/2 is the
Mertens correction from the long cycle to the short range below the ceiling.

**The heuristic is open and never claimed.** It is about as strong as the
Hardy–Littlewood count for twins itself, restated at the prime squares. This
node proves, without it:

* the corrected twin share, times the logarithm of the largest wheel, tends to
  half the twin-prime constant (`corrected_share_limit`);
* neighbouring primes have ratio tending to 1 (`next_prime_ratio`);

and, from it:

* at the prime squares the twin count is Hardy and Littlewood's prediction
  (`twin_count_at_squares`);
* the twin count is Hardy and Littlewood's prediction for every bound
  (`birdsey_schay_implies_twin_asymptotic`): the heuristic implies the
  Hardy–Littlewood conjecture for the twin pattern.

So the one Mertens correction lands exactly on Hardy and Littlewood's constant.
Numerically (pairs below the square of 9973): 438,192 against the heuristic's
410,353 (ratio 1.068) and the plain Hardy–Littlewood term's 387,236 (ratio
1.132); both ratios fall slowly toward 1.

Proof: `RNSSolutions/BirdseySchay.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.BirdseySchay

/-- Twin pairs below a bound: the starting numbers below it where the number and
the number plus 2 are both prime. -/
noncomputable def twin_pairs_below (x : ℕ) : ℝ := actual_tuple_count {0, 2} x

/-- The twin share for the wheels up to `q`, with 2 left out: the product of
(wheel − 2)/(wheel − 1). It is the twin survivors of the cycle as a fraction of
all survivors (`TwinShare.twin_share_eq_prod`). -/
noncomputable def twin_share (q : ℕ) : ℝ :=
  ∏ p ∈ (active_primes (q + 1)).erase 2, ((p : ℝ) - 2) / ((p : ℝ) - 1)

/-- **Birdsey and Schay's heuristic** (open, never claimed): along the primes,
the twin pairs below a prime's square are asymptotically e^γ/2 times the twin
share for the wheels up to that prime times the number of primes up to the
square. -/
def birdsey_schay_heuristic : Prop :=
  Asymptotics.IsEquivalent Filter.atTop
    (fun n => twin_pairs_below (Nat.nth Nat.Prime n ^ 2))
    (fun n => Real.exp Real.eulerMascheroniConstant / 2 *
      twin_share (Nat.nth Nat.Prime n) * Nat.primeCounting (Nat.nth Nat.Prime n ^ 2))

/-- **The corrected share tends to half the twin constant over the log.** The
twin share for the wheels up to `q`, times e^γ/2, times the logarithm of `q`,
tends to half the twin-prime constant. -/
def corrected_share_limit : Prop :=
  Filter.Tendsto (fun q : ℕ => Real.exp Real.eulerMascheroniConstant / 2 *
      twin_share q * Real.log q) Filter.atTop
    (nhds (RNS.TwinConstant.twin_prime_classical_constant / 2))

/-- **Neighbouring primes have ratio tending to 1.** -/
def next_prime_ratio : Prop :=
  Filter.Tendsto (fun n => (Nat.nth Nat.Prime (n + 1) : ℝ) / Nat.nth Nat.Prime n)
    Filter.atTop (nhds 1)

/-- **At the prime squares, the heuristic gives Hardy and Littlewood's count.**
If the heuristic holds, the twin pairs below a prime's square are
asymptotically the Hardy–Littlewood prediction there. -/
def twin_count_at_squares : Prop :=
  birdsey_schay_heuristic →
    Asymptotics.IsEquivalent Filter.atTop
      (fun n => twin_pairs_below (Nat.nth Nat.Prime n ^ 2))
      (fun n => hardy_littlewood_main_term {0, 2} (Nat.nth Nat.Prime n ^ 2))

/-- **The heuristic implies Hardy–Littlewood for twins.** If the heuristic
holds, the Hardy–Littlewood conjecture holds for the twin pattern {0, 2}. -/
def birdsey_schay_implies_twin_asymptotic : Prop :=
  birdsey_schay_heuristic → RNS.HardyLittlewood.hardy_littlewood_conjecture {0, 2}

end RNS.BirdseySchay
