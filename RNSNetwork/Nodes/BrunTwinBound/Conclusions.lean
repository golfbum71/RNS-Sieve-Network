/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunPureSieve.Conclusions
import RNSNetwork.Nodes.BrunTwinCount.Conclusions
import RNSNetwork.Nodes.BrunTruncation.Conclusions

/-!
# BrunTwinBound — Brun's upper bound for the twin survivors, with every error term

Brun's sieve, stage 4. Join the three stages:

* `BrunPureSieve`: the twin survivors of a set of prime wheels up to `N` are
  at most inclusion–exclusion stopped at an even number of wheels;
* `BrunTwinCount`: each term of it is `N` times the product of the wheels'
  twin shares, off by at most the number of twin roots;
* `BrunTruncation`: the stopped sum of products of shares is at most the
  full product plus the sum over the sets of one more wheel.

The result (`twin_sifted_bound`): the twin survivors up to `N` are at most
`N` times (the product over the wheels of one minus the twin share, plus the
sum over the sets of one more wheel than the stopping point of the products
of their twin shares), plus the total number of twin roots over the sets
used. The twin share of a wheel is one half for the wheel at 2 and two over
the wheel for every other wheel.

And the link to twin primes (`twin_count_le_sifted`): a twin prime pair whose
smaller member is at least `L` survives every wheel below `L`, so the twin
prime pairs up to `N` are at most `L` plus the twin survivors of the wheels
below `L`.

Proof: `RNSSolutions/BrunTwinBound.lean`. Rests on `BrunPureSieve`,
`BrunTwinCount` and `BrunTruncation` (the bound) and on no node (the link).
Metadata: `formalization.yaml`.
-/

namespace RNS.BrunTwinBound

open RNS.BrunPureSieve RNS.BrunTwinCount RNS.BrunTruncation

/-- The twin share of a wheel: one half for the wheel at 2, two over the
wheel for every other wheel. -/
noncomputable def twin_g (p : Nat) : ℝ := (if p = 2 then (1 : ℝ) else 2) / (p : ℝ)

/-- **Brun's twin bound with its error terms.** -/
def twin_sifted_bound : Prop :=
  ∀ (W : Finset Nat) (N t : Nat), (∀ q ∈ W, q.Prime) → Even t →
    ((sifted W (fun n => n * (n + 2)) N).card : ℝ) ≤
      (N : ℝ) * (∏ p ∈ W, (1 - twin_g p) + esymm_k W twin_g (t + 1))
        + ∑ D ∈ W.powerset.filter (fun D => D.card ≤ t), ((twin_rho D : ℕ) : ℝ)

/-- The twin prime pairs whose smaller member is at most `N`. -/
def twin_prime_count (N : Nat) : Nat :=
  ((Finset.Ioc 0 N).filter (fun n => n.Prime ∧ (n + 2).Prime)).card

/-- **Twin primes survive the small wheels.** -/
def twin_count_le_sifted : Prop :=
  ∀ (L N : Nat), twin_prime_count N ≤ L + (sifted (active_primes L) (fun n => n * (n + 2)) N).card

end RNS.BrunTwinBound
