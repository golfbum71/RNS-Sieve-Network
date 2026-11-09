/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

/-!
# BrunTwinCount — counting the twin multiples of a set of wheels exactly

Brun's sieve, stage 2. `BrunPureSieve` bounds the twin survivors by
inclusion–exclusion over sets of wheels; each term counts the positions `m`
from 1 to `N` where the product of a set of wheels divides `m` times `m + 2`.
This node counts those positions.

Take a set of distinct prime wheels and their product. In one full cycle of
the product, the positions where the product divides `m` times `m + 2` number
one for the wheel at 2 and two for every odd wheel, multiplied together
(`twin_rho`). The cycle repeats, so up to `N` the count is `N` times that
number divided by the product, off by at most that number.

The proof works one cycle at a time. A full cycle contributes the same
number every time; the leftover piece of a cycle contributes between zero and
that number. Inside one cycle, the positions are the residues of the product,
and the Chinese Remainder Theorem splits the residues of the product into
residues of each wheel. For one wheel, a residue times the residue two
further on is zero only at zero and at minus two, which are the same residue
for the wheel at 2.

Proof: `RNSSolutions/BrunTwinCount.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.BrunTwinCount

/-- The number of twin roots in one cycle of the product of `D`: one for the
wheel at 2, two for every other wheel, multiplied together. -/
def twin_rho (D : Finset Nat) : Nat := ∏ p ∈ D, (if p = 2 then 1 else 2)

/-- **The twin multiples count.** For a set of distinct prime wheels with
product `d`, the positions `m` from 1 to `N` where `d` divides `m (m + 2)`
number `N · twin_rho / d`, off by at most `twin_rho`. -/
def twin_multiples_count : Prop :=
  ∀ (D : Finset Nat) (N : Nat), (∀ p ∈ D, p.Prime) →
    |((((Finset.Ioc 0 N).filter (fun m => D.prod id ∣ m * (m + 2))).card : ℕ) : ℝ)
        - (N : ℝ) * ((twin_rho D : ℕ) : ℝ) / ((D.prod id : ℕ) : ℝ)|
      ≤ ((twin_rho D : ℕ) : ℝ)

/-- The number of roots of `x (x + c)` in one cycle of the product of `D`: one
for a wheel dividing `c`, two for every other wheel, multiplied together. -/
def shift_rho (c : Nat) (D : Finset Nat) : Nat := ∏ p ∈ D, (if p ∣ c then 1 else 2)

/-- **The multiples count at any shift.** For a set of distinct prime wheels
with product `d` and any shift `c`, the positions `m` from 1 to `N` where `d`
divides `m (m + c)` number `N · shift_rho / d`, off by at most `shift_rho`. -/
def shift_multiples_count : Prop :=
  ∀ (D : Finset Nat) (c N : Nat), (∀ p ∈ D, p.Prime) →
    |((((Finset.Ioc 0 N).filter (fun m => D.prod id ∣ m * (m + c))).card : ℕ) : ℝ)
        - (N : ℝ) * ((shift_rho c D : ℕ) : ℝ) / ((D.prod id : ℕ) : ℝ)|
      ≤ ((shift_rho c D : ℕ) : ℝ)

end RNS.BrunTwinCount
