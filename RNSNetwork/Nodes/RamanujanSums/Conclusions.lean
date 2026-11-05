/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.RingTheory.RootsOfUnity.Complex   -- `Complex.exp`, roots of unity

/-!
# RamanujanSums — the survivor pattern's frequencies, wheel by wheel

Place the positions of one combined cycle evenly around a circle. Add up the
points that survive every wheel, each turned by a chosen frequency: position
`k` contributes the cycle's basic turn raised to `k` times the frequency. The
total is Ramanujan's sum for the cycle length at that frequency, the
frequency content of the survivor pattern.

For prime wheels it is a product over the wheels: a wheel contributes its size
minus 1 if it divides the frequency, and minus 1 if it does not. So each
wheel acts on the frequencies independently, as the Chinese Remainder Theorem
suggests. At frequency 1 the total is plus or minus 1 by the number of
wheels (the Möbius function of the cycle length); at frequency 0 it is the
survivor count.

This is the squarefree case of the classical evaluation of Ramanujan's sum
(Kluyver 1906; Hölder's link with von Sterneck's function). Mathlib does not
define Ramanujan sums, so the sum is defined here.

Proof: `RNSSolutions/RamanujanSums.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.RamanujanSums

/-- The basic turn of the combined cycle of the wheels `W`: one full turn
divided by the cycle length. -/
noncomputable def cycle_root (W : Finset Nat) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / ((W.prod id : Nat) : ℂ))

/-- **Ramanujan's sum for the cycle of the wheels `W`, at frequency `n`**: the
survivors of one cycle, each turned by the basic turn to the power of the
survivor times the frequency, added up. -/
noncomputable def ramanujan_sum (W : Finset Nat) (n : Nat) : ℂ :=
  ∑ k ∈ survivors_upto W (W.prod id), cycle_root W ^ (k * n)

/-- **The wheel product.** For prime wheels `W` and any frequency `n`,
Ramanujan's sum is the product over the wheels of: the wheel size minus 1 if
the wheel divides `n`, and minus 1 if it does not. -/
def ramanujan_wheel_product : Prop :=
  ∀ (W : Finset Nat), (∀ q ∈ W, q.Prime) → ∀ n : Nat,
    ramanujan_sum W n = ∏ q ∈ W, (if q ∣ n then (q : ℂ) - 1 else -1)

end RNS.RamanujanSums
