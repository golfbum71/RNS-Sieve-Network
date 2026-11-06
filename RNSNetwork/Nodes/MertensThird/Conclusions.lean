/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.Harmonic.EulerMascheroni   -- `Real.eulerMascheroniConstant`
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# MertensThird — how fast the survivor share shrinks (outside source)

The survivor share after the wheels up to `x` is the product, over the primes
up to `x`, of one minus one over the prime. Mertens' third theorem: this share
is e to the minus Euler's constant, divided by the logarithm of `x`, up to an
error of order one over the logarithm squared.

Proved in Lean in PrimeNumberTheoremAnd (PNT+, `Mertens.lean`, no `sorry`;
checked at commit 127b50e, 2026-10-19). PNT+ builds on a different Lean
toolchain, so the one result needed from it, the remainder bound
`mertens_third_remainder`, is copied word for word (with the definition `E₃`)
and taken as a named hypothesis. The identity `product_identity` (blueprint
7.1.7) is proved here, with the proof adapted from PNT+, and the limit form
`mertens_third` (share times logarithm tends to e to the minus Euler's
constant), the form other nodes use, follows.

Proof of the limit form: `RNSSolutions/MertensThird.lean`.
Metadata: `formalization.yaml`.
-/

namespace RNS.MertensThird

open Filter Topology

/-- The survivor share after the wheels up to `y`: the product, over the primes
up to `y`, of one minus one over the prime. -/
noncomputable def survivor_share (y : ℝ) : ℝ :=
  ∏ p ∈ active_primes (⌊y⌋₊ + 1), (1 - 1 / (p : ℝ))

/-- The remainder in Mertens' third theorem, copied from PNT+ (`Mertens.E₃`):
the sum, over the primes up to `x`, of the logarithm of one minus one over the
prime, plus the logarithm of the logarithm of `x`, plus Euler's constant. -/
noncomputable def E₃ (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log (1 - (1 : ℝ) / p) + Real.log (Real.log x) +
    Real.eulerMascheroniConstant

/-- **Mertens' third theorem, error bound** (outside source; word for word the
statement of PNT+ `Mertens.E₃.abs_le`, blueprint Theorem 7.1.8). There is a
constant `C` with the remainder at most `C` over the logarithm of `x`, for every
`x` at least 2. -/
def mertens_third_remainder : Prop :=
  ∃ C, ∀ x : ℝ, 2 ≤ x → |E₃ x| ≤ C / Real.log x

/-- **The product as an exponential of the remainder** (blueprint Theorem
7.1.7, PNT+ `Mertens.prod_one_minus_div_prime_eq`, proved here). For `x` above
1, the survivor share is e to the minus Euler's constant, times e to the
remainder, over the logarithm of `x`. -/
def product_identity : Prop :=
  ∀ x : ℝ, 1 < x →
    survivor_share x =
      Real.exp (-Real.eulerMascheroniConstant) * Real.exp (E₃ x) / Real.log x

/-- **Mertens' third theorem, limit form.** The survivor share times the
logarithm of `x` tends to e to the minus Euler's constant. -/
def mertens_third : Prop :=
  Tendsto (fun x : ℝ => survivor_share x * Real.log x) atTop
    (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))

end RNS.MertensThird
