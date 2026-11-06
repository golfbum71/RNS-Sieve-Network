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

Proved in Lean in PrimeNumberTheoremAnd (PNT+, declaration `E₃.bound''`),
which builds on a different Lean toolchain, so nodes here take it as a named
hypothesis (`mertens_third_error`, stated in the classical form of the PNT+
blueprint). The limit form `mertens_third` (share times logarithm tends to e
to the minus Euler's constant) follows from it in Lean here, and is the form
other nodes use.

Proof of the limit form: `RNSSolutions/MertensThird.lean`.
Metadata: `formalization.yaml`.
-/

namespace RNS.MertensThird

open Filter Topology

/-- The survivor share after the wheels up to `y`: the product, over the primes
up to `y`, of one minus one over the prime. -/
noncomputable def survivor_share (y : ℝ) : ℝ :=
  ∏ p ∈ active_primes (⌊y⌋₊ + 1), (1 - 1 / (p : ℝ))

/-- **Mertens' third theorem, with its error term** (outside source, PNT+).
There is a constant `C` such that for every `x` at least 2, the survivor share
differs from e to the minus Euler's constant over the logarithm of `x` by at
most `C` over the logarithm of `x` squared. -/
def mertens_third_error : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |survivor_share x - Real.exp (-Real.eulerMascheroniConstant) / Real.log x| ≤
      C / Real.log x ^ 2

/-- **Mertens' third theorem, limit form.** The survivor share times the
logarithm of `x` tends to e to the minus Euler's constant. -/
def mertens_third : Prop :=
  Tendsto (fun x : ℝ => survivor_share x * Real.log x) atTop
    (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))

end RNS.MertensThird
