/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.PrimeCounting               -- `Nat.primeCounting`
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# PrimeNumberTheorem — the number of primes up to x (outside source)

The number of primes up to `x`, times the logarithm of `x`, divided by `x`,
tends to 1. Proved in Lean in PrimeNumberTheoremAnd (PNT+, declaration
`pi_alt'`), on a different Lean toolchain, so nodes here take it as a named
hypothesis.

Metadata: `formalization.yaml`.
-/

namespace RNS.PrimeNumberTheorem

open Filter Topology

/-- **The prime number theorem** (outside source, PNT+). -/
def prime_number_theorem : Prop :=
  Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1)

end RNS.PrimeNumberTheorem
