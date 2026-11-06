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
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# PrimeNumberTheorem — the number of primes up to x (outside source)

The number of primes up to `x` is asymptotically equivalent to `x` over the
logarithm of `x`. Proved in Lean in PrimeNumberTheoremAnd (PNT+, `pi_alt'` in
`Consequences.lean`, commit 127b50e). PNT+ builds on a different Lean
toolchain, so its statement is copied word for word (`pnt_equivalent`) and
taken as a named hypothesis; the limit form `prime_number_theorem` used by
other nodes is proved here from it.

Metadata: `formalization.yaml`.
-/

namespace RNS.PrimeNumberTheorem

open Filter Topology

/-- **The prime number theorem** (outside source; word for word the statement
of PNT+ `pi_alt'`). -/
def pnt_equivalent : Prop :=
  Asymptotics.IsEquivalent atTop (fun (x : ℝ) ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ))
    (fun x ↦ x / Real.log x)

/-- **The prime number theorem, limit form.** The number of primes up to `x`,
times the logarithm of `x`, divided by `x`, tends to 1. -/
def prime_number_theorem : Prop :=
  Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1)

end RNS.PrimeNumberTheorem
