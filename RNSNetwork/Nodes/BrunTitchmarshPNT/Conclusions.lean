/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# BrunTitchmarshPNT — primes in a short window (outside source)

The number of primes in a window of length `y` starting at `x` is at most
twice the length over the logarithm of the sieve level `z`, plus an error of
size `z` times a power of its logarithm. Proved in Lean with the Selberg sieve
in PrimeNumberTheoremAnd (PNT+, `BrunTitchmarsh.primesBetween_le`; no `sorry`
in that file or its sieve imports, checked at commit 127b50e, 2026-10-19).
PNT+ builds on a different Lean toolchain, so the statement, with the
definition `primesBetween`, is copied word for word and taken as a named
hypothesis.

No proof file: the claim is an outside source.
Metadata: `formalization.yaml`.
-/

namespace RNS.BrunTitchmarshPNT

/-- The number of primes in the interval from `a` to `b` (both ends
included), copied from PNT+ (`BrunTitchmarsh.primesBetween`). -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter Nat.Prime |>.card

/-- **Primes in a short window** (outside source; word for word the statement
of PNT+ `BrunTitchmarsh.primesBetween_le`, with its section variables
`0 < x`, `0 < y` written out). -/
def primes_between_le : Prop :=
  ∀ x y z : ℝ, 0 < x → 0 < y → 1 < z →
    primesBetween x (x + y) ≤ 2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3

end RNS.BrunTitchmarshPNT
