/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# MertensSecond — the sum of the reciprocals of the primes

Mertens' second theorem: the sum of one over each prime up to `x` is the
logarithm of the logarithm of `x`, plus a constant (the Meissel–Mertens
constant), plus a remainder at most a constant over the logarithm of `x`.

`mertens_second_remainder` is an outside claim. PrimeNumberTheoremAnd (PNT+)
proves it with explicit constants: `Mertens.sum_prime_div_eq` writes the sum
as the logarithm of the logarithm plus `Mertens.M` plus `Mertens.E₂p x`, and
`Mertens.E₂p.abs_le` bounds `E₂p x` by `(log 4 + 6 + E₁) / log x` for `x` at
least 2 (file `PrimeNumberTheoremAnd/IEANTN/Mertens.lean`). The claim here
keeps that shape and replaces the two explicit constants by "some constant",
so it follows from those two results directly.

`prime_reciprocal_upper` is the one consequence Brun's theorem needs: the sum
is at most the logarithm of the logarithm plus a constant. Proved here as a
step from the outside claim.

Proof: `RNSSolutions/MertensSecond.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.MertensSecond

/-- **Mertens' second theorem, with its remainder** (outside claim, from PNT+). -/
def mertens_second_remainder : Prop :=
  ∃ M C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |(∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) - Real.log (Real.log x) - M|
      ≤ C / Real.log x

/-- **The sum of the prime reciprocals is at most the logarithm of the
logarithm plus a constant.** -/
def prime_reciprocal_upper : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 2 ≤ x →
    (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) ≤ Real.log (Real.log x) + B

end RNS.MertensSecond
