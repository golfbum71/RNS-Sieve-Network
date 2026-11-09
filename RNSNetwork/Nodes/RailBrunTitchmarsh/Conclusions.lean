/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunTitchmarshPNT.Conclusions

/-!
# RailBrunTitchmarsh — primes in a short window of one column

The two columns of the 6n±1 wheel are the numbers leaving remainder 5 and
remainder 1 on division by 6. How many primes can one column hold in a window
of a given length, wherever the window sits?

* **A column holds at most the window's primes.** The column primes in a
  window are among all the primes in it.
* **The first bound.** So PNT+'s window bound for all primes (twice the
  length over the logarithm of the sieve level, plus an error) bounds each
  column too. This is the weaker form; the sharper one, about the length over
  the logarithm of five sixths of the length (Brun–Titchmarsh for the modulus
  6), needs a Selberg sieve on one column and is not proved here.

Proof: `RNSSolutions/RailBrunTitchmarsh.lean`. The first bound rests on
`BrunTitchmarshPNT` (an outside claim from PNT+), joined in `Assemble`.
Metadata: `formalization.yaml`.
-/

namespace RNS.RailBrunTitchmarsh

/-- The primes from `a` to `b` (both ends included) in the column leaving
remainder `r` on division by 6. -/
def column_primes_between (r : ℕ) (a b : ℝ) : ℕ :=
  ((Finset.Icc (Nat.ceil a) (Nat.floor b)).filter (fun n => n.Prime ∧ n % 6 = r)).card

/-- **A column holds at most the window's primes.** -/
def column_window_le_all : Prop :=
  ∀ (r : ℕ) (a b : ℝ), column_primes_between r a b ≤ RNS.BrunTitchmarshPNT.primesBetween a b

/-- **The first bound for one column.** For a window of length `y > 0`
starting at `x > 0` and any sieve level `z > 1`, the primes of one column in
the window are at most twice `y` over the logarithm of `z`, plus `6 z` times
`(1 + log z)` cubed. -/
def column_window_weak : Prop :=
  ∀ (r : ℕ) (x y z : ℝ), 0 < x → 0 < y → 1 < z →
    (column_primes_between r x (x + y) : ℝ) ≤ 2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3

end RNS.RailBrunTitchmarsh
