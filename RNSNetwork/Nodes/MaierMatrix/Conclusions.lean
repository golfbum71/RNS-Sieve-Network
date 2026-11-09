/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# MaierMatrix — short windows with too many and too few primes

Maier's matrix: fix a set of prime wheels with cycle length `P` (their
product). The rows are the stretches from `r P + 1` to `r P + U`, one for each
row number `r`; the columns are the survivors of the wheels from 1 to `U`.
The entry in row `r` and column `c` is `r P + c`.

* **The double count.** Counting the prime entries row by row and column by
  column gives the same total.
* **A row's prime entries are all the primes of its window.** From the
  first row on, every prime in the window from `r P + 1` to `r P + U` is an
  entry of the matrix: a prime that large is no wheel, so no wheel divides it,
  and its column (the prime minus `r P`) survives. Each row of the matrix
  therefore counts the primes of a short window exactly.
* **Maier's theorem** (cited, not proved here). For every power above 1,
  windows of that power of the logarithm in length hold, infinitely often,
  noticeably more primes than the length over the logarithm, and infinitely
  often noticeably fewer. Maier's proof counts the matrix by columns, using
  the prime number theorem in progressions modulo `P`, and the number of
  columns differs from its expected share by an oscillating factor (the
  Buchstab function minus e to minus Euler's constant). Those analytic steps
  are not formalized.

Proof of the first two: `RNSSolutions/MaierMatrix.lean`. Rests on no other
node. Metadata: `formalization.yaml`.
-/

namespace RNS.MaierMatrix

/-- **The double count.** Over the rows `r` and the columns `c` (the
survivors of the wheels `W` from 1 to `U`), the prime entries `r P + c`
(`P` the product of the wheels) counted by rows equal those counted by
columns. -/
def maier_column_identity : Prop :=
  ∀ (W rows : Finset ℕ) (U : ℕ),
    ∑ r ∈ rows, ((survivors_upto W U).filter (fun c => (r * W.prod id + c).Prime)).card =
      ∑ c ∈ survivors_upto W U, (rows.filter (fun r => (r * W.prod id + c).Prime)).card

/-- **A row counts the primes of its window.** For prime wheels `W` with
product `P` and a row number `r` of at least 1, the prime entries of row `r`
are as many as the primes from `r P + 1` to `r P + U`. -/
def maier_row_count : Prop :=
  ∀ (W : Finset ℕ) (r U : ℕ), (∀ q ∈ W, q.Prime) → 1 ≤ r →
    ((survivors_upto W U).filter (fun c => (r * W.prod id + c).Prime)).card =
      ((Finset.Ioc (r * W.prod id) (r * W.prod id + U)).filter Nat.Prime).card

/-- The primes above `x` up to `x` plus the integer part of `(log x) ^ A`. -/
noncomputable def primes_in_window (x : ℕ) (A : ℝ) : ℕ :=
  ((Finset.Ioc x (x + ⌊Real.log x ^ A⌋₊)).filter Nat.Prime).card

/-- **Maier's theorem** (Maier 1985; cited). For every power `A` above 1 there
is a margin `δ > 0` such that, beyond every point, some window of length
`(log x) ^ A` holds at least `1 + δ` times `(log x) ^ (A - 1)` primes, and
some holds at most `1 - δ` times that. -/
def maier_irregularity : Prop :=
  ∀ A : ℝ, 1 < A → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℕ,
    (∃ x ≥ X, (1 + δ) * Real.log x ^ (A - 1) ≤ (primes_in_window x A : ℝ)) ∧
    (∃ x ≥ X, (primes_in_window x A : ℝ) ≤ (1 - δ) * Real.log x ^ (A - 1))

end RNS.MaierMatrix
