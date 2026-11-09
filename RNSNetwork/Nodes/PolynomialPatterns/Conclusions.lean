/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# PolynomialPatterns — polynomial patterns and the Bateman–Horn conjecture

A pattern of offsets asks that the candidate number plus each offset be
prime. A polynomial pattern asks that each polynomial, evaluated at the
candidate number, be prime: for example the candidate number squared plus 1.
A wheel then blocks the positions where some polynomial of the pattern is
divisible by the wheel, the roots of the polynomials on that wheel, and
admissibility asks that no wheel be fully blocked.

* **The finite check.** If no prime divides every coefficient of any of the
  polynomials, only the wheels up to the total degree need checking: a larger
  wheel cannot be fully blocked, because each polynomial has at most its
  degree in roots on it.
* **The square plus one is admissible.** Its degree is 2, and on the wheel 2
  it blocks only the position 1.
* **Landau's fourth problem from Bateman–Horn.** Bateman and Horn's
  conjecture, for the single polynomial "square plus one", predicts the count
  of positions up to `x` where it is prime: half its constant times `x` over
  the logarithm of `x`. Its constant is the limit of the products over the
  wheels of one minus the blocked share, over one minus one over the wheel.
  That this limit exists and is positive is a theorem (it rests on how the
  primes split between remainders 1 and 3 on division by 4), but it is not
  proved here, so it enters as a second hypothesis. Together they give
  infinitely many primes that are a square plus one.

Proof: `RNSSolutions/PolynomialPatterns.lean`. Rests on no other node; the
two conjectural inputs are named hypotheses of `landau_of_bateman_horn`.
Metadata: `formalization.yaml`.
-/

namespace RNS.PolynomialPatterns

open Polynomial Filter Topology Asymptotics

open Classical in
/-- The positions on the wheel of size `p` blocked by the polynomial pattern
`F`: the remainders where some polynomial of `F` is divisible by `p`. -/
noncomputable def poly_blocked (F : Finset ℤ[X]) (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter (fun r : ℕ => ∃ f ∈ F, (p : ℤ) ∣ f.eval (r : ℤ))

/-- A polynomial pattern is admissible when no prime wheel is fully blocked. -/
def poly_admissible (F : Finset ℤ[X]) : Prop :=
  ∀ p : ℕ, p.Prime → (poly_blocked F p).card < p

/-- No prime divides every coefficient of `f`. -/
def coeffs_coprime (f : ℤ[X]) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ i, ¬ (p : ℤ) ∣ f.coeff i

/-- **The finite check.** For polynomials none of whose coefficients share a
prime factor, admissibility needs checking only on the wheels up to the total
degree. -/
def poly_admissible_iff : Prop :=
  ∀ F : Finset ℤ[X], (∀ f ∈ F, coeffs_coprime f) →
    (poly_admissible F ↔
      ∀ p : ℕ, p.Prime → p ≤ ∑ f ∈ F, f.natDegree → (poly_blocked F p).card < p)

/-- **The square plus one is admissible.** -/
def sq_add_one_admissible : Prop :=
  poly_admissible {X ^ 2 + 1}

/-- The positions from 1 to `x` where the square plus one is prime. -/
def sq_add_one_count (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => (n ^ 2 + 1).Prime)).card

/-- The Bateman–Horn product for the square plus one over the wheels below
`z`: one minus the blocked share, over one minus one over the wheel. -/
noncomputable def sq_add_one_partial (z : ℕ) : ℝ :=
  ∏ p ∈ active_primes z,
    (1 - ((poly_blocked {X ^ 2 + 1} p).card : ℝ) / (p : ℝ)) / (1 - 1 / (p : ℝ))

/-- **The constant exists and is positive** (a theorem, not proved here; a
named hypothesis). -/
def sq_add_one_constant_converges : Prop :=
  ∃ C : ℝ, 0 < C ∧ Tendsto sq_add_one_partial atTop (𝓝 C)

/-- **The Bateman–Horn conjecture for the square plus one** (open; a named
hypothesis). With the constant the limit of the products, the count up to `x`
is asymptotic to half the constant times `x` over the logarithm of `x`. -/
def bateman_horn_sq_add_one : Prop :=
  ∀ C : ℝ, Tendsto sq_add_one_partial atTop (𝓝 C) →
    (fun x : ℕ => (sq_add_one_count x : ℝ)) ~[atTop] (fun x : ℕ => C / 2 * (x : ℝ) / Real.log x)

/-- **Landau's fourth problem, from Bateman–Horn.** If the constant exists and
is positive, and the Bateman–Horn conjecture holds for the square plus one,
there are infinitely many primes that are a square plus one. -/
def landau_of_bateman_horn : Prop :=
  sq_add_one_constant_converges → bateman_horn_sq_add_one →
    Set.Infinite {n : ℕ | (n ^ 2 + 1).Prime}

end RNS.PolynomialPatterns
