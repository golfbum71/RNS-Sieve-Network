/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BirchTateRational.Conclusions
import RNSNetwork.Nodes.UnitSquares24.Conclusions
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Tactic

/-!
# Proofs for BirchTateRational

Draft, 2026-11-22.

ζ(−1) from Mathlib's value of zeta at negative whole numbers through the
Bernoulli numbers (`riemannZeta_neg_nat_eq_bernoulli`, Bernoulli 2 = 1/6). The
largest cycle on which every open position squares to 1 is 24 by
`UnitSquares24.units_square_one_iff`, taken as a named hypothesis.
-/

namespace RNS.BirchTateRational

theorem zeta_neg_one_holds : zeta_neg_one := by
  unfold zeta_neg_one
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  norm_num [bernoulli_two] at h
  rw [h]
  norm_num

theorem w2_times_zeta_step (h : RNS.UnitSquares24.units_square_one_iff) (hz : zeta_neg_one) :
    w2_times_zeta := by
  refine ⟨24, by norm_num, (h 24 (by norm_num)).mpr dvd_rfl,
    fun k hk hu => Nat.le_of_dvd (by norm_num) ((h k hk).mp hu), rfl, ?_⟩
  unfold zeta_neg_one at hz
  rw [hz]
  norm_num

end RNS.BirchTateRational

#print axioms RNS.BirchTateRational.zeta_neg_one_holds
#print axioms RNS.BirchTateRational.w2_times_zeta_step
