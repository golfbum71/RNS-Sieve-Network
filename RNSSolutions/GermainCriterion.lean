/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.GermainCriterion.Conclusions
import RNSNetwork.Nodes.Sawtooth.Conclusions
import RNSNetwork.Nodes.HurwitzZetaZero.Conclusions
import Mathlib.NumberTheory.LSeries.Nonvanishing   -- `LFunction_apply_one_ne_zero`, `rootNumber_ne_zero`
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset   -- `Finset.sum_powerset_insert`
import Mathlib.Data.Nat.ModEq                  -- `Nat.ModEq.mul_left`
import Mathlib.Data.Nat.GCD.BigOperators      -- `Nat.coprime_prod_left_iff`
import Mathlib.Tactic.DefEqTransformations     -- `beta_reduce`
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Proofs for GermainCriterion

Imports claims only, never other nodes' proofs. The sufficient direction rests
on `Sawtooth.even_split_iff_remainders_cancel`, taken as a named hypothesis.

Built clean by `lake build RNSSolutions` on 2026-11-05; `#print axioms` shows only
the standard three for every theorem here.

Idea. For the wheels `p`, `q`, the signed sum of `Sawtooth` has four terms:
the remainders of `a p q`, `a q`, `a p` and `a` on division by `k`, with signs
`+ - - +`. If `p` leaves remainder 1, the first two agree and so do the last
two. In the other case, `q` is the negative of `p` and `p q` is the negative
of 1, so the first and last remainders add up to `k` or are both 0, and so do
the middle two; and they are 0 together, since `p` shares no factor with `k`.
-/

namespace RNS.GermainCriterion

/-- The four-term form of the signed sum for two wheels. -/
private theorem pair_remainder_sum (p q k a : Nat) (hpq : p ≠ q) :
    ∑ S ∈ ({p, q} : Finset Nat).powerset,
        (-1 : Int) ^ S.card * ((a * (({p, q} : Finset Nat) \ S).prod id % k : Nat) : Int)
      = ((a * (p * q) % k : Nat) : Int) - ((a * q % k : Nat) : Int)
          - ((a * p % k : Nat) : Int) + ((a % k : Nat) : Int) := by
  have hnot : p ∉ ({q} : Finset Nat) := by
    simp only [Finset.mem_singleton]; exact hpq
  have hps : ({q} : Finset Nat).powerset = {∅, {q}} := by
    ext t
    simp only [Finset.mem_powerset, Finset.subset_singleton_iff, Finset.mem_insert,
      Finset.mem_singleton]
  have h0 : (∅ : Finset Nat) ≠ {q} := (Finset.singleton_ne_empty q).symm
  have e1 : ({p, q} : Finset Nat) \ {q} = {p} := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; aesop
  have e2 : ({p, q} : Finset Nat) \ {p} = {q} := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; aesop
  rw [Finset.sum_powerset_insert hnot, hps, Finset.sum_pair h0, Finset.sum_pair h0]
  simp only [Finset.card_empty, Finset.sdiff_empty, Finset.card_singleton, Finset.insert_empty,
    Finset.card_pair hpq, e1, e2, Finset.sdiff_self, Finset.prod_pair hpq,
    Finset.prod_singleton, Finset.prod_empty, id, pow_zero, pow_one, Nat.mul_one]
  ring

/-- Two remainders that add up to a multiple of `k` add up to 0 or to `k`. -/
private theorem pair_mod_cases {X W k : Nat} (hX : X < k) (hW : W < k)
    (h : (X + W) % k = 0) : X + W = 0 ∨ X + W = k := by
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · interval_cases t <;> simp_all
  · exfalso
    nlinarith

theorem two_wheel_split_of_remainders_step
    (h_cancel : RNS.Sawtooth.even_split_iff_remainders_cancel) :
    two_wheel_split_of_remainders := by
  intro p q k a hp hq hpq hk hcase
  have hW : ∀ r ∈ ({p, q} : Finset Nat), r.Prime := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hp
    · exact hq
  rw [h_cancel {p, q} k a hW, pair_remainder_sum p q k a hpq]
  rcases hcase with h1 | h1 | ⟨hsq, hneg⟩
  · -- `p` leaves remainder 1
    have hA : a * p % k = a % k := by
      have := Nat.ModEq.mul_left a h1
      simpa [Nat.ModEq] using this
    have hB : a * (p * q) % k = a * q % k := by
      have := Nat.ModEq.mul_left (a * q) h1
      have e : a * (p * q) = a * q * p := by ring
      rw [e]; simpa [Nat.ModEq] using this
    rw [hA, hB]; ring
  · -- `q` leaves remainder 1
    have hA : a * q % k = a % k := by
      have := Nat.ModEq.mul_left a h1
      simpa [Nat.ModEq] using this
    have hB : a * (p * q) % k = a * p % k := by
      have := Nat.ModEq.mul_left (a * p) h1
      have e : a * (p * q) = a * p * q := by ring
      rw [e]; simpa [Nat.ModEq] using this
    rw [hA, hB]; ring
  · -- `p * p` leaves remainder 1 and `p + q` is a multiple of `k`
    -- the four remainders
    set X := a * (p * q) % k with hXdef
    set Y := a * q % k with hYdef
    set Z := a * p % k with hZdef
    set W := a % k with hWdef
    have hX : X < k := Nat.mod_lt _ hk
    have hY : Y < k := Nat.mod_lt _ hk
    have hZ : Z < k := Nat.mod_lt _ hk
    have hWk : W < k := Nat.mod_lt _ hk
    -- `p q + 1` is a multiple of `k`
    have hpq1 : (p * q + 1) % k = 0 := by
      have e1 : (p * (p + q)) % k = 0 := by
        rw [Nat.mul_mod, hneg, Nat.mul_zero, Nat.zero_mod]
      have e2 : (p * p + p * q) % k = 0 := by
        have e : p * (p + q) = p * p + p * q := by ring
        rw [← e]; exact e1
      have e3 : (p * p + p * q) % k = (1 + p * q) % k := by
        rw [Nat.add_mod, hsq, ← Nat.add_mod]
      rw [Nat.add_comm]; rw [← e3]; exact e2
    have hXW : (X + W) % k = 0 := by
      rw [hXdef, hWdef, ← Nat.add_mod]
      have e : a * (p * q) + a = a * (p * q + 1) := by ring
      rw [e, Nat.mul_mod, hpq1, Nat.mul_zero, Nat.zero_mod]
    have hYZ : (Y + Z) % k = 0 := by
      rw [hYdef, hZdef, ← Nat.add_mod]
      have e : a * q + a * p = a * (p + q) := by ring
      rw [e, Nat.mul_mod, hneg, Nat.mul_zero, Nat.zero_mod]
    -- `W = 0` exactly when `Z = 0`, since `p` shares no factor with `k`
    have hWZ : W = 0 ↔ Z = 0 := by
      constructor
      · intro h
        rw [hZdef, Nat.mul_mod, ← hWdef, h, Nat.zero_mul, Nat.zero_mod]
      · intro h
        have h2 : a * p * p % k = 0 := by
          rw [Nat.mul_mod, ← hZdef, h, Nat.zero_mul, Nat.zero_mod]
        have h3 : a * p * p % k = a % k := by
          have := Nat.ModEq.mul_left a hsq
          have e : a * (p * p) = a * p * p := by ring
          rw [← e]; simpa [Nat.ModEq] using this
        rw [hWdef, ← h3, h2]
    rcases pair_mod_cases hX hWk hXW with h1 | h1 <;>
      rcases pair_mod_cases hY hZ hYZ with h2 | h2
    · have : X = 0 := by omega
      have : W = 0 := by omega
      have : Y = 0 := by omega
      have : Z = 0 := by omega
      omega
    · exfalso
      have hW0 : W = 0 := by omega
      have hZ0 := hWZ.mp hW0
      omega
    · exfalso
      have hZ0 : Z = 0 := by omega
      have hW0 := hWZ.mpr hZ0
      omega
    · omega

/-! ## The analytic input: odd primitive characters -/

/-- An odd character does not live modulo 1, and is not the trivial character. -/
private theorem odd_facts {N : Nat} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) : N ≠ 1 ∧ χ ≠ 1 := by
  have hN1 : N ≠ 1 := by
    rintro rfl
    have h1 : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
    have h := hodd
    unfold DirichletCharacter.Odd at h
    rw [h1, map_one] at h
    norm_num at h
  refine ⟨hN1, fun h => ?_⟩
  have hc := hprim
  rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hc
  exact hN1 hc.symm

theorem odd_primitive_LFunction_zero_ne_zero_holds : odd_primitive_LFunction_zero_ne_zero := by
  intro N _ χ hprim hodd
  obtain ⟨hN1, hχ1⟩ := odd_facts hprim hodd
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ1
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hg0 : DirichletCharacter.gammaFactor χ 0 ≠ 0 := by
    rw [hodd.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
  have hg1 : DirichletCharacter.gammaFactor χ⁻¹ 1 ≠ 0 := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hC1 : DirichletCharacter.completedLFunction χ⁻¹ 1 ≠ 0 := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ 1 (Or.inl one_ne_zero)
    have hL := DirichletCharacter.LFunction_apply_one_ne_zero hinv
    intro hc
    rw [hc, zero_div] at h
    exact hL h
  have hFE := hprim.completedLFunction_one_sub 1
  rw [sub_self] at hFE
  have hC0 : DirichletCharacter.completedLFunction χ 0 ≠ 0 := by
    rw [hFE]
    refine mul_ne_zero (mul_ne_zero ?_ (DirichletCharacter.rootNumber_ne_zero hprim)) hC1
    intro h
    exact hN0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hN1)]
  exact div_ne_zero hC0 hg0

theorem odd_primitive_weighted_sum_ne_zero_step
    (h_hz : RNS.HurwitzZetaZero.hurwitz_zeta_at_zero) :
    odd_primitive_weighted_sum_ne_zero := by
  intro N _ χ hprim hodd hsum
  obtain ⟨hN1, hχ1⟩ := odd_facts hprim hodd
  apply odd_primitive_LFunction_zero_ne_zero_holds N χ hprim hodd
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have key : ∀ j : ZMod N, χ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) 0
      = χ j * (1 / 2 - (j.val : ℂ) / N) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [χ.map_zero' hN1, zero_mul, zero_mul]
    · have hv : 0 < j.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero j).mpr hj)
      have hx0 : (0 : ℝ) < (j.val : ℝ) / N := div_pos (by exact_mod_cast hv) hNpos
      have hle : (j.val : ℝ) ≤ N := by exact_mod_cast (ZMod.val_lt j).le
      have hx1 : (j.val : ℝ) / N ≤ 1 := by
        calc (j.val : ℝ) / N ≤ (N : ℝ) / N := by gcongr
          _ = 1 := div_self (ne_of_gt hNpos)
      rw [ZMod.toAddCircle_apply, h_hz _ hx0 hx1]
      push_cast
      ring
  have hs0 : ∑ j : ZMod N, χ j = 0 := MulChar.sum_eq_zero_of_ne_one hχ1
  rw [DirichletCharacter.LFunction, ZMod.LFunction, neg_zero, Complex.cpow_zero, one_mul,
    Finset.sum_congr rfl (fun j _ => key j)]
  calc ∑ j : ZMod N, χ j * (1 / 2 - (j.val : ℂ) / N)
      = (∑ j : ZMod N, χ j) * (1 / 2) - (∑ j : ZMod N, χ j * (j.val : ℂ)) / N := by
        rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = 0 := by rw [hs0, hsum]; simp

/-! ## The character transform -/

/-- One wheel term of the transform: multiplying every residue by a unit `m`
permutes the residues, so the weighted remainder sum picks up the factor `χ m`. -/
private theorem transform_one_term {k : Nat} [NeZero k] (χ : DirichletCharacter ℂ k) (m : Nat)
    (hm : Nat.Coprime m k) :
    ∑ j : ZMod k, χ⁻¹ j * ((j.val * m % k : Nat) : ℂ)
      = χ (m : ZMod k) * ∑ i : ZMod k, χ⁻¹ i * (i.val : ℂ) := by
  obtain ⟨u, hu⟩ : ∃ u : (ZMod k)ˣ, (u : ZMod k) = m :=
    ⟨ZMod.unitOfCoprime m hm, ZMod.coe_unitOfCoprime m hm⟩
  have hval : ∀ j : ZMod k, j.val * m % k = (j * (u : ZMod k)).val := by
    intro j
    rw [hu, ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod, Nat.mul_mod j.val (m % k), Nat.mod_mod]
  have hχu : χ⁻¹ (u : ZMod k) * χ (u : ZMod k) = 1 := by
    rw [← MulChar.mul_apply, MulChar.inv_mul, MulChar.one_apply_coe]
  have hT : ∑ i : ZMod k, χ⁻¹ i * (i.val : ℂ)
      = χ⁻¹ (u : ZMod k) * ∑ j : ZMod k, χ⁻¹ j * ((j * (u : ZMod k)).val : ℂ) := by
    rw [← Equiv.sum_comp (Units.mulRight u) (fun i : ZMod k => χ⁻¹ i * (i.val : ℂ)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Units.mulRight_apply, map_mul]
    ring
  calc ∑ j : ZMod k, χ⁻¹ j * ((j.val * m % k : Nat) : ℂ)
      = ∑ j : ZMod k, χ⁻¹ j * ((j * (u : ZMod k)).val : ℂ) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hval j]
    _ = χ (u : ZMod k) * ∑ i : ZMod k, χ⁻¹ i * (i.val : ℂ) := by
        rw [hT, ← mul_assoc, mul_comm (χ (u : ZMod k)), hχu, one_mul]
    _ = χ (m : ZMod k) * ∑ i : ZMod k, χ⁻¹ i * (i.val : ℂ) := by
        rw [hu]

/-- The product over the wheels of `χ(wheel) - 1`, expanded over the choices
of wheels, in the same signed form as `Sawtooth`. -/
private theorem wheel_product_expand {k : Nat} (χ : DirichletCharacter ℂ k) (W : Finset Nat) :
    ∏ p ∈ W, (χ (p : ZMod k) - 1)
      = ∑ S ∈ W.powerset, (-1 : ℂ) ^ S.card * χ (((W \ S).prod id : Nat) : ZMod k) := by
  have h := Finset.prod_add (fun _ : Nat => (-1 : ℂ)) (fun p => χ (p : ZMod k)) W
  beta_reduce at h
  rw [show (∏ p ∈ W, (χ (p : ZMod k) - 1)) = ∏ p ∈ W, ((-1 : ℂ) + χ (p : ZMod k)) from
    Finset.prod_congr rfl (fun p _ => by ring), h]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.prod_const, Nat.cast_prod, map_prod]
  rfl

theorem character_transform_holds : character_transform := by
  intro k _ W χ hW hWk
  have hcop : ∀ S ∈ W.powerset, Nat.Coprime ((W \ S).prod id) k := by
    intro S _
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    have hpW := (Finset.mem_sdiff.mp hp).1
    exact (Nat.Prime.coprime_iff_not_dvd (hW p hpW)).mpr (hWk p hpW)
  have hL : ∀ j : ZMod k, χ⁻¹ j * (((∑ S ∈ W.powerset,
        (-1 : Int) ^ S.card * ((j.val * (W \ S).prod id % k : Nat) : Int) : Int)) : ℂ)
      = ∑ S ∈ W.powerset, (-1 : ℂ) ^ S.card * (χ⁻¹ j * ((j.val * (W \ S).prod id % k : Nat) : ℂ)) := by
    intro j
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun S _ => by ring)
  rw [wheel_product_expand χ W, Finset.sum_mul, Finset.sum_congr rfl (fun j _ => hL j),
    Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [← Finset.mul_sum, transform_one_term χ _ (hcop S hS)]
  ring

/-! ## Characters that are not primitive (Germain's (3.2)) -/

/-- An odd character does not live modulo 1, and is not the trivial character
(no primitivity needed). -/
private theorem odd_level_and_nontrivial {N : Nat} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (hodd : ψ.Odd) : N ≠ 1 ∧ ψ ≠ 1 := by
  have hN1 : N ≠ 1 := by
    rintro rfl
    have h1 : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
    have h := hodd
    unfold DirichletCharacter.Odd at h
    rw [h1, map_one] at h
    norm_num at h
  refine ⟨hN1, fun h => ?_⟩
  have h2 := hodd
  unfold DirichletCharacter.Odd at h2
  rw [h, MulChar.one_apply (isUnit_one.neg)] at h2
  norm_num at h2

theorem weighted_sum_eq_LFunction_zero_step
    (h_hz : RNS.HurwitzZetaZero.hurwitz_zeta_at_zero) :
    weighted_sum_eq_LFunction_zero := by
  intro N _ ψ hN1 hψ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : ∀ j : ZMod N, ψ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) 0
      = ψ j * (1 / 2 - (j.val : ℂ) / N) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [ψ.map_zero' hN1, zero_mul, zero_mul]
    · have hv : 0 < j.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero j).mpr hj)
      have hx0 : (0 : ℝ) < (j.val : ℝ) / N := div_pos (by exact_mod_cast hv) hNpos
      have hle : (j.val : ℝ) ≤ N := by exact_mod_cast (ZMod.val_lt j).le
      have hx1 : (j.val : ℝ) / N ≤ 1 := by
        calc (j.val : ℝ) / N ≤ (N : ℝ) / N := by gcongr
          _ = 1 := div_self (ne_of_gt hNpos)
      rw [ZMod.toAddCircle_apply, h_hz _ hx0 hx1]
      push_cast
      ring
  have hs0 : ∑ j : ZMod N, ψ j = 0 := MulChar.sum_eq_zero_of_ne_one hψ
  have hsplit : ∑ j : ZMod N, ψ j * (1 / 2 - (j.val : ℂ) / N)
      = (∑ j : ZMod N, ψ j) * (1 / 2) - (∑ j : ZMod N, ψ j * (j.val : ℂ)) / N := by
    rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [DirichletCharacter.LFunction, ZMod.LFunction, neg_zero, Complex.cpow_zero, one_mul,
    Finset.sum_congr rfl (fun j _ => key j), hsplit, hs0, zero_mul, zero_sub]
  field_simp

theorem odd_weighted_sum_ne_zero_iff_step
    (h_hz : RNS.HurwitzZetaZero.hurwitz_zeta_at_zero) :
    odd_weighted_sum_ne_zero_iff := by
  intro k _ ψ hodd
  obtain ⟨hk1, hψ1⟩ := odd_level_and_nontrivial hodd
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  -- the primitive character behind `ψ` is odd and primitive
  have hσodd : ψ.primitiveCharacter.Odd := by
    have h := ψ.primitiveCharacter_apply_of_isCoprime (a := -1) isCoprime_one_left.neg_left
    unfold DirichletCharacter.Odd
    push_cast at h
    rw [h]
    exact hodd
  have hLσ := odd_primitive_LFunction_zero_ne_zero_holds ψ.conductor ψ.primitiveCharacter
    ψ.primitiveCharacter_isPrimitive hσodd
  -- move L(ψ, 0) to the primitive character
  have hL := DirichletCharacter.LFunction_changeLevel ψ.conductor_dvd_level ψ.primitiveCharacter
    (s := 0) (Or.inr zero_ne_one)
  rw [ψ.changeLevel_primitiveCharacter] at hL
  simp only [neg_zero, Complex.cpow_zero, mul_one] at hL
  rw [weighted_sum_eq_LFunction_zero_step h_hz k ψ hk1 hψ1, hL]
  constructor
  · intro h p hp hσp
    apply h
    rw [Finset.prod_eq_zero hp (by rw [hσp, sub_self]), mul_zero, mul_zero]
  · intro h
    refine mul_ne_zero (neg_ne_zero.mpr hk0) (mul_ne_zero hLσ ?_)
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => sub_ne_zero.mpr (Ne.symm (h p hp)))

end RNS.GermainCriterion

#print axioms RNS.GermainCriterion.two_wheel_split_of_remainders_step
#print axioms RNS.GermainCriterion.odd_primitive_LFunction_zero_ne_zero_holds
#print axioms RNS.GermainCriterion.odd_primitive_weighted_sum_ne_zero_step
#print axioms RNS.GermainCriterion.character_transform_holds
#print axioms RNS.GermainCriterion.weighted_sum_eq_LFunction_zero_step
#print axioms RNS.GermainCriterion.odd_weighted_sum_ne_zero_iff_step
