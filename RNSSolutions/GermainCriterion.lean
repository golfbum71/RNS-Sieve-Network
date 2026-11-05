/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.GermainCriterion.Conclusions
import RNSNetwork.Nodes.Sawtooth.Conclusions
import RNSNetwork.Nodes.HurwitzZetaZero.Conclusions
import Mathlib.NumberTheory.LSeries.Nonvanishing   -- `LFunction_apply_one_ne_zero`, `rootNumber_ne_zero`
import Mathlib.NumberTheory.LSeries.PrimesInAP     -- character orthogonality over ℂ, with its instances
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
Germain's Theorem 1.1 (`germain_theorem_step`) rests on `Sawtooth` and on the
cited node `HurwitzZetaZero` (through Corollary 3.2).

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

/-! ## Inversion over characters and Germain's Proposition 3.1 -/

/-- `Sawtooth`'s signed remainder sum at the residue `j`. -/
private def remSum (k : Nat) (W : Finset Nat) (j : ZMod k) : Int :=
  ∑ S ∈ W.powerset, (-1 : Int) ^ S.card * ((j.val * (W \ S).prod id % k : Nat) : Int)

/-- The inverse of an odd character is odd. -/
private theorem inv_odd {k : Nat} {χ : DirichletCharacter ℂ k} (h : χ.Odd) : χ⁻¹.Odd := by
  unfold DirichletCharacter.Odd at *
  rw [MulChar.inv_apply_eq_inv', h]
  norm_num

/-- The inverse of an even character is even. -/
private theorem inv_even {k : Nat} {χ : DirichletCharacter ℂ k} (h : χ.Even) : χ⁻¹.Even := by
  unfold DirichletCharacter.Even at *
  rw [MulChar.inv_apply_eq_inv', h]
  norm_num

/-- For an even nontrivial character the weighted residue sum is 0: pairing each
residue with its negative turns the sum into the modulus times the plain sum,
minus itself. -/
private theorem weightedSum_even_eq_zero {k : Nat} [NeZero k] (ψ : DirichletCharacter ℂ k)
    (heven : ψ.Even) (hψ : ψ ≠ 1) : ∑ j : ZMod k, ψ j * (j.val : ℂ) = 0 := by
  have hk1 : k ≠ 1 := fun h => hψ (DirichletCharacter.level_one' ψ h)
  have hs0 : ∑ j : ZMod k, ψ j = 0 := MulChar.sum_eq_zero_of_ne_one hψ
  have hneg : ∑ j : ZMod k, ψ j * (j.val : ℂ) = ∑ j : ZMod k, ψ j * ((k : ℂ) - j.val) := by
    rw [← Equiv.sum_comp (Equiv.neg (ZMod k)) (fun j : ZMod k => ψ j * (j.val : ℂ))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Equiv.neg_apply]
    rw [DirichletCharacter.Even.eval_neg ψ j heven]
    by_cases hj : j = 0
    · subst hj
      rw [ψ.map_zero' hk1, zero_mul, zero_mul]
    · rw [ZMod.neg_val, if_neg hj, Nat.cast_sub (ZMod.val_lt j).le]
  have hsum : ∑ j : ZMod k, ψ j * ((k : ℂ) - j.val)
      = (∑ j : ZMod k, ψ j) * k - ∑ j : ZMod k, ψ j * (j.val : ℂ) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum, hs0, zero_mul, zero_sub] at hneg
  have h2 : (2 : ℂ) * ∑ j : ZMod k, ψ j * (j.val : ℂ) = 0 := by linear_combination hneg
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-- At a unit, the inverse character is the character at the inverse residue. -/
private theorem inv_apply_unit {k : Nat} (χ : DirichletCharacter ℂ k) {j : ZMod k}
    (hj : IsUnit j) : χ⁻¹ j = χ j⁻¹ := by
  obtain ⟨u, rfl⟩ := hj
  rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]

/-- The orthogonality kernel: summing `χ⁻¹ j * χ a` over all characters gives
`φ(k)` when `j = a` and 0 otherwise, for a unit `a`. -/
private theorem char_sum_kernel {k : Nat} [NeZero k] {a : ZMod k} (ha : IsUnit a) (j : ZMod k) :
    ∑ χ : DirichletCharacter ℂ k, χ⁻¹ j * χ a = if j = a then (k.totient : ℂ) else 0 := by
  by_cases hj : IsUnit j
  · have h : ∀ χ : DirichletCharacter ℂ k, χ⁻¹ j * χ a = χ j⁻¹ * χ a := fun χ => by
      rw [inv_apply_unit χ hj]
    simp only [h]
    exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hj a
  · have hne : j ≠ a := fun h => hj (h ▸ ha)
    rw [if_neg hne]
    exact Finset.sum_eq_zero (fun χ _ => by rw [MulChar.map_nonunit _ hj, zero_mul])

theorem coprime_split_iff_characters_step
    (h_hz : RNS.HurwitzZetaZero.hurwitz_zeta_at_zero) :
    coprime_split_iff_characters := by
  intro k _ W hWne hW hWk
  have hT : ∀ χ : DirichletCharacter ℂ k,
      ∑ j : ZMod k, χ⁻¹ j * ((remSum k W j : Int) : ℂ)
        = (∏ p ∈ W, (χ (p : ZMod k) - 1)) * ∑ i : ZMod k, χ⁻¹ i * (i.val : ℂ) :=
    fun χ => character_transform_holds k W χ hW hWk
  have hiff := odd_weighted_sum_ne_zero_iff_step h_hz k
  change (∀ j : ZMod k, IsUnit j → remSum k W j = 0) ↔ _
  constructor
  · -- vanishing at every unit forces the character condition
    intro hF χ hodd
    by_contra hcon
    obtain ⟨h1, h2⟩ := not_or.mp hcon
    have hprod : ∏ p ∈ W, (χ (p : ZMod k) - 1) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun p hp => sub_ne_zero.mpr (fun he => h1 ⟨p, hp, he⟩))
    have hS : ∑ i : ZMod k, χ⁻¹ i * (i.val : ℂ) ≠ 0 :=
      (hiff χ⁻¹ (inv_odd hodd)).mpr (fun p hp he => h2 ⟨p, hp, he⟩)
    have hT0 : ∑ j : ZMod k, χ⁻¹ j * ((remSum k W j : Int) : ℂ) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hj : IsUnit j
      · rw [hF j hj, Int.cast_zero, mul_zero]
      · rw [MulChar.map_nonunit _ hj, zero_mul]
    rw [hT χ] at hT0
    exact mul_ne_zero hprod hS hT0
  · -- the character condition makes every transform vanish; invert
    intro hχ a ha
    have hall : ∀ χ : DirichletCharacter ℂ k,
        ∑ j : ZMod k, χ⁻¹ j * ((remSum k W j : Int) : ℂ) = 0 := by
      intro χ
      rw [hT χ]
      rcases χ.even_or_odd with heven | hodd
      · by_cases h1 : χ = 1
        · obtain ⟨p, hp⟩ := hWne
          have hcop : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd (hW p hp)).mpr (hWk p hp)
          have hunit : IsUnit (p : ZMod k) := by
            rw [← ZMod.coe_unitOfCoprime p hcop]
            exact Units.isUnit _
          rw [Finset.prod_eq_zero hp (by rw [h1, MulChar.one_apply hunit, sub_self]), zero_mul]
        · rw [weightedSum_even_eq_zero χ⁻¹ (inv_even heven) (inv_ne_one.mpr h1), mul_zero]
      · rcases hχ χ hodd with ⟨p, hp, hp1⟩ | ⟨p, hp, hp1⟩
        · rw [Finset.prod_eq_zero hp (by rw [hp1, sub_self]), zero_mul]
        · have hz : ∑ i : ZMod k, χ⁻¹ i * (i.val : ℂ) = 0 := by
            by_contra hne
            exact (hiff χ⁻¹ (inv_odd hodd)).mp hne p hp hp1
          rw [hz, mul_zero]
    have key : (k.totient : ℂ) * ((remSum k W a : Int) : ℂ) = 0 := by
      have h0 : ∑ χ : DirichletCharacter ℂ k,
          χ a * ∑ j : ZMod k, χ⁻¹ j * ((remSum k W j : Int) : ℂ) = 0 :=
        Finset.sum_eq_zero (fun χ _ => by rw [hall χ, mul_zero])
      rw [← h0]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have hj : ∀ j : ZMod k, ∑ χ : DirichletCharacter ℂ k,
          χ a * (χ⁻¹ j * ((remSum k W j : Int) : ℂ))
            = (if j = a then (k.totient : ℂ) else 0) * ((remSum k W j : Int) : ℂ) := by
        intro j
        rw [← char_sum_kernel ha j, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun χ _ => by ring)
      rw [Finset.sum_congr rfl (fun j _ => hj j)]
      simp
    have hφ : (k.totient : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))).ne'
    exact_mod_cast (mul_eq_zero.mp key).resolve_left hφ

/-! ## Germain's Corollary 3.2: every residue, wheels only -/

/-- The signed remainder sum at a natural-number residue `a`. -/
private def remSumN (k : Nat) (W : Finset Nat) (a : Nat) : Int :=
  ∑ S ∈ W.powerset, (-1 : Int) ^ S.card * ((a * (W \ S).prod id % k : Nat) : Int)

/-- Multiplying the residue and the number of parts by the same factor
multiplies every remainder, and so the whole sum, by that factor. -/
private theorem remSumN_scale (d k' b : Nat) (W : Finset Nat) :
    remSumN (d * k') W (d * b) = (d : Int) * remSumN k' W b := by
  unfold remSumN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Nat.mul_assoc, Nat.mul_mod_mul_left, Nat.cast_mul]
  ring

/-- Only the residue's remainder matters. -/
private theorem remSumN_mod (k b : Nat) (W : Finset Nat) :
    remSumN k W (b % k) = remSumN k W b := by
  unfold remSumN
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- A primitive character is 0, so not 1, at a prime dividing its level. -/
private theorem primitive_ne_one_at_prime_dvd {N : Nat} (ψ : DirichletCharacter ℂ N)
    (hψ : ψ.IsPrimitive) {q : Nat} (hq : q.Prime) (hqN : q ∣ N) :
    ψ.primitiveCharacter (q : ZMod ψ.conductor) ≠ 1 := by
  have hc : ψ.conductor = N := hψ
  have hnu : ¬ IsUnit (q : ZMod ψ.conductor) := by
    rw [ZMod.isUnit_iff_coprime, hc]
    exact fun h => (Nat.Prime.coprime_iff_not_dvd hq).mp h hqN
  rw [MulChar.map_nonunit _ hnu]
  exact zero_ne_one

/-- The primitive character behind an odd character is odd. -/
private theorem primitive_odd {N : Nat} {ψ : DirichletCharacter ℂ N} (hodd : ψ.Odd) :
    ψ.primitiveCharacter.Odd := by
  have h := ψ.primitiveCharacter_apply_of_isCoprime (a := -1) isCoprime_one_left.neg_left
  unfold DirichletCharacter.Odd
  push_cast at h
  rw [h]
  exact hodd

/-- Lifting an odd character to a multiple of its level keeps it odd. -/
private theorem changeLevel_odd {n m : Nat} (hm : n ∣ m) {χ : DirichletCharacter ℂ n}
    (hodd : χ.Odd) : (DirichletCharacter.changeLevel hm χ).Odd := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hm
    (a := -1) isCoprime_one_left.neg_left
  unfold DirichletCharacter.Odd
  push_cast at h
  rw [h]
  exact hodd

theorem all_residues_split_iff_wheels_step
    (h_hz : RNS.HurwitzZetaZero.hurwitz_zeta_at_zero) :
    all_residues_split_iff_wheels := by
  intro k _ W hWne hW hWk
  have h31 := coprime_split_iff_characters_step h_hz
  change (∀ a : Nat, remSumN k W a = 0) ↔ _
  have hk0 : k ≠ 0 := NeZero.ne k
  have hpZ : ∀ p ∈ W, IsCoprime (p : ℤ) (k : ℤ) := fun p hp =>
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd (hW p hp)).mpr (hWk p hp))
  constructor
  · -- every residue splits evenly: pass to the conductor of `χ⁻¹`
    intro hF χ hodd
    haveI : NeZero χ⁻¹.conductor := ⟨χ⁻¹.conductor_ne_zero⟩
    have hψodd : (χ⁻¹.primitiveCharacter).Odd := primitive_odd (inv_odd hodd)
    obtain ⟨d, hd⟩ := χ⁻¹.conductor_dvd_level
    have hk' : d * χ⁻¹.conductor = k := by
      rw [Nat.mul_comm]
      exact hd.symm
    have hd0 : (d : Int) ≠ 0 := by
      have : d ≠ 0 := by
        rintro rfl
        exact hk0 (hd.trans (Nat.mul_zero _))
      exact_mod_cast this
    have hWf : ∀ p ∈ W, ¬ p ∣ χ⁻¹.conductor := fun p hp h =>
      hWk p hp (h.trans χ⁻¹.conductor_dvd_level)
    have hsplit : ∀ j : ZMod χ⁻¹.conductor, IsUnit j →
        ∑ S ∈ W.powerset, (-1 : Int) ^ S.card *
          ((j.val * (W \ S).prod id % χ⁻¹.conductor : Nat) : Int) = 0 := by
      intro j _
      have hs := remSumN_scale d χ⁻¹.conductor j.val W
      rw [hk', hF] at hs
      exact (mul_eq_zero.mp hs.symm).resolve_left hd0
    rcases (h31 χ⁻¹.conductor W hWne hW hWf).mp hsplit ((χ⁻¹.primitiveCharacter)⁻¹)
        (inv_odd hψodd) with ⟨p, hp, hp1⟩ | ⟨q, hq, hq1⟩
    · refine ⟨p, hp, ?_⟩
      rw [MulChar.inv_apply_eq_inv', inv_eq_one] at hp1
      have h2 := χ⁻¹.primitiveCharacter_apply_of_isCoprime (hpZ p hp)
      simp only [Int.cast_natCast] at h2
      rw [hp1, MulChar.inv_apply_eq_inv', eq_comm, inv_eq_one] at h2
      exact h2
    · exfalso
      have hprim : ((χ⁻¹.primitiveCharacter)⁻¹)⁻¹.IsPrimitive := by
        rw [inv_inv]
        exact χ⁻¹.primitiveCharacter_isPrimitive
      exact primitive_ne_one_at_prime_dvd _ hprim (Nat.prime_of_mem_primeFactors hq)
        (Nat.dvd_of_mem_primeFactors hq) hq1
  · -- the wheel condition: divide out the common factor of the residue and `k`
    intro hχ a
    have hg0 : 0 < Nat.gcd a k := Nat.gcd_pos_of_pos_right a (Nat.pos_of_ne_zero hk0)
    have ha : Nat.gcd a k * (a / Nat.gcd a k) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a k)
    have hk : Nat.gcd a k * (k / Nat.gcd a k) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_right a k)
    have hcop : Nat.Coprime (a / Nat.gcd a k) (k / Nat.gcd a k) :=
      Nat.coprime_div_gcd_div_gcd hg0
    generalize a / Nat.gcd a k = b at ha hcop
    generalize k / Nat.gcd a k = k' at hk hcop
    generalize Nat.gcd a k = g at ha hk hg0
    have hk'0 : k' ≠ 0 := by
      rintro rfl
      exact hk0 (hk.symm.trans (Nat.mul_zero g))
    haveI : NeZero k' := ⟨hk'0⟩
    have hdvd : k' ∣ k := ⟨g, by rw [← hk, Nat.mul_comm]⟩
    have hWk' : ∀ p ∈ W, ¬ p ∣ k' := fun p hp h => hWk p hp (h.trans hdvd)
    have hcond : ∀ χ : DirichletCharacter ℂ k', χ.Odd →
        (∃ p ∈ W, χ (p : ZMod k') = 1) ∨
        (∃ p ∈ k'.primeFactors, χ⁻¹.primitiveCharacter (p : ZMod χ⁻¹.conductor) = 1) := by
      intro χ hodd
      left
      obtain ⟨p, hp, hp1⟩ := hχ (DirichletCharacter.changeLevel hdvd χ) (changeLevel_odd hdvd hodd)
      refine ⟨p, hp, ?_⟩
      have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hdvd (hpZ p hp)
      simp only [Int.cast_natCast] at h2
      rw [← h2]
      exact hp1
    have hunit : IsUnit (b : ZMod k') := (ZMod.isUnit_iff_coprime b k').mpr hcop
    have h0 : remSumN k' W ((b : ZMod k').val) = 0 :=
      (h31 k' W hWne hW hWk').mpr hcond (b : ZMod k') hunit
    rw [ZMod.val_natCast, remSumN_mod] at h0
    rw [← ha, ← hk, remSumN_scale, h0, mul_zero]

/-! ## Germain's Proposition 2.1 (c), (d), (e) -/

/-- Adding a wheel `q`: the sum at `a` becomes the sum at `a·q` minus the sum
at `a`. -/
private theorem remSumN_insert (k : Nat) (W : Finset Nat) (q a : Nat) (hq : q ∉ W) :
    remSumN k (insert q W) a = remSumN k W (a * q) - remSumN k W a := by
  unfold remSumN
  rw [Finset.sum_powerset_insert hq, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl (fun S hS => ?_)
    have hqS : q ∉ S := fun h => hq (Finset.mem_powerset.mp hS h)
    have hqWS : q ∉ W \ S := fun h => hq (Finset.mem_sdiff.mp h).1
    rw [Finset.insert_sdiff_of_notMem _ hqS, Finset.prod_insert hqWS, ← Nat.mul_assoc]
    rfl
  · refine Finset.sum_congr rfl (fun S hS => ?_)
    have hqS : q ∉ S := fun h => hq (Finset.mem_powerset.mp hS h)
    rw [Finset.card_insert_of_notMem hqS, Finset.insert_sdiff_insert,
      Finset.sdiff_insert_of_notMem hq, pow_succ]
    ring

/-- Shifting by multiples of `m` permutes the remainders on division by `p`,
when `m` shares no factor with `p`. -/
private theorem sum_mod_shift (p m c : Nat) (hp : 0 < p) (hm : Nat.Coprime m p) :
    ∑ i ∈ Finset.range p, (c + i * m) % p = ∑ h ∈ Finset.range p, h := by
  have hinj : Set.InjOn (fun i => (c + i * m) % p) (Finset.range p : Set Nat) := by
    intro x hx y hy hxy
    have h1 : c + x * m ≡ c + y * m [MOD p] := hxy
    have h2 : x * m ≡ y * m [MOD p] := Nat.ModEq.add_left_cancel' c h1
    have h3 : x ≡ y [MOD p] := Nat.ModEq.cancel_right_of_coprime hm.symm h2
    have hx' := Finset.mem_range.mp (Finset.mem_coe.mp hx)
    have hy' := Finset.mem_range.mp (Finset.mem_coe.mp hy)
    unfold Nat.ModEq at h3
    rwa [Nat.mod_eq_of_lt hx', Nat.mod_eq_of_lt hy'] at h3
  have himg : (Finset.range p).image (fun i => (c + i * m) % p) = Finset.range p := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
    · exact (Finset.card_image_of_injOn hinj).ge
  calc ∑ i ∈ Finset.range p, (c + i * m) % p
      = ∑ h ∈ (Finset.range p).image (fun i => (c + i * m) % p), h :=
        (Finset.sum_image (f := fun h => h) hinj).symm
    _ = ∑ h ∈ Finset.range p, h := by rw [himg]

/-- Averaging over the residues `a, a + k₁, …, a + (p-1)·k₁` modulo `p·k₁`:
twice the sum of the remainders of `(a + i·k₁)·m` is fixed. -/
private theorem sum_shift_mod_mul (p k1 a m : Nat) (hp : 0 < p) (hk1 : 0 < k1)
    (hm : Nat.Coprime m p) :
    2 * ∑ i ∈ Finset.range p, (a + i * k1) * m % (p * k1)
      = 2 * p * (a * m % k1) + k1 * (p * (p - 1)) := by
  have hterm : ∀ i, (a + i * k1) * m % (p * k1)
      = a * m % k1 + k1 * ((a * m / k1 + i * m) % p) := by
    intro i
    have hx : (a + i * k1) * m = a * m + i * m * k1 := by ring
    have e1 := Nat.mod_add_div ((a * m + i * m * k1) % (k1 * p)) k1
    rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right k1 p), Nat.mod_mul_right_div_self,
      Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hk1] at e1
    rw [hx, Nat.mul_comm p k1]
    exact e1.symm
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, ← Finset.mul_sum, sum_mod_shift p m _ hp hm]
  have h2 := Finset.sum_range_id_mul_two p
  rw [show 2 * (p * (a * m % k1) + k1 * ∑ h ∈ Finset.range p, h)
      = 2 * p * (a * m % k1) + k1 * ((∑ h ∈ Finset.range p, h) * 2) by ring, h2]

theorem split_add_wheel_holds : split_add_wheel := by
  intro W k q hq hsplit a
  change remSumN k (insert q W) a = 0
  rw [remSumN_insert k W q a hq, show remSumN k W (a * q) = 0 from hsplit (a * q),
    show remSumN k W a = 0 from hsplit a, sub_zero]

theorem split_fewer_parts_holds : split_fewer_parts := by
  intro W k h hk hdvd hsplit a
  obtain ⟨c, hc⟩ := hdvd
  change remSumN h W a = 0
  have hs := remSumN_scale c h a W
  rw [Nat.mul_comm c h, ← hc, show remSumN k W (c * a) = 0 from hsplit (c * a)] at hs
  have hc0 : (c : Int) ≠ 0 := by
    have : c ≠ 0 := by
      rintro rfl
      rw [Nat.mul_zero] at hc
      omega
    exact_mod_cast this
  exact (mul_eq_zero.mp hs.symm).resolve_left hc0

theorem split_remove_dividing_wheel_holds : split_remove_dividing_wheel := by
  intro W k p hW hp hpW hWne hk hpk hsplit a
  obtain ⟨k1, rfl⟩ := hpk
  have hk1 : 0 < k1 := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  -- with `p` dividing the parts, the even split for `W` and `p` says the sum
  -- for `p·k₁` parts is `p` times the sum for `k₁` parts
  have hH : ∀ b, remSumN (p * k1) W b = (p : Int) * remSumN k1 W b := by
    intro b
    have h : remSumN (p * k1) (insert p W) b = 0 := hsplit b
    rw [remSumN_insert _ _ _ _ hpW, Nat.mul_comm b p, remSumN_scale] at h
    linarith
  have hper : ∀ b i, remSumN k1 W (b + i * k1) = remSumN k1 W b := by
    intro b i
    rw [← remSumN_mod k1 (b + i * k1) W, Nat.add_mul_mod_self_right, remSumN_mod]
  have hsumA : ∑ i ∈ Finset.range p, remSumN (p * k1) W (a + i * k1)
      = (p : Int) * p * remSumN k1 W a := by
    have h : ∀ i ∈ Finset.range p, remSumN (p * k1) W (a + i * k1) = (p : Int) * remSumN k1 W a :=
      fun i _ => by rw [hH, hper]
    rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hS : ∀ S ∈ W.powerset,
      2 * ∑ i ∈ Finset.range p, (-1 : Int) ^ S.card *
          (((a + i * k1) * (W \ S).prod id % (p * k1) : Nat) : Int)
        = 2 * p * ((-1 : Int) ^ S.card * ((a * (W \ S).prod id % k1 : Nat) : Int))
          + (-1 : Int) ^ S.card * ((k1 * (p * (p - 1)) : Nat) : Int) := by
    intro S _
    have hcop : Nat.Coprime ((W \ S).prod id) p := by
      refine Nat.coprime_prod_left_iff.mpr (fun q hq => ?_)
      have hqW := (Finset.mem_sdiff.mp hq).1
      exact (Nat.coprime_primes (hW q hqW) hp).mpr (fun h => hpW (h ▸ hqW))
    have hC := sum_shift_mod_mul p k1 a ((W \ S).prod id) hp.pos hk1 hcop
    have hC' : (2 : Int) * ∑ i ∈ Finset.range p,
        (((a + i * k1) * (W \ S).prod id % (p * k1) : Nat) : Int)
          = 2 * p * ((a * (W \ S).prod id % k1 : Nat) : Int)
            + ((k1 * (p * (p - 1)) : Nat) : Int) := by
      exact_mod_cast hC
    rw [← Finset.mul_sum]
    linear_combination (-1 : Int) ^ S.card * hC'
  have hsumB : 2 * ∑ i ∈ Finset.range p, remSumN (p * k1) W (a + i * k1)
      = 2 * (p : Int) * remSumN k1 W a := by
    calc 2 * ∑ i ∈ Finset.range p, remSumN (p * k1) W (a + i * k1)
        = ∑ S ∈ W.powerset, 2 * ∑ i ∈ Finset.range p, (-1 : Int) ^ S.card *
            (((a + i * k1) * (W \ S).prod id % (p * k1) : Nat) : Int) := by
          unfold remSumN
          rw [Finset.sum_comm, Finset.mul_sum]
      _ = ∑ S ∈ W.powerset, (2 * p * ((-1 : Int) ^ S.card * ((a * (W \ S).prod id % k1 : Nat) : Int))
            + (-1 : Int) ^ S.card * ((k1 * (p * (p - 1)) : Nat) : Int)) :=
          Finset.sum_congr rfl hS
      _ = 2 * (p : Int) * remSumN k1 W a := by
          unfold remSumN
          rw [Finset.sum_add_distrib, ← Finset.sum_mul,
            Finset.sum_powerset_neg_one_pow_card_of_nonempty hWne, zero_mul, add_zero,
            Finset.mul_sum]
  have hG : remSumN k1 W a = 0 := by
    have e : (2 * (p : Int) * ((p : Int) - 1)) * remSumN k1 W a = 0 := by
      linear_combination (-2 : Int) * hsumA + hsumB
    have hp2 : (2 : Int) ≤ p := by exact_mod_cast hp.two_le
    have hpos : (0 : Int) < 2 * (p : Int) * ((p : Int) - 1) := by nlinarith
    exact (mul_eq_zero.mp e).resolve_left hpos.ne'
  change remSumN (p * k1) W a = 0
  rw [hH, hG, mul_zero]

theorem two_parts_exception_holds : two_parts_exception := by
  refine ⟨fun h => ?_, fun χ hodd => ?_⟩
  · have h1 : remSumN 2 (insert 2 ∅) 1 = 0 := h 1
    rw [remSumN_insert 2 ∅ 2 1 (Finset.notMem_empty 2)] at h1
    simp [remSumN] at h1
  · unfold DirichletCharacter.Odd at hodd
    have hm : (-1 : ZMod 2) = 1 := by decide
    rw [hm, MulChar.map_one] at hodd
    norm_num at hodd

/-! ## Germain's Theorem 1.1 -/

theorem split_iff_nondividing_wheels_holds : split_iff_nondividing_wheels := by
  intro W k hk hW hex
  obtain ⟨p0, hp0W, hp0k⟩ := hex
  have hW'ne : (W.filter (fun p => ¬ p ∣ k)).Nonempty :=
    ⟨p0, Finset.mem_filter.mpr ⟨hp0W, hp0k⟩⟩
  have hW'p : ∀ q ∈ W.filter (fun p => ¬ p ∣ k), q.Prime :=
    fun q hq => hW q (Finset.mem_filter.mp hq).1
  -- put back the dividing wheels `D` one at a time
  have key : ∀ D : Finset Nat, (∀ q ∈ D, q.Prime) → (∀ q ∈ D, q ∣ k) →
      Disjoint (W.filter (fun p => ¬ p ∣ k)) D →
      (remainders_cancel (W.filter (fun p => ¬ p ∣ k) ∪ D) k ↔
        remainders_cancel (W.filter (fun p => ¬ p ∣ k)) k) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro _ _ _
      rw [Finset.union_empty]
    | insert p D hpD ih =>
      intro hD hDk hdisj
      have hD' : ∀ q ∈ D, q.Prime := fun q hq => hD q (Finset.mem_insert_of_mem hq)
      have hDk' : ∀ q ∈ D, q ∣ k := fun q hq => hDk q (Finset.mem_insert_of_mem hq)
      have hdisj' := Finset.disjoint_of_subset_right (Finset.subset_insert p D) hdisj
      have hpU : p ∉ W.filter (fun p => ¬ p ∣ k) ∪ D := by
        rw [Finset.mem_union]
        rintro (h | h)
        · exact Finset.disjoint_left.mp hdisj h (Finset.mem_insert_self p D)
        · exact hpD h
      have hUp : ∀ q ∈ W.filter (fun p => ¬ p ∣ k) ∪ D, q.Prime := by
        intro q hq
        rcases Finset.mem_union.mp hq with h | h
        · exact hW'p q h
        · exact hD' q h
      rw [Finset.union_insert, ← ih hD' hDk' hdisj']
      constructor
      · intro h
        exact split_remove_dividing_wheel_holds _ k p hUp (hD p (Finset.mem_insert_self p D)) hpU
          (hW'ne.mono Finset.subset_union_left) hk (hDk p (Finset.mem_insert_self p D)) h
      · intro h
        exact split_add_wheel_holds _ k p hpU h
  have hU : W.filter (fun p => ¬ p ∣ k) ∪ W.filter (fun p => p ∣ k) = W := by
    rw [Finset.union_comm]
    exact Finset.filter_union_filter_not_eq _ W
  have h := key (W.filter (fun p => p ∣ k))
    (fun q hq => hW q (Finset.mem_filter.mp hq).1) (fun q hq => (Finset.mem_filter.mp hq).2)
    (Finset.disjoint_filter_filter_not W W (fun p => p ∣ k)).symm
  rw [hU] at h
  exact h

theorem germain_theorem_step
    (h_saw : RNS.Sawtooth.even_split_iff_remainders_cancel)
    (h_hz : RNS.HurwitzZetaZero.hurwitz_zeta_at_zero) :
    germain_theorem := by
  intro k _ W hW hex
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hW'ne : (W.filter (fun p => ¬ p ∣ k)).Nonempty := by
    obtain ⟨p0, hp0W, hp0k⟩ := hex
    exact ⟨p0, Finset.mem_filter.mpr ⟨hp0W, hp0k⟩⟩
  have hW'p : ∀ q ∈ W.filter (fun p => ¬ p ∣ k), q.Prime :=
    fun q hq => hW q (Finset.mem_filter.mp hq).1
  have hW'k : ∀ q ∈ W.filter (fun p => ¬ p ∣ k), ¬ q ∣ k :=
    fun q hq => (Finset.mem_filter.mp hq).2
  -- survivors to remainders (`Sawtooth`), drop the dividing wheels, then Corollary 3.2
  have e1 : (∀ a : Nat, k * (survivors_upto W (a * W.prod id / k)).card
      = a * (survivors_upto W (W.prod id)).card) ↔ remainders_cancel W k :=
    forall_congr' (fun a => h_saw W k a hW)
  refine e1.trans ((split_iff_nondividing_wheels_holds W k hk hW hex).trans
    ((all_residues_split_iff_wheels_step h_hz k _ hW'ne hW'p hW'k).trans ?_))
  -- a character is 0, never 1, at a wheel dividing `k`
  refine forall_congr' (fun χ => imp_congr_right (fun _ => ?_))
  constructor
  · rintro ⟨p, hp, h1⟩
    exact ⟨p, (Finset.mem_filter.mp hp).1, h1⟩
  · rintro ⟨p, hp, h1⟩
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, fun hpk => ?_⟩, h1⟩
    have hnu : ¬ IsUnit (p : ZMod k) := by
      rw [ZMod.isUnit_iff_coprime]
      exact fun h => (Nat.Prime.coprime_iff_not_dvd (hW p hp)).mp h hpk
    rw [MulChar.map_nonunit _ hnu] at h1
    exact zero_ne_one h1

end RNS.GermainCriterion

#print axioms RNS.GermainCriterion.two_wheel_split_of_remainders_step
#print axioms RNS.GermainCriterion.odd_primitive_LFunction_zero_ne_zero_holds
#print axioms RNS.GermainCriterion.odd_primitive_weighted_sum_ne_zero_step
#print axioms RNS.GermainCriterion.character_transform_holds
#print axioms RNS.GermainCriterion.weighted_sum_eq_LFunction_zero_step
#print axioms RNS.GermainCriterion.odd_weighted_sum_ne_zero_iff_step
#print axioms RNS.GermainCriterion.coprime_split_iff_characters_step
#print axioms RNS.GermainCriterion.all_residues_split_iff_wheels_step
#print axioms RNS.GermainCriterion.split_add_wheel_holds
#print axioms RNS.GermainCriterion.split_fewer_parts_holds
#print axioms RNS.GermainCriterion.split_remove_dividing_wheel_holds
#print axioms RNS.GermainCriterion.two_parts_exception_holds
#print axioms RNS.GermainCriterion.split_iff_nondividing_wheels_holds
#print axioms RNS.GermainCriterion.germain_theorem_step
