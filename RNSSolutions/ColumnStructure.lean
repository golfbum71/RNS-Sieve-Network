/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Algebra.Field.ZMod        -- remainders modulo a prime form a field
import Mathlib.Data.Nat.Factors          -- `Nat.primeFactorsList`
import Mathlib.Tactic.Push               -- `push Not`
import RNSNetwork.Nodes.Wheel6.Conclusions
import RNSNetwork.Nodes.ColumnStructure.Conclusions

/-!
# Proofs for ColumnStructure

Imports claims only. The two prime-factor conclusions are proved as steps from
`Wheel6.prime_gt_three_is_candidate`, taken as the hypothesis `h_w6`.

Tactic proofs are copied from `rns_sieve_6.lean` (Part C and the column
lemmas), with each call to `prime_gt_three_is_candidate` replaced by `h_w6`.
-/

namespace RNS.ColumnStructure

theorem columns_multiply_holds : columns_multiply := by
  unfold columns_multiply
  intro a b
  refine ⟨⟨6 * a * b + 5 * a + 5 * b + 4, ?_⟩, ⟨6 * a * b + a + 5 * b, ?_⟩,
    ⟨6 * b * a + b + 5 * a, ?_⟩, ⟨6 * a * b + a + b, ?_⟩⟩ <;>
  (simp only [col_minus, col_plus]; ring)

theorem col_minus_periodicity_holds : col_minus_periodicity := by
  unfold col_minus_periodicity
  intro p hp _hp2 _hp3
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  have h6ne : (6 : ZMod p) ≠ 0 := by
    intro h6
    have hdvd : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp (by exact_mod_cast h6)
    have h23 : p ∣ 2 * 3 := by norm_num; exact hdvd
    rcases hp.dvd_mul.mp h23 with h | h
    · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
      have hge : 2 ≤ p := hp.two_le
      omega
    · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) h
      have hge : 2 ≤ p := hp.two_le
      omega
  set x : ZMod p := -5 * (6 : ZMod p)⁻¹ with hxdef
  have h6inv : (6 : ZMod p) * (6 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h6ne
  have hchar : ∀ n : Nat, (6 * (n : ZMod p) + 5 = 0) ↔ (n : ZMod p) = x := by
    intro n
    rw [hxdef]
    constructor
    · intro h
      apply mul_left_cancel₀ h6ne
      rw [mul_left_comm, h6inv, mul_one]
      exact add_eq_zero_iff_eq_neg.mp h
    · intro h
      rw [h, mul_left_comm, h6inv, mul_one]
      exact add_eq_zero_iff_eq_neg.mpr rfl
  refine ⟨x.val, ZMod.val_lt x, ?_⟩
  intro n
  have hcol : (col_minus n : ZMod p) = 6 * (n : ZMod p) + 5 := by
    unfold col_minus; push_cast; ring
  rw [← ZMod.natCast_eq_zero_iff (col_minus n) p, hcol, hchar n]
  constructor
  · intro h
    have heq : ((n % p : ℕ) : ZMod p) = x := by
      rw [ZMod.natCast_mod n p]; exact h
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast] at hval
    rwa [Nat.mod_eq_of_lt (Nat.mod_lt n hp.pos)] at hval
  · intro h
    have heq : ((n % p : ℕ) : ZMod p) = x := by
      rw [h]; exact ZMod.natCast_rightInverse x
    rw [ZMod.natCast_mod n p] at heq
    exact heq

private theorem list_prod_mod_six_of_all_one_mod_six :
    ∀ l : List Nat, (∀ p ∈ l, p % 6 = 1) → l.prod % 6 = 1 := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      have ha : a % 6 = 1 := h a (List.mem_cons.mpr (Or.inl rfl))
      have ht : ∀ p ∈ t, p % 6 = 1 := fun p hp => h p (List.mem_cons.mpr (Or.inr hp))
      rw [List.prod_cons, Nat.mul_mod, ha, ih ht]

private theorem minus_factor_aux (h_w6 : RNS.Wheel6.prime_gt_three_is_candidate)
    (n : Nat) : ∃ p, p.Prime ∧ p ∣ col_minus n ∧ p % 6 = 5 := by
  by_contra hcon
  push Not at hcon
  have hx_mod : col_minus n % 6 = 5 := by unfold col_minus; omega
  have hall1 : ∀ p ∈ (col_minus n).primeFactorsList, p % 6 = 1 := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hpdvd : p ∣ col_minus n := Nat.dvd_of_mem_primeFactorsList hp
    have hne5 : p % 6 ≠ 5 := hcon p hprime hpdvd
    have hne2 : p ≠ 2 := by
      intro h
      rw [h] at hpdvd
      unfold col_minus at hpdvd
      omega
    have hne3 : p ≠ 3 := by
      intro h
      rw [h] at hpdvd
      unfold col_minus at hpdvd
      omega
    have hgt3 : 3 < p := by
      have h2 := hprime.two_le
      omega
    have hcand := h_w6 p hprime hgt3
    unfold is_candidate at hcand
    simp only [Bool.or_eq_true, beq_iff_eq] at hcand
    omega
  have hprodmod : (col_minus n).primeFactorsList.prod % 6 = 1 :=
    list_prod_mod_six_of_all_one_mod_six _ hall1
  have hne0 : col_minus n ≠ 0 := by unfold col_minus; omega
  rw [Nat.prod_primeFactorsList hne0] at hprodmod
  omega

/-- **Step:** `Wheel6` implies every 6n-1 number has a 6n-1 prime factor. -/
theorem col_minus_has_minus_prime_factor_step
    (h_w6 : RNS.Wheel6.prime_gt_three_is_candidate) : col_minus_has_minus_prime_factor := by
  unfold col_minus_has_minus_prime_factor
  exact minus_factor_aux h_w6

/-- **Step:** `Wheel6` implies a composite 6n-1 number has a smaller 6n-1
prime factor. -/
theorem col_minus_composite_has_proper_minus_factor_step
    (h_w6 : RNS.Wheel6.prime_gt_three_is_candidate) :
    col_minus_composite_has_proper_minus_factor := by
  unfold col_minus_composite_has_proper_minus_factor
  intro n hcomp
  obtain ⟨p, hp, hpdvd, hp5⟩ := minus_factor_aux h_w6 n
  refine ⟨p, hp, hpdvd, hp5, ?_⟩
  have hle : p ≤ col_minus n := Nat.le_of_dvd (by unfold col_minus; omega) hpdvd
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso; exact hcomp (h ▸ hp)

end RNS.ColumnStructure

#print axioms RNS.ColumnStructure.columns_multiply_holds
#print axioms RNS.ColumnStructure.col_minus_periodicity_holds
#print axioms RNS.ColumnStructure.col_minus_has_minus_prime_factor_step
#print axioms RNS.ColumnStructure.col_minus_composite_has_proper_minus_factor_step
