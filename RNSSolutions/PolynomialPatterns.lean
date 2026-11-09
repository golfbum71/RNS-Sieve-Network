/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PolynomialPatterns.Conclusions
import Mathlib

/-!
# Proofs for PolynomialPatterns

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. The finite check: carry a polynomial to the remainders on division by
the wheel. Because no prime divides all its coefficients, it does not become
zero there, so it has at most its degree in roots; a blocked position is a
root of one of the polynomials, and different positions below the wheel give
different remainders. So a wheel larger than the total degree has a free
position.

The square plus one: degree 2, so only the wheel 2 needs checking, where only
the position 1 is blocked (1 squared plus 1 is even, 0 squared plus 1 is not).

Landau: half a positive constant times `x` over its logarithm grows without
limit, a count asymptotic to it does too, but finitely many such primes would
cap the count.
-/

namespace RNS.PolynomialPatterns

open Polynomial Filter Topology Asymptotics

open Classical in
/-- One polynomial blocks at most its degree in positions on a prime wheel. -/
private theorem blocked_one_le (f : ℤ[X]) (p : ℕ) (hp : p.Prime) (hf : coeffs_coprime f) :
    ((Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ))).card ≤ f.natDegree := by
  haveI := Fact.mk hp
  have hg : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := hf p hp
    apply hi
    have h1 : (f.map (Int.castRingHom (ZMod p))).coeff i = 0 := by rw [h0, coeff_zero]
    rw [coeff_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    exact h1
  calc ((Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ))).card
      ≤ (f.map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
        apply Finset.card_le_card_of_injOn (fun r : ℕ => (r : ZMod p))
        · intro r hr
          rw [Finset.mem_coe, Finset.mem_filter] at hr
          show (r : ZMod p) ∈ ((f.map (Int.castRingHom (ZMod p))).roots.toFinset : Set (ZMod p))
          rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hg, IsRoot.def,
            eval_natCast_map, eq_intCast]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hr.2
        · intro a ha b hb hab
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
          have h := congrArg ZMod.val hab
          simp only [ZMod.val_natCast] at h
          rwa [Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h
    _ ≤ Multiset.card (f.map (Int.castRingHom (ZMod p))).roots := Multiset.toFinset_card_le _
    _ ≤ (f.map (Int.castRingHom (ZMod p))).natDegree := card_roots' _
    _ ≤ f.natDegree := natDegree_map_le

open Classical in
theorem poly_admissible_iff_holds : poly_admissible_iff := by
  intro F hF
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp
    by_cases hle : p ≤ ∑ f ∈ F, f.natDegree
    · exact h p hp hle
    · calc (poly_blocked F p).card
          ≤ (F.biUnion (fun f => (Finset.range p).filter
              (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ)))).card := by
            apply Finset.card_le_card
            intro r hr
            unfold poly_blocked at hr
            rw [Finset.mem_filter] at hr
            obtain ⟨hr1, f, hfF, hdvd⟩ := hr
            exact Finset.mem_biUnion.mpr ⟨f, hfF, Finset.mem_filter.mpr ⟨hr1, hdvd⟩⟩
        _ ≤ ∑ f ∈ F, ((Finset.range p).filter (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ f ∈ F, f.natDegree :=
            Finset.sum_le_sum (fun f hf => blocked_one_le f p hp (hF f hf))
        _ < p := by omega

theorem sq_add_one_admissible_holds : sq_add_one_admissible := by
  have hcop : ∀ f ∈ ({X ^ 2 + 1} : Finset ℤ[X]), coeffs_coprime f := by
    intro f hf
    rw [Finset.mem_singleton] at hf
    subst hf
    intro p hp
    refine ⟨0, ?_⟩
    have h0 : (X ^ 2 + 1 : ℤ[X]).coeff 0 = 1 := by simp
    rw [h0]
    intro hd
    have hd' : (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by simpa using hd
    have h1 : p = 1 := Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd')
    exact hp.one_lt.ne' h1
  unfold sq_add_one_admissible
  rw [poly_admissible_iff_holds _ hcop]
  intro p hp hle
  have hdeg : ∑ f ∈ ({X ^ 2 + 1} : Finset ℤ[X]), f.natDegree = 2 := by
    rw [Finset.sum_singleton, ← C_1, natDegree_X_pow_add_C]
  rw [hdeg] at hle
  interval_cases p
  · exact absurd hp Nat.not_prime_zero
  · exact absurd hp Nat.not_prime_one
  · have hsub : poly_blocked {X ^ 2 + 1} 2 ⊆ {1} := by
      intro r hr
      unfold poly_blocked at hr
      rw [Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨hr2, f, hf, hd⟩ := hr
      rw [Finset.mem_singleton] at hf
      subst hf
      rw [Finset.mem_singleton]
      interval_cases r
      · norm_num at hd
      · rfl
    calc (poly_blocked {X ^ 2 + 1} 2).card ≤ ({1} : Finset ℕ).card := Finset.card_le_card hsub
      _ < 2 := by decide

private theorem tendsto_natCast_div_log_atTop :
    Tendsto (fun N : ℕ => (N : ℝ) / Real.log N) atTop atTop := by
  have hreal : Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
    have hz : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa using h
    have hpos : ∀ᶠ x : ℝ in atTop, Real.log x / x ∈ Set.Ioi (0 : ℝ) := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hlog : 0 < Real.log x := Real.log_pos hx
      have hxpos : 0 < x := lt_trans one_pos hx
      exact Set.mem_Ioi.mpr (by positivity)
    have hnW : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hz, hpos⟩
    have hinv := tendsto_inv_nhdsGT_zero.comp hnW
    have heq : ((fun y : ℝ => y⁻¹) ∘ fun x : ℝ => Real.log x / x) = fun x : ℝ => x / Real.log x := by
      funext x
      rw [Function.comp_apply, inv_div]
    rwa [heq] at hinv
  exact hreal.comp tendsto_natCast_atTop_atTop

theorem landau_of_bateman_horn_holds : landau_of_bateman_horn := by
  rintro ⟨C, hC, hlim⟩ hBH
  have hequiv := hBH C hlim
  have hmain : Tendsto (fun x : ℕ => C / 2 * (x : ℝ) / Real.log x) atTop atTop := by
    have h := tendsto_natCast_div_log_atTop.const_mul_atTop (show (0 : ℝ) < C / 2 by positivity)
    simpa only [mul_div_assoc] using h
  have hcount : Tendsto (fun x : ℕ => (sq_add_one_count x : ℝ)) atTop atTop :=
    hequiv.symm.tendsto_atTop hmain
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    (tendsto_atTop.mp hcount ((hfin.toFinset.card : ℝ) + 1))
  have h1 := hB B le_rfl
  have hbound : sq_add_one_count B ≤ hfin.toFinset.card := by
    unfold sq_add_one_count
    apply Finset.card_le_card
    intro n hn
    rw [Finset.mem_filter] at hn
    exact hfin.mem_toFinset.mpr hn.2
  have h2 : (sq_add_one_count B : ℝ) ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast hbound
  linarith

#print axioms RNS.PolynomialPatterns.poly_admissible_iff_holds
#print axioms RNS.PolynomialPatterns.sq_add_one_admissible_holds
#print axioms RNS.PolynomialPatterns.landau_of_bateman_horn_holds

end RNS.PolynomialPatterns
