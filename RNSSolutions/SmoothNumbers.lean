/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SmoothNumbers.Conclusions
import Mathlib

/-!
# Proofs for SmoothNumbers

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. Rankin: each counted number is at most `x`, so `x / n` to the power `α`
is at least one; sum these. The sum of `n` to the minus `α` over the smooth
numbers is at most the product over the wheels of the geometric series: add
the wheels one at a time, and split each smooth number into the power of the
new wheel it contains and the rest (unique by factorization), whose prime
factors are the old wheels.

Lower bound: a set of distinct wheels has a product whose prime factors are
exactly that set (Mathlib's `Nat.primeFactors_prod`), so different sets give
different products, each at most `y` to the size of the set.

Recurrence: split by whether the new wheel divides the number, as in
Legendre's recurrence.
-/

namespace RNS.SmoothNumbers

private theorem mem_smooth {W : Finset Nat} {x n : Nat} :
    n ∈ smooth_upto W x ↔ (1 ≤ n ∧ n ≤ x) ∧ n.primeFactors ⊆ W := by
  simp only [smooth_upto, Finset.mem_filter, Finset.mem_Icc]

/-! ## The recurrence -/

theorem smooth_buchstab_holds : smooth_buchstab := by
  intro W p x hp hpW
  have hp0 : 0 < p := hp.pos
  have hsplit : ((smooth_upto (insert p W) x).filter (fun n => p ∣ n)).card +
      ((smooth_upto (insert p W) x).filter (fun n => ¬ p ∣ n)).card =
        (smooth_upto (insert p W) x).card :=
    Finset.card_filter_add_card_filter_not _
  have h1 : (smooth_upto (insert p W) x).filter (fun n => ¬ p ∣ n) = smooth_upto W x := by
    ext n
    simp only [Finset.mem_filter, mem_smooth]
    constructor
    · rintro ⟨⟨hn, hsub⟩, hpn⟩
      refine ⟨hn, fun r hr => ?_⟩
      rcases Finset.mem_insert.mp (hsub hr) with h | h
      · rw [h] at hr
        exact absurd (Nat.dvd_of_mem_primeFactors hr) hpn
      · exact h
    · rintro ⟨hn, hsub⟩
      refine ⟨⟨hn, hsub.trans (Finset.subset_insert p W)⟩, fun hpn => hpW (hsub ?_)⟩
      have hn1 := hn.1
      exact Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
  have h2 : ((smooth_upto (insert p W) x).filter (fun n => p ∣ n)).card =
      (smooth_upto (insert p W) (x / p)).card := by
    apply Finset.card_nbij' (fun n => n / p) (fun m => p * m)
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, mem_smooth] at hn ⊢
      obtain ⟨⟨⟨hn1, hnx⟩, hsub⟩, hpn⟩ := hn
      obtain ⟨m, rfl⟩ := hpn
      rw [Nat.mul_div_cancel_left m hp0]
      have hm0 : m ≠ 0 := by rintro rfl; simp at hn1
      refine ⟨⟨by omega, (Nat.le_div_iff_mul_le hp0).mpr (by rw [mul_comm]; exact hnx)⟩, ?_⟩
      rw [Nat.primeFactors_mul hp.ne_zero hm0] at hsub
      exact fun r hr => hsub (Finset.mem_union_right _ hr)
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter, mem_smooth] at hm ⊢
      obtain ⟨⟨hm1, hmx⟩, hsub⟩ := hm
      have hm0 : m ≠ 0 := by omega
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right p m⟩
      · have := Nat.mul_pos hp0 hm1
        omega
      · have := (Nat.le_div_iff_mul_le hp0).mp hmx
        rw [mul_comm]; exact this
      · intro r hr
        rw [Nat.primeFactors_mul hp.ne_zero hm0, hp.primeFactors] at hr
        rcases Finset.mem_union.mp hr with h | h
        · rw [Finset.mem_singleton.mp h]; exact Finset.mem_insert_self p W
        · exact hsub h
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter] at hn
      show p * (n / p) = n
      exact Nat.mul_div_cancel' hn.2
    · intro m _
      show p * m / p = m
      exact Nat.mul_div_cancel_left m hp0
  rw [← h1, ← h2]
  omega

/-! ## The lower bound -/

theorem smooth_count_lower_holds : smooth_count_lower := by
  intro W y u x hW hWy hy hyx
  have hmap : ((W.powerset.filter (fun D => D.card ≤ u) : Finset (Finset Nat)) : Set (Finset Nat)).MapsTo
      (fun D => D.card) (Finset.range (u + 1) : Set Nat) := by
    intro D hD
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_filter.mp (Finset.mem_coe.mp hD)).2))
  have hcount : (W.powerset.filter (fun D => D.card ≤ u)).card =
      ∑ j ∈ Finset.range (u + 1), W.card.choose j := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hfib : (W.powerset.filter (fun D => D.card ≤ u)).filter (fun D => D.card = j) =
        W.powersetCard j := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, by omega⟩, h3⟩
    rw [hfib, Finset.card_powersetCard]
  rw [← hcount]
  apply Finset.card_le_card_of_injOn (fun D => ∏ p ∈ D, p)
  · intro D hD
    have hD' := Finset.mem_filter.mp (Finset.mem_coe.mp hD)
    have hDW : D ⊆ W := Finset.mem_powerset.mp hD'.1
    have hDp : ∀ p ∈ D, p.Prime := fun p hp => hW p (hDW hp)
    show (∏ p ∈ D, p) ∈ smooth_upto W x
    rw [mem_smooth]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr fun p hp => (hDp p hp).ne_zero)
    · calc ∏ p ∈ D, p ≤ y ^ D.card :=
            Finset.prod_le_pow_card D (fun p => p) y (fun p hp => hWy p (hDW hp))
        _ ≤ y ^ u := Nat.pow_le_pow_right hy hD'.2
        _ ≤ x := hyx
    · rw [Nat.primeFactors_prod hDp]
      exact hDW
  · intro D hD E hE hDE
    have hD' := Finset.mem_filter.mp (Finset.mem_coe.mp hD)
    have hE' := Finset.mem_filter.mp (Finset.mem_coe.mp hE)
    have hDp : ∀ p ∈ D, p.Prime := fun p hp => hW p (Finset.mem_powerset.mp hD'.1 hp)
    have hEp : ∀ p ∈ E, p.Prime := fun p hp => hW p (Finset.mem_powerset.mp hE'.1 hp)
    have hDE' : ∏ p ∈ D, p = ∏ p ∈ E, p := hDE
    have h := congrArg Nat.primeFactors hDE'
    rwa [Nat.primeFactors_prod hDp, Nat.primeFactors_prod hEp] at h

/-! ## Rankin's bound -/

/-- Split a number into the exponent of `p` in it and the part prime to `p`. -/
private def splitP (p n : Nat) : Nat × Nat := (n.factorization p, n / p ^ n.factorization p)

private theorem one_le_term {x n : Nat} {α : ℝ} (hα : 0 < α) (hn : 1 ≤ n) (hnx : n ≤ x) :
    (1 : ℝ) ≤ (x : ℝ) ^ α * (n : ℝ) ^ (-α) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ^ α ≤ (x : ℝ) ^ α :=
    Real.rpow_le_rpow hn0.le (by exact_mod_cast hnx) hα.le
  have hpos : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hn0 α
  rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, one_le_div hpos]
  exact hle

private theorem sum_le_prod (W : Finset Nat) (x : Nat) (α : ℝ) (hW : ∀ p ∈ W, p.Prime)
    (hα : 0 < α) :
    ∑ n ∈ smooth_upto W x, (n : ℝ) ^ (-α) ≤ ∏ p ∈ W, (1 - (p : ℝ) ^ (-α))⁻¹ := by
  induction W using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    calc ∑ n ∈ smooth_upto ∅ x, (n : ℝ) ^ (-α)
        ≤ ∑ n ∈ ({1} : Finset Nat), (n : ℝ) ^ (-α) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            rw [mem_smooth] at hn
            obtain ⟨⟨hn1, _⟩, hsub⟩ := hn
            rw [Finset.subset_empty, Nat.primeFactors_eq_empty] at hsub
            rw [Finset.mem_singleton]
            omega
          · intro i _ _
            exact Real.rpow_nonneg (Nat.cast_nonneg i) _
      _ = 1 := by simp
  | insert p W hpW ih =>
    have hp : p.Prime := hW p (Finset.mem_insert_self p W)
    have hW' : ∀ q ∈ W, q.Prime := fun q hq => hW q (Finset.mem_insert_of_mem hq)
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hr0 : 0 ≤ (p : ℝ) ^ (-α) := Real.rpow_nonneg (by positivity) _
    have hr1 : (p : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hmaps : ∀ n ∈ smooth_upto (insert p W) x,
        splitP p n ∈ Finset.range (x + 1) ×ˢ smooth_upto W x := by
      intro n hn
      rw [mem_smooth] at hn
      obtain ⟨⟨hn1, hnx⟩, hsub⟩ := hn
      have hn0 : n ≠ 0 := by omega
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · show n.factorization p ∈ Finset.range (x + 1)
        rw [Finset.mem_range]
        have h1 : n.factorization p < p ^ n.factorization p := Nat.lt_pow_self hp.one_lt
        have h2 : p ^ n.factorization p ≤ n := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)
        omega
      · show n / p ^ n.factorization p ∈ smooth_upto W x
        rw [mem_smooth]
        have hpos := Nat.ordCompl_pos p hn0
        refine ⟨⟨hpos, le_trans (Nat.div_le_self _ _) hnx⟩, ?_⟩
        intro r hr
        have hr' := Nat.mem_primeFactors.mp hr
        have hrn : r ∣ n := dvd_trans hr'.2.1 (Nat.ordCompl_dvd n p)
        rcases Finset.mem_insert.mp (hsub (Nat.mem_primeFactors.mpr ⟨hr'.1, hrn, hn0⟩)) with h | h
        · exact absurd hr'.2.1 (by rw [h]; exact Nat.not_dvd_ordCompl hp hn0)
        · exact h
    have hinj : Set.InjOn (splitP p) (smooth_upto (insert p W) x : Set Nat) := by
      intro a _ b _ hab
      have h1 : a.factorization p = b.factorization p := congrArg Prod.fst hab
      have h2 : a / p ^ a.factorization p = b / p ^ b.factorization p := congrArg Prod.snd hab
      calc a = p ^ a.factorization p * (a / p ^ a.factorization p) :=
            (Nat.ordProj_mul_ordCompl_eq_self a p).symm
        _ = p ^ b.factorization p * (b / p ^ b.factorization p) := by rw [h2, h1]
        _ = b := Nat.ordProj_mul_ordCompl_eq_self b p
    have hval : ∀ n ∈ smooth_upto (insert p W) x,
        (n : ℝ) ^ (-α) = ((p : ℝ) ^ (-α)) ^ (splitP p n).1 * (((splitP p n).2 : Nat) : ℝ) ^ (-α) := by
      intro n _
      show (n : ℝ) ^ (-α) = ((p : ℝ) ^ (-α)) ^ n.factorization p *
        (((n / p ^ n.factorization p : Nat)) : ℝ) ^ (-α)
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
      rw [Nat.cast_mul,
        Real.mul_rpow (show (0 : ℝ) ≤ ((p ^ n.factorization p : Nat) : ℝ) by positivity)
          (show (0 : ℝ) ≤ ((n / p ^ n.factorization p : Nat) : ℝ) by positivity),
        Nat.cast_pow, ← Real.rpow_pow_comm (show (0 : ℝ) ≤ (p : ℝ) by positivity)]
    calc ∑ n ∈ smooth_upto (insert p W) x, (n : ℝ) ^ (-α)
        = ∑ t ∈ (smooth_upto (insert p W) x).image (splitP p),
            ((p : ℝ) ^ (-α)) ^ t.1 * ((t.2 : Nat) : ℝ) ^ (-α) := by
          rw [Finset.sum_image hinj]
          exact Finset.sum_congr rfl hval
      _ ≤ ∑ t ∈ Finset.range (x + 1) ×ˢ smooth_upto W x,
            ((p : ℝ) ^ (-α)) ^ t.1 * ((t.2 : Nat) : ℝ) ^ (-α) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro t ht
            obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
            exact hmaps n hn
          · intro t _ _
            exact mul_nonneg (pow_nonneg hr0 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = (∑ v ∈ Finset.range (x + 1), ((p : ℝ) ^ (-α)) ^ v) *
            ∑ m ∈ smooth_upto W x, (m : ℝ) ^ (-α) := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ (1 - (p : ℝ) ^ (-α))⁻¹ * ∏ q ∈ W, (1 - (q : ℝ) ^ (-α))⁻¹ := by
          refine mul_le_mul ?_ (ih hW') (Finset.sum_nonneg fun m _ =>
            Real.rpow_nonneg (Nat.cast_nonneg m) _) (inv_nonneg.mpr (by linarith))
          have hg : ∑ i ∈ Finset.Ico 0 (x + 1), ((p : ℝ) ^ (-α)) ^ i ≤
              ((p : ℝ) ^ (-α)) ^ 0 / (1 - (p : ℝ) ^ (-α)) := geom_sum_Ico_le_of_lt_one hr0 hr1
          rw [pow_zero, ← Finset.range_eq_Ico, one_div] at hg
          exact hg
      _ = ∏ q ∈ insert p W, (1 - (q : ℝ) ^ (-α))⁻¹ := (Finset.prod_insert hpW).symm

theorem rankin_upper_holds : rankin_upper := by
  intro W x α hW hα
  have hxα : 0 ≤ (x : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg x) α
  calc ((smooth_upto W x).card : ℝ) = ∑ n ∈ smooth_upto W x, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ smooth_upto W x, (x : ℝ) ^ α * (n : ℝ) ^ (-α) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [mem_smooth] at hn
        exact one_le_term hα hn.1.1 hn.1.2
    _ = (x : ℝ) ^ α * ∑ n ∈ smooth_upto W x, (n : ℝ) ^ (-α) := by rw [Finset.mul_sum]
    _ ≤ (x : ℝ) ^ α * ∏ p ∈ W, (1 - (p : ℝ) ^ (-α))⁻¹ :=
        mul_le_mul_of_nonneg_left (sum_le_prod W x α hW hα) hxα

#print axioms RNS.SmoothNumbers.rankin_upper_holds
#print axioms RNS.SmoothNumbers.smooth_count_lower_holds
#print axioms RNS.SmoothNumbers.smooth_buchstab_holds

end RNS.SmoothNumbers
