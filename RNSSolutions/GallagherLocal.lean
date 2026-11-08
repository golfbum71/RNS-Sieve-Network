/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.GallagherLocal.Conclusions
import Mathlib

/-!
# Proofs for GallagherLocal

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. The wheel size minus the occupied positions is the number of positions
the pattern avoids. Summing over the `k`-sets of offsets below `h` and
swapping the sums, each position `c` is avoided by the `k`-sets of the
offsets below `h` outside the class of `c`; there are `m` such offsets, with
`m / h` tending to one minus one over the wheel (each class holds `h / p`
offsets, up to one). The ratio of `m` choose `k` to `h` choose `k` is the
product of `(m − i) / (h − i)` over `i < k`, which tends to (one minus one
over the wheel) to the `k`. Summing over the `p` positions and dividing by
`p` times that power gives 1.
-/

namespace RNS.GallagherLocal

open Filter Topology

/-- A pattern occupies at most `p` positions on the wheel of size `p`. -/
private theorem w_le (T : Finset Nat) {p : Nat} (hp : 0 < p) : w T p ≤ p := by
  unfold w
  calc (T.image (fun t => t % p)).card ≤ (Finset.range p).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (Nat.mod_lt t hp)
    _ = p := Finset.card_range p

/-- The positions a pattern avoids number the wheel size minus the occupied ones. -/
private theorem avoid_count (T : Finset Nat) {p : Nat} (hp : 0 < p) :
    p - w T p = ((Finset.range p).filter (fun c => ∀ t ∈ T, t % p ≠ c)).card := by
  have hsub : T.image (fun t => t % p) ⊆ Finset.range p := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Nat.mod_lt t hp)
  have heq : (Finset.range p).filter (fun c => ∀ t ∈ T, t % p ≠ c) =
      Finset.range p \ T.image (fun t => t % p) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_image, not_exists, not_and, ne_eq]
  rw [heq, Finset.card_sdiff_of_subset hsub, Finset.card_range]
  rfl

/-- The `k`-sets avoiding the class of `c` are the `k`-sets of the offsets
outside that class. -/
private theorem avoid_sets (h k p c : Nat) :
    ((Finset.range h).powersetCard k).filter (fun T => ∀ t ∈ T, t % p ≠ c) =
      ((Finset.range h).filter (fun t => t % p ≠ c)).powersetCard k := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hav⟩
    exact ⟨fun t ht => Finset.mem_filter.mpr ⟨hsub ht, hav t ht⟩, hcard⟩
  · rintro ⟨hsub, hcard⟩
    exact ⟨⟨fun t ht => (Finset.mem_filter.mp (hsub ht)).1, hcard⟩,
      fun t ht => (Finset.mem_filter.mp (hsub ht)).2⟩

/-- Swapping the sums. -/
private theorem sum_avoid (h k p : Nat) (hp : 0 < p) :
    ∑ T ∈ (Finset.range h).powersetCard k, (p - w T p) =
      ∑ c ∈ Finset.range p, ((Finset.range h).filter (fun t => t % p ≠ c)).card.choose k := by
  calc ∑ T ∈ (Finset.range h).powersetCard k, (p - w T p)
      = ∑ T ∈ (Finset.range h).powersetCard k, ∑ c ∈ Finset.range p,
          (if ∀ t ∈ T, t % p ≠ c then 1 else 0) := by
        refine Finset.sum_congr rfl (fun T _ => ?_)
        rw [avoid_count T hp, Finset.card_filter]
    _ = ∑ c ∈ Finset.range p, ∑ T ∈ (Finset.range h).powersetCard k,
          (if ∀ t ∈ T, t % p ≠ c then 1 else 0) := Finset.sum_comm
    _ = ∑ c ∈ Finset.range p, ((Finset.range h).filter (fun t => t % p ≠ c)).card.choose k := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [← Finset.card_filter, avoid_sets, Finset.card_powersetCard]

/-- The descending factorial as a real product. -/
private theorem desc_prod (n k : Nat) :
    ((n.descFactorial k : Nat) : ℝ) = ∏ i ∈ Finset.range k, ((n : ℝ) - i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.cast_mul, Finset.prod_range_succ, ← ih]
    by_cases hk : k ≤ n
    · rw [Nat.cast_sub hk]
      ring
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp

private theorem choose_eq (n k : Nat) :
    ((n.choose k : Nat) : ℝ) = (∏ i ∈ Finset.range k, ((n : ℝ) - i)) / (k.factorial : ℝ) := by
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hR : ((n.descFactorial k : Nat) : ℝ) = (k.factorial : ℝ) * (n.choose k : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n k
  rw [← desc_prod, eq_div_iff hf.ne']
  linarith

/-- If `m h / h` tends to `L`, then `m h` choose `k` over `h` choose `k` tends
to `L ^ k`. -/
private theorem choose_ratio (k : Nat) (m : Nat → Nat) (L : ℝ)
    (hm : Tendsto (fun h : Nat => (m h : ℝ) / h) atTop (𝓝 L)) :
    Tendsto (fun h : Nat => ((m h).choose k : ℝ) / (h.choose k : ℝ)) atTop (𝓝 (L ^ k)) := by
  have hfac : ∀ i ∈ Finset.range k, Tendsto (fun h : Nat => ((m h : ℝ) - i) / ((h : ℝ) - i))
      atTop (𝓝 L) := by
    intro i _
    have h1 : Tendsto (fun h : Nat => ((m h : ℝ) / h - (i : ℝ) / h) / (1 - (i : ℝ) / h))
        atTop (𝓝 ((L - 0) / (1 - 0))) :=
      (hm.sub (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ))).div
        (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ))) (by norm_num)
    rw [sub_zero, sub_zero, div_one] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop i] with h hh
    have hpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
    have hne : (h : ℝ) - i ≠ 0 := by
      have : (i : ℝ) < h := by exact_mod_cast hh
      linarith
    field_simp
  have hprod := tendsto_finsetProd (Finset.range k) hfac
  rw [Finset.prod_const, Finset.card_range] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop k] with h hh
  have hne : ∀ i ∈ Finset.range k, (h : ℝ) - i ≠ 0 := by
    intro i hi
    have : (i : ℝ) < h := by
      have := Finset.mem_range.mp hi
      exact_mod_cast (show i < h by omega)
    linarith
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hP : ∏ i ∈ Finset.range k, ((h : ℝ) - i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  rw [choose_eq (m h) k, choose_eq h k, div_div_div_cancel_right₀ hf, Finset.prod_div_distrib]

/-- The offsets below `h` outside the class of `c` are a share of about one
minus one over the wheel. -/
private theorem outside_share {p c : Nat} (hp : 0 < p) (hc : c < p) :
    Tendsto (fun h : Nat => (((Finset.range h).filter (fun t => t % p ≠ c)).card : ℝ) / h)
      atTop (𝓝 (1 - 1 / (p : ℝ))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hcount : ∀ h : Nat, ((Finset.range h).filter (fun t => t % p = c)).card =
      h / p + if c % p < h % p then 1 else 0 := by
    intro h
    rw [← Nat.count_modEq_card h hp c, Nat.count_eq_card_filter_range]
    congr 1
    ext t
    simp only [Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt hc]
  have hsplit : ∀ h : Nat, ((Finset.range h).filter (fun t => t % p = c)).card +
      ((Finset.range h).filter (fun t => t % p ≠ c)).card = h := fun h =>
    (Finset.card_filter_add_card_filter_not (s := Finset.range h) (fun t => t % p = c)).trans
      (Finset.card_range h)
  have hbounds : ∀ h : Nat, (h : ℝ) * (1 - 1 / p) - 1 ≤
      (((Finset.range h).filter (fun t => t % p ≠ c)).card : ℝ) ∧
      (((Finset.range h).filter (fun t => t % p ≠ c)).card : ℝ) ≤ (h : ℝ) * (1 - 1 / p) + 1 := by
    intro h
    have hs := hsplit h
    rw [hcount h] at hs
    have hsR : ((h / p : Nat) : ℝ) + ((if c % p < h % p then 1 else 0 : Nat) : ℝ) +
        (((Finset.range h).filter (fun t => t % p ≠ c)).card : ℝ) = h := by
      exact_mod_cast hs
    have he0 : (0 : ℝ) ≤ ((if c % p < h % p then 1 else 0 : Nat) : ℝ) := Nat.cast_nonneg _
    have he1 : ((if c % p < h % p then 1 else 0 : Nat) : ℝ) ≤ 1 := by
      split_ifs <;> norm_num
    have hd1 : ((h / p : Nat) : ℝ) ≤ (h : ℝ) / p := Nat.cast_div_le
    have e : (h : ℝ) = p * ((h / p : Nat) : ℝ) + ((h % p : Nat) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod h p).symm
    have hr : ((h % p : Nat) : ℝ) < p := by exact_mod_cast Nat.mod_lt h hp
    have hd2 : (h : ℝ) / p < ((h / p : Nat) : ℝ) + 1 := by
      rw [div_lt_iff₀ hpR]
      linarith
    have hhp : (h : ℝ) * (1 - 1 / p) = h - h / p := by ring
    rw [hhp]
    constructor <;> linarith
  have hup : Tendsto (fun h : Nat => (1 - 1 / (p : ℝ)) + 1 / (h : ℝ)) atTop
      (𝓝 ((1 - 1 / (p : ℝ)) + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat 1)
  have hlo : Tendsto (fun h : Nat => (1 - 1 / (p : ℝ)) - 1 / (h : ℝ)) atTop
      (𝓝 ((1 - 1 / (p : ℝ)) - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat 1)
  rw [add_zero] at hup
  rw [sub_zero] at hlo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with h hh
    have hpos : (0 : ℝ) < h := by exact_mod_cast hh
    rw [le_div_iff₀ hpos, sub_mul, one_div_mul_cancel hpos.ne']
    linarith [(hbounds h).1]
  · filter_upwards [eventually_gt_atTop 0] with h hh
    have hpos : (0 : ℝ) < h := by exact_mod_cast hh
    rw [div_le_iff₀ hpos, add_mul, one_div_mul_cancel hpos.ne']
    linarith [(hbounds h).2]

theorem one_wheel_average_holds : one_wheel_average := by
  intro p k hp hk
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hr : 0 < 1 - 1 / (p : ℝ) := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [sub_pos, div_lt_one hpR]
    linarith
  have hD : (p : ℝ) * (1 - 1 / (p : ℝ)) ^ k ≠ 0 := mul_ne_zero hpR.ne' (pow_ne_zero k hr.ne')
  -- the sum of the factors over the k-sets
  have hS : ∀ h : Nat, ∑ T ∈ (Finset.range h).powersetCard k, one_wheel_factor p T =
      (∑ c ∈ Finset.range p,
        ((((Finset.range h).filter (fun t => t % p ≠ c)).card.choose k : Nat) : ℝ)) /
        ((p : ℝ) * (1 - 1 / (p : ℝ)) ^ k) := by
    intro h
    calc ∑ T ∈ (Finset.range h).powersetCard k, one_wheel_factor p T
        = ∑ T ∈ (Finset.range h).powersetCard k,
            ((p - w T p : Nat) : ℝ) / ((p : ℝ) * (1 - 1 / (p : ℝ)) ^ k) := by
          refine Finset.sum_congr rfl (fun T hT => ?_)
          have hcard : T.card = k := (Finset.mem_powersetCard.mp hT).2
          unfold one_wheel_factor
          rw [hcard, Nat.cast_sub (w_le T hp0),
            show (1 : ℝ) - (w T p : ℝ) / p = ((p : ℝ) - w T p) / p by
              rw [sub_div, div_self hpR.ne'],
            div_div]
      _ = (((∑ T ∈ (Finset.range h).powersetCard k, (p - w T p) : Nat)) : ℝ) /
            ((p : ℝ) * (1 - 1 / (p : ℝ)) ^ k) := by
          rw [Nat.cast_sum, Finset.sum_div]
      _ = _ := by
          rw [sum_avoid h k p hp0, Nat.cast_sum]
  have hlim : Tendsto (fun h : Nat => ∑ c ∈ Finset.range p,
      ((((Finset.range h).filter (fun t => t % p ≠ c)).card.choose k : Nat) : ℝ) /
        (h.choose k : ℝ)) atTop (𝓝 (∑ c ∈ Finset.range p, (1 - 1 / (p : ℝ)) ^ k)) := by
    apply tendsto_finsetSum
    intro c hc
    exact choose_ratio k (fun h => ((Finset.range h).filter (fun t => t % p ≠ c)).card) _
      (outside_share hp0 (Finset.mem_range.mp hc))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlim
  have hfinal := hlim.div_const ((p : ℝ) * (1 - 1 / (p : ℝ)) ^ k)
  rw [div_self hD] at hfinal
  refine hfinal.congr (fun h => ?_)
  rw [hS h, ← Finset.sum_div]
  exact div_right_comm _ _ _

#print axioms RNS.GallagherLocal.one_wheel_average_holds

end RNS.GallagherLocal
