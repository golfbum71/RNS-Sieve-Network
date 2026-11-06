/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunPureSieve.Conclusions
import Mathlib.Data.Nat.Factorization.Basic           -- `Nat.Ioc_filter_dvd_card_eq_div`
import Mathlib.Data.Nat.Choose.Sum                    -- `Int.alternating_sum_range_choose_eq_choose`
import Mathlib.Algebra.BigOperators.Associated        -- `Finset.prod_primes_dvd`
import Mathlib.Algebra.BigOperators.Ring.Finset       -- `Finset.natCast_card_filter`
import Mathlib.Algebra.Order.BigOperators.Group.Finset -- `Finset.sum_le_sum`
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma -- `Finset.sum_comm`
import Mathlib.Algebra.Ring.Parity                    -- `Even.neg_one_pow`, `Odd.neg_one_pow`

/-!
# Proofs for BrunPureSieve

Imports claims only, never other nodes' proofs. Rests on no other node.

Built clean by `lake build RNSSolutions` on 2026-11-06; `#print axioms` shows only
the standard three.

Idea. For prime wheels, the product of a set of wheels divides a position
exactly when every wheel in the set does, so the multiples of the product
count the positions whose hit set contains the set. Swapping the sums, the
truncated count is a sum over positions of the signed number of subsets, of
size at most the stopping point, of the position's hit set. Grouped by size,
that is the alternating binomial sum up to the stopping point, which Mathlib
evaluates (`Int.alternating_sum_range_choose_eq_choose`): it is 1 for a
survivor (no hits), and for a position with at least one hit it is a single
binomial coefficient with the sign of the stopping point, or 0 once the
stopping point reaches the number of hits.
-/

namespace RNS.BrunPureSieve

/-- The wheels dividing the position `m`. -/
private def hitSet (W : Finset Nat) (m : Nat) : Finset Nat := W.filter (fun q => q ∣ m)

/-- Grouping the subsets by size gives the alternating binomial sum. -/
private theorem partial_signed (H : Finset Nat) (t : Nat) :
    ∑ D ∈ H.powerset.filter (fun D => D.card ≤ t), (-1 : ℤ) ^ D.card =
      ∑ j ∈ Finset.range (t + 1), (-1 : ℤ) ^ j * (H.card.choose j : ℤ) := by
  have hmap : ∀ D ∈ H.powerset.filter (fun D => D.card ≤ t), D.card ∈ Finset.range (t + 1) :=
    fun D hD => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hD).2)
  rw [← Finset.sum_fiberwise_of_maps_to' hmap (fun j => (-1 : ℤ) ^ j)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfib : (H.powerset.filter (fun D => D.card ≤ t)).filter (fun D => D.card = j) =
      H.powersetCard j := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, by omega⟩, h3⟩
  rw [hfib, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  exact mul_comm _ _

private theorem value_zero (t : Nat) :
    ∑ j ∈ Finset.range (t + 1), (-1 : ℤ) ^ j * ((0 : Nat).choose j : ℤ) = 1 := by
  rw [Finset.sum_range_succ']
  simp

private theorem value_succ (n t : Nat) :
    ∑ j ∈ Finset.range (t + 1), (-1 : ℤ) ^ j * ((n + 1).choose j : ℤ) =
      (-1 : ℤ) ^ t * (n.choose t : ℤ) :=
  Int.alternating_sum_range_choose_eq_choose

private theorem point_even (H : Finset Nat) (t : Nat) (ht : Even t) :
    (if H.card = 0 then (1 : ℤ) else 0) ≤
      ∑ D ∈ H.powerset.filter (fun D => D.card ≤ t), (-1 : ℤ) ^ D.card := by
  rw [partial_signed]
  generalize H.card = k
  cases k with
  | zero =>
    rw [value_zero]
    simp
  | succ n =>
    rw [value_succ, ht.neg_one_pow, one_mul, if_neg (Nat.add_one_ne_zero n)]
    exact Nat.cast_nonneg _

private theorem point_odd (H : Finset Nat) (t : Nat) (ht : Odd t) :
    ∑ D ∈ H.powerset.filter (fun D => D.card ≤ t), (-1 : ℤ) ^ D.card ≤
      (if H.card = 0 then (1 : ℤ) else 0) := by
  rw [partial_signed]
  generalize H.card = k
  cases k with
  | zero =>
    rw [value_zero]
    simp
  | succ n =>
    rw [value_succ, ht.neg_one_pow, neg_one_mul, if_neg (Nat.add_one_ne_zero n)]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)

private theorem point_exact (H : Finset Nat) (t : Nat) (hk : H.card ≤ t) :
    (if H.card = 0 then (1 : ℤ) else 0) =
      ∑ D ∈ H.powerset.filter (fun D => D.card ≤ t), (-1 : ℤ) ^ D.card := by
  rw [partial_signed]
  generalize H.card = k at hk
  cases k with
  | zero =>
    rw [value_zero]
    simp
  | succ n =>
    rw [value_succ, Nat.choose_eq_zero_of_lt (show n < t by omega), Nat.cast_zero, mul_zero,
      if_neg (Nat.add_one_ne_zero n)]

/-- For prime wheels, the product of a set of them divides a position exactly
when the set lies inside the position's hit set. -/
private theorem prod_dvd_iff (W : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (D : Finset Nat)
    (hD : D ⊆ W) (m : Nat) : D.prod id ∣ m ↔ D ⊆ hitSet W m := by
  constructor
  · intro h q hq
    exact Finset.mem_filter.mpr ⟨hD hq, (Finset.dvd_prod_of_mem id hq).trans h⟩
  · intro h
    exact Finset.prod_primes_dvd m (fun a ha => (hW a (hD ha)).prime)
      (fun a ha => (Finset.mem_filter.mp (h ha)).2)

/-- The truncated count as a sum over positions. -/
private theorem truncated_eq_sum (W : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (N t : Nat) :
    truncated_count W N t = ∑ m ∈ Finset.Ioc 0 N,
      ∑ D ∈ (hitSet W m).powerset.filter (fun D => D.card ≤ t), (-1 : ℤ) ^ D.card := by
  unfold truncated_count
  have h1 : ∀ D ∈ W.powerset.filter (fun D => D.card ≤ t),
      (-1 : ℤ) ^ D.card * ((N / D.prod id : Nat) : ℤ) =
        ∑ m ∈ Finset.Ioc 0 N, if D.prod id ∣ m then (-1 : ℤ) ^ D.card else 0 := by
    intro D _
    rw [← Nat.Ioc_filter_dvd_card_eq_div, Finset.natCast_card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm (s := W.powerset.filter (fun D => D.card ≤ t))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext D
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hDW, hc⟩, hdvd⟩
    exact ⟨(prod_dvd_iff W hW D hDW m).mp hdvd, hc⟩
  · rintro ⟨hDH, hc⟩
    have hDW : D ⊆ W := fun q hq => (Finset.mem_filter.mp (hDH hq)).1
    exact ⟨⟨hDW, hc⟩, (prod_dvd_iff W hW D hDW m).mpr hDH⟩

/-- The survivor count as a sum over positions. -/
private theorem survivors_card_eq (W : Finset Nat) (N : Nat) :
    ((survivors_upto W N).card : ℤ) =
      ∑ m ∈ Finset.Ioc 0 N, if (hitSet W m).card = 0 then (1 : ℤ) else 0 := by
  have hS : survivors_upto W N = (Finset.Ioc 0 N).filter (fun m => (hitSet W m).card = 0) := by
    ext m
    simp only [survivors_upto, hitSet, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc,
      Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, by intro q hq; first | exact h3 hq | exact h3 q hq⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, by intro q hq; first | exact h3 hq | exact h3 q hq⟩
  rw [hS, Finset.natCast_card_filter]

theorem bonferroni_even_holds : bonferroni_even := by
  intro W N t hW ht
  rw [survivors_card_eq, truncated_eq_sum W hW]
  exact Finset.sum_le_sum fun m _ => point_even (hitSet W m) t ht

theorem bonferroni_odd_holds : bonferroni_odd := by
  intro W N t hW ht
  rw [survivors_card_eq, truncated_eq_sum W hW]
  exact Finset.sum_le_sum fun m _ => point_odd (hitSet W m) t ht

theorem legendre_exact_holds : legendre_exact := by
  intro W N t hW hWt
  rw [survivors_card_eq, truncated_eq_sum W hW]
  exact Finset.sum_congr rfl fun m _ =>
    point_exact (hitSet W m) t ((Finset.card_filter_le _ _).trans hWt)

/-! ## Any function of the position -/

/-- The wheels dividing `g m`. -/
private def hitSetFn (W : Finset Nat) (g : Nat → Nat) (m : Nat) : Finset Nat :=
  W.filter (fun q => q ∣ g m)

private theorem prod_dvd_iff_fn (W : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (g : Nat → Nat)
    (D : Finset Nat) (hD : D ⊆ W) (m : Nat) : D.prod id ∣ g m ↔ D ⊆ hitSetFn W g m := by
  constructor
  · intro h q hq
    exact Finset.mem_filter.mpr ⟨hD hq, (Finset.dvd_prod_of_mem id hq).trans h⟩
  · intro h
    exact Finset.prod_primes_dvd (g m) (fun a ha => (hW a (hD ha)).prime)
      (fun a ha => (Finset.mem_filter.mp (h ha)).2)

private theorem truncated_fn_eq_sum (W : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (g : Nat → Nat)
    (N t : Nat) :
    truncated_count_fn W g N t = ∑ m ∈ Finset.Ioc 0 N,
      ∑ D ∈ (hitSetFn W g m).powerset.filter (fun D => D.card ≤ t), (-1 : ℤ) ^ D.card := by
  unfold truncated_count_fn
  have h1 : ∀ D ∈ W.powerset.filter (fun D => D.card ≤ t),
      (-1 : ℤ) ^ D.card * (((Finset.Ioc 0 N).filter (fun m => D.prod id ∣ g m)).card : ℤ) =
        ∑ m ∈ Finset.Ioc 0 N, if D.prod id ∣ g m then (-1 : ℤ) ^ D.card else 0 := by
    intro D _
    rw [Finset.natCast_card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm (s := W.powerset.filter (fun D => D.card ≤ t))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext D
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hDW, hc⟩, hdvd⟩
    exact ⟨(prod_dvd_iff_fn W hW g D hDW m).mp hdvd, hc⟩
  · rintro ⟨hDH, hc⟩
    have hDW : D ⊆ W := fun q hq => (Finset.mem_filter.mp (hDH hq)).1
    exact ⟨⟨hDW, hc⟩, (prod_dvd_iff_fn W hW g D hDW m).mpr hDH⟩

private theorem sifted_card_eq (W : Finset Nat) (g : Nat → Nat) (N : Nat) :
    ((sifted W g N).card : ℤ) =
      ∑ m ∈ Finset.Ioc 0 N, if (hitSetFn W g m).card = 0 then (1 : ℤ) else 0 := by
  have hS : sifted W g N = (Finset.Ioc 0 N).filter (fun m => (hitSetFn W g m).card = 0) := by
    unfold sifted
    refine Finset.filter_congr fun m _ => ?_
    simp only [hitSetFn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    constructor
    · intro h q hq
      first | exact h q hq | exact h hq
    · intro h q hq
      first | exact h hq | exact h q hq
  rw [hS, Finset.natCast_card_filter]

theorem bonferroni_even_fn_holds : bonferroni_even_fn := by
  intro W g N t hW ht
  rw [sifted_card_eq, truncated_fn_eq_sum W hW]
  exact Finset.sum_le_sum fun m _ => point_even (hitSetFn W g m) t ht

theorem bonferroni_odd_fn_holds : bonferroni_odd_fn := by
  intro W g N t hW ht
  rw [sifted_card_eq, truncated_fn_eq_sum W hW]
  exact Finset.sum_le_sum fun m _ => point_odd (hitSetFn W g m) t ht

theorem twin_bonferroni_upper_holds : twin_bonferroni_upper := by
  intro W N t hW ht
  exact bonferroni_even_fn_holds W (fun n => n * (n + 2)) N t hW ht

end RNS.BrunPureSieve

#print axioms RNS.BrunPureSieve.bonferroni_even_holds
#print axioms RNS.BrunPureSieve.bonferroni_odd_holds
#print axioms RNS.BrunPureSieve.legendre_exact_holds
#print axioms RNS.BrunPureSieve.bonferroni_even_fn_holds
#print axioms RNS.BrunPureSieve.bonferroni_odd_fn_holds
#print axioms RNS.BrunPureSieve.twin_bonferroni_upper_holds
