/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SingularSeries.Conclusions
import RNSNetwork.Nodes.TwinConstant.Conclusions
import RNSNetwork.Nodes.GapConstant.Conclusions
import Mathlib

/-!
# Proofs for GapConstant

Imports claims only, never other nodes' proofs. The claims are steps taking
`SingularSeries.factor_multipliable` (and, for the classical form,
`TwinConstant.twin_prime_constant_eq_classical`) as named hypotheses, joined
in `RNSSolutions/Assemble.lean`.

Idea. Wheel by wheel, the factor for `{0, g}` is the twin factor times a
correction: 1 at the wheel 2 (both patterns block one position there), the
prime minus one over the prime minus two at an odd prime dividing `g` (one
blocked position instead of two), and 1 elsewhere. The corrections differ
from 1 only at finitely many wheels, so the infinite product of the factors
splits as the twin product times the finite product of the corrections
(`Multipliable.tprod_mul`, `tprod_eq_prod`).
-/

namespace RNS.GapConstant

/-- The correction at one wheel. -/
private noncomputable def corr (g p : Nat) : ℝ :=
  if p ∣ g ∧ p ≠ 2 then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

private theorem w_pair (g p : Nat) : w {0, g} p = if p ∣ g then 1 else 2 := by
  unfold w
  rw [Finset.image_insert, Finset.image_singleton, Nat.zero_mod]
  split_ifs with h
  · rw [Nat.mod_eq_zero_of_dvd h]
    simp
  · have h0 : g % p ≠ 0 := fun h0 => h (Nat.dvd_of_mod_eq_zero h0)
    exact Finset.card_pair (Ne.symm h0)

private theorem card_pair_zero {g : Nat} (hg : g ≠ 0) : ({0, g} : Finset Nat).card = 2 :=
  Finset.card_pair (Ne.symm hg)

private theorem factor_gap {g : Nat} (hg0 : g ≠ 0) (hg : Even g) (p : Nat) (hp : p.Prime) :
    singular_series_factor {0, g} p = singular_series_factor {0, 2} p * corr g p := by
  have h2 : (2 : Nat) ∣ g := even_iff_two_dvd.mp hg
  unfold singular_series_factor corr
  rw [card_pair_zero hg0, card_pair_zero (by norm_num : (2 : Nat) ≠ 0), w_pair g p, w_pair 2 p]
  by_cases hp2 : p = 2
  · subst hp2
    simp [h2]
  · have h2p : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    rw [if_neg h2p]
    by_cases hpg : p ∣ g
    · rw [if_pos hpg, if_pos ⟨hpg, hp2⟩]
      have h3 : 3 ≤ p := by have := hp.two_le; omega
      have h3' : (3 : ℝ) ≤ p := by exact_mod_cast h3
      have hne1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hne2 : (p : ℝ) - 2 ≠ 0 := by linarith
      norm_num
      field_simp
    · rw [if_neg hpg, if_neg (fun h => hpg h.1)]
      ring

/-- The wheels where the correction is not 1. -/
private noncomputable def corrSupport (g : Nat) : Finset Nat.Primes :=
  (g.primeFactors.filter (fun p => p ≠ 2)).preimage (Subtype.val : Nat.Primes → Nat)
    Subtype.val_injective.injOn

private theorem corr_out {g : Nat} (hg0 : g ≠ 0) :
    ∀ p ∉ corrSupport g, corr g (p : Nat) = 1 := by
  intro p hp
  unfold corr
  rw [if_neg]
  rintro ⟨hpg, hp2⟩
  apply hp
  unfold corrSupport
  exact Finset.mem_preimage.mpr
    (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨p.2, hpg, hg0⟩, hp2⟩)

private theorem corr_prod {g : Nat} :
    ∏ p ∈ corrSupport g, corr g (p : Nat) = odd_divisor_correction g := by
  unfold corrSupport odd_divisor_correction
  refine (Finset.prod_preimage (Subtype.val : Nat.Primes → Nat) _ Subtype.val_injective.injOn (corr g)
    (fun x hx hnr => (hnr ⟨(⟨x, (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hx).1).1⟩ :
      {p : Nat // p.Prime}), rfl⟩).elim)).trans ?_
  refine Finset.prod_congr rfl (fun x hx => ?_)
  obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
  unfold corr
  rw [if_pos ⟨(Nat.mem_primeFactors.mp hx1).2.1, hx2⟩]

theorem gap_constant_eq_twin_mul_step (hmul : RNS.SingularSeries.factor_multipliable) :
    gap_constant_eq_twin_mul := by
  intro g hg0 hg
  have hf : Multipliable (fun p : Nat.Primes => singular_series_factor {0, 2} p) :=
    hmul {0, 2} (by decide)
  have hr : Multipliable (fun p : Nat.Primes => corr g p) :=
    multipliable_of_ne_finset_one (corr_out hg0)
  unfold hardy_littlewood_constant
  rw [show (fun p : Nat.Primes => singular_series_factor {0, g} p) =
      fun p : Nat.Primes => singular_series_factor {0, 2} p * corr g p from
    funext fun p => factor_gap hg0 hg p p.2]
  rw [hf.tprod_mul hr, tprod_eq_prod (corr_out hg0), corr_prod]

theorem gap_constant_classical_step (hmul : RNS.SingularSeries.factor_multipliable)
    (htwin : RNS.TwinConstant.twin_prime_constant_eq_classical) : gap_constant_classical := by
  intro g hg0 hg
  rw [gap_constant_eq_twin_mul_step hmul g hg0 hg]
  unfold RNS.TwinConstant.twin_prime_constant_eq_classical at htwin
  rw [htwin]

private theorem six_correction : odd_divisor_correction 6 = 2 := by
  have hs : (6 : Nat).primeFactors.filter (fun p => p ≠ 2) = {3} := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hp, hd, -⟩, h2⟩
      have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hd
      interval_cases p <;> first | rfl | (exfalso; revert hp hd h2; decide)
    · rintro rfl
      exact ⟨⟨Nat.prime_three, by norm_num, by norm_num⟩, by norm_num⟩
  unfold odd_divisor_correction
  rw [hs, Finset.prod_singleton]
  norm_num

theorem sexy_constant_eq_two_twin_step (hmul : RNS.SingularSeries.factor_multipliable) :
    sexy_constant_eq_two_twin := by
  unfold sexy_constant_eq_two_twin
  rw [gap_constant_eq_twin_mul_step hmul 6 (by norm_num) (by decide), six_correction]
  ring

theorem goldbach_constant_step (hmul : RNS.SingularSeries.factor_multipliable) :
    goldbach_constant := by
  intro N hN0 hN
  rw [← gap_constant_eq_twin_mul_step hmul N hN0 hN]
  unfold goldbach_constant_of hardy_littlewood_constant
  congr 1
  funext p
  unfold singular_series_factor w
  rw [card_pair_zero hN0, Finset.image_insert, Finset.image_singleton, Nat.zero_mod]
  norm_num

#print axioms RNS.GapConstant.gap_constant_eq_twin_mul_step
#print axioms RNS.GapConstant.gap_constant_classical_step
#print axioms RNS.GapConstant.sexy_constant_eq_two_twin_step
#print axioms RNS.GapConstant.goldbach_constant_step

end RNS.GapConstant
