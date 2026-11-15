/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.GermainReciprocals.Conclusions
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Proofs for GermainReciprocals

Imports claims only. `germain_count_le` is a step from
`PatternUpperBound.pattern_count_le` and `BadWheels.blocked_le_card` /
`blocked_eq_card_iff`; `germain_reciprocal_summable` a step from it and
`PatternReciprocals.summable_of_count_bound`.

The bad factor of the two forms `n` and `2n + 1` is 1: a wheel larger than 2
dividing the bad product would block fewer than two positions
(`BadWheels.blocked_eq_card_iff`), but every odd wheel blocks 0 (where `n` is
divisible) and half of (the wheel − 1) (where `2n + 1` equals the wheel).
-/

namespace RNS.GermainReciprocals

open RNS.BadWheels RNS.PatternUpperBound

/-- The Sophie Germain pattern: the forms `n` and `2n + 1`. -/
def germain_forms : Finset (ℕ × ℕ) := {(1, 0), (2, 1)}

theorem germain_forms_card : germain_forms.card = 2 :=
  Finset.card_pair (by decide)

theorem germain_forms_primitive : primitive_forms germain_forms := by
  intro ℓ hℓ
  unfold germain_forms at hℓ
  rcases Finset.mem_insert.mp hℓ with rfl | hℓ'
  · exact ⟨le_rfl, Nat.coprime_one_left 0⟩
  · rw [Finset.mem_singleton] at hℓ'
    subst hℓ'
    exact ⟨by norm_num, Nat.coprime_one_right 2⟩

theorem mem_blocked {L : Finset (ℕ × ℕ)} {q r : ℕ} :
    r ∈ blocked L q ↔ r < q ∧ ∃ ℓ ∈ L, (ℓ.1 * r + ℓ.2) % q = 0 := by
  unfold blocked
  rw [Finset.mem_filter, Finset.mem_range]

/-- Two different blocked positions make a blocked count of at least 2. -/
theorem two_le_blocked {L : Finset (ℕ × ℕ)} {q r s : ℕ} (hr : r ∈ blocked L q)
    (hs : s ∈ blocked L q) (hne : r ≠ s) : 2 ≤ blocked_count L q := by
  unfold blocked_count
  have h : ({r, s} : Finset ℕ) ⊆ blocked L q := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hr
    · rw [Finset.mem_singleton] at hx'
      rw [hx']
      exact hs
  calc 2 = ({r, s} : Finset ℕ).card := (Finset.card_pair hne).symm
    _ ≤ _ := Finset.card_le_card h

/-- **The bad factor of the Sophie Germain pattern is 1.** -/
theorem germain_bad_factor (h_le : blocked_le_card) (h_eq : blocked_eq_card_iff) :
    bad_factor germain_forms = 1 := by
  unfold bad_factor
  apply Finset.prod_eq_one
  intro q hq
  exfalso
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
  obtain ⟨hqP, hqd, _⟩ := Nat.mem_primeFactors.mp hq1
  rw [germain_forms_card] at hq2
  have hcop : ∀ ℓ ∈ germain_forms, Nat.Coprime ℓ.1 ℓ.2 :=
    fun ℓ hℓ => (germain_forms_primitive ℓ hℓ).2
  have hdvd : (q : ℤ) ∣ bad_product germain_forms := Int.natCast_dvd.mpr hqd
  have hne : (blocked germain_forms q).card ≠ germain_forms.card :=
    fun h => ((h_eq _ q hqP hcop).mp h) hdvd
  have hle := h_le germain_forms q hqP hcop
  rw [germain_forms_card] at hne hle
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hqP.odd_of_ne_two (by omega))
  have h0 : 0 ∈ blocked germain_forms q :=
    mem_blocked.mpr ⟨hqP.pos, (1, 0), by simp [germain_forms], by simp⟩
  have h1 : (q - 1) / 2 ∈ blocked germain_forms q := by
    refine mem_blocked.mpr ⟨by omega, (2, 1), by simp [germain_forms], ?_⟩
    have h2 : 2 * ((q - 1) / 2) + 1 = q := by omega
    show (2 * ((q - 1) / 2) + 1) % q = 0
    rw [h2, Nat.mod_self]
  have h2 := two_le_blocked h0 h1 (by omega)
  unfold blocked_count at h2
  omega

theorem germain_count_eq (N : ℕ) :
    RNS.PatternReciprocals.position_count germain N = pattern_count germain_forms N := by
  unfold RNS.PatternReciprocals.position_count pattern_count
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro n _
  simp [germain, germain_forms]

theorem germain_count_le_step (h_count : pattern_count_le) (h_le : blocked_le_card)
    (h_eq : blocked_eq_card_iff) : germain_count_le := by
  obtain ⟨C, N₀, hC⟩ := h_count 2 (by norm_num)
  refine ⟨C, N₀, fun N hN => ?_⟩
  have h := hC germain_forms germain_forms_primitive germain_forms_card N hN
  rw [germain_bad_factor h_le h_eq, mul_one] at h
  rw [germain_count_eq]
  exact h

theorem germain_reciprocal_summable_step
    (h_sum : RNS.PatternReciprocals.summable_of_count_bound) (h_c : germain_count_le) :
    germain_reciprocal_summable :=
  h_sum germain h_c

end RNS.GermainReciprocals

#print axioms RNS.GermainReciprocals.germain_count_le_step
#print axioms RNS.GermainReciprocals.germain_reciprocal_summable_step
