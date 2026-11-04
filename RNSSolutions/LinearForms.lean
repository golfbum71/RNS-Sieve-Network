/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Tactic.NormNum.Prime      -- `norm_num` proving small numbers prime
import RNSNetwork.Nodes.LinearForms.Conclusions

/-!
# Proofs for LinearForms

Rests on no other node. Tactic proofs are copied from
`rns_sieve_6_parts_J_K.lean`, Part K (reported clean by `#print axioms`).
`sophie_germain` is now the shared Vocabulary definition, with the same
meaning as the source's.
-/

namespace RNS.LinearForms

private theorem sophieGermainSystem_pos : ∀ ℓ ∈ sophieGermainSystem, 0 < ℓ.1 := by
  decide

private theorem mem_sophieGermain_iff (n : Nat) :
    (∀ ℓ ∈ sophieGermainSystem, (ℓ.1 * n + ℓ.2).Prime) ↔ sophie_germain n := by
  unfold sophieGermainSystem sophie_germain
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨by simpa using h (1, 0) (Or.inl rfl),
           by simpa using h (2, 1) (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ ℓ (rfl | rfl)
    · simpa using h1
    · simpa using h2

theorem sophieGermainSystem_admissible_holds : sophieGermainSystem_admissible := by
  unfold sophieGermainSystem_admissible is_admissible_lin
  intro p hp
  by_cases h3 : p = 3
  · subst h3
    refine ⟨2, by norm_num, ?_⟩
    intro ℓ hℓ
    simp only [sophieGermainSystem, Finset.mem_insert, Finset.mem_singleton] at hℓ
    rcases hℓ with rfl | rfl
    · simp only [form_blocked_at]
      norm_num
    · simp only [form_blocked_at]
      norm_num
  · refine ⟨1, hp.one_lt, ?_⟩
    intro ℓ hℓ
    simp only [sophieGermainSystem, Finset.mem_insert, Finset.mem_singleton] at hℓ
    have hp3 : ¬ p ∣ 3 :=
      fun hdvd => h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd)
    rcases hℓ with rfl | rfl
    · simp only [form_blocked_at, Nat.mul_one, Nat.add_zero]
      have hp2 := hp.two_le
      have h1p : 1 < p := by omega
      rw [Nat.mod_eq_of_lt h1p]
      decide
    · simp only [form_blocked_at]
      intro hz
      exact hp3 (Nat.dvd_of_mod_eq_zero (by simpa using hz))

theorem sophie_germain_of_LinearForms_conjecture_holds :
    sophie_germain_of_LinearForms_conjecture := by
  unfold sophie_germain_of_LinearForms_conjecture
  intro hLF
  have hadm : is_admissible_lin sophieGermainSystem := by
    have h := sophieGermainSystem_admissible_holds
    unfold sophieGermainSystem_admissible at h
    exact h
  have h := hLF sophieGermainSystem sophieGermainSystem_pos hadm
  have heq : {n : Nat | ∀ ℓ ∈ sophieGermainSystem, (ℓ.1 * n + ℓ.2).Prime}
      = {n : Nat | sophie_germain n} := by
    ext n; exact mem_sophieGermain_iff n
  unfold sophie_germain_conjecture
  rwa [heq] at h

end RNS.LinearForms

#print axioms RNS.LinearForms.sophieGermainSystem_admissible_holds
#print axioms RNS.LinearForms.sophie_germain_of_LinearForms_conjecture_holds
