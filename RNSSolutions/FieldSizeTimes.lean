/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.FieldSizeTimes.Conclusions
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Int

/-!
# Proofs for FieldSizeTimes

Draft (2026-11-23).

With `N` parts and the bound one part, being far means the remainder is from 1
to `N - 1`, i.e. not 0. For consecutive speeds and a prime number of runners, a
prime dividing a product divides a factor, and no speed from 1 to one less than
the prime is a multiple of it.
-/

namespace RNS.FieldSizeTimes

open RNS.PileUpLock

theorem field_size_far_iff_holds : field_size_far_iff := by
  intro N y hN
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have hr0 : 0 ≤ y % (N : ℤ) := Int.emod_nonneg y (ne_of_gt hN')
  have hr1 : y % (N : ℤ) < N := Int.emod_lt_of_pos y hN'
  rw [Int.dvd_iff_emod_eq_zero]
  unfold far
  constructor
  · rintro ⟨h1, _⟩ h0
    rw [h0] at h1
    linarith
  · intro h0
    have hr2 : 1 ≤ y % (N : ℤ) := by omega
    have hr3 : 1 ≤ (N : ℤ) - y % (N : ℤ) := by omega
    constructor
    · nlinarith
    · nlinarith

theorem field_size_lonely_iff_step (h : field_size_far_iff) : field_size_lonely_iff := by
  intro S s
  unfold lonely_at
  constructor
  · rintro ⟨_, hS⟩ v hv
    exact (h _ _ (by omega)).mp (hS v hv)
  · intro hS
    exact ⟨by omega, fun v hv => (h _ _ (by omega)).mpr (hS v hv)⟩

theorem field_size_lonely_iff_holds : field_size_lonely_iff :=
  field_size_lonely_iff_step field_size_far_iff_holds

theorem consecutive_prime_field_step (h : field_size_lonely_iff) : consecutive_prime_field := by
  intro k hk s
  have hcard : (Finset.Icc (1 : ℤ) k).card = k := by
    rw [Int.card_Icc]
    simp
  have hk1 : 1 ≤ k := by
    have := hk.two_le
    omega
  have hp : Prime ((k + 1 : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hk
  have key := h (Finset.Icc (1 : ℤ) k) s
  rw [hcard] at key
  rw [key]
  constructor
  · intro hall hs
    have h1 : (1 : ℤ) ∈ Finset.Icc (1 : ℤ) k := by
      rw [Finset.mem_Icc]
      constructor
      · exact le_refl _
      · exact_mod_cast hk1
    apply hall 1 h1
    rw [one_mul]
    exact hs
  · intro hs v hv hdiv
    rw [Finset.mem_Icc] at hv
    rcases hp.dvd_or_dvd hdiv with h1 | h1
    · have hle := Int.le_of_dvd (by omega) h1
      push_cast at hle
      omega
    · exact hs h1

theorem consecutive_prime_field_holds : consecutive_prime_field :=
  consecutive_prime_field_step field_size_lonely_iff_holds

end RNS.FieldSizeTimes

#print axioms RNS.FieldSizeTimes.field_size_far_iff_holds
#print axioms RNS.FieldSizeTimes.field_size_lonely_iff_holds
#print axioms RNS.FieldSizeTimes.consecutive_prime_field_holds
