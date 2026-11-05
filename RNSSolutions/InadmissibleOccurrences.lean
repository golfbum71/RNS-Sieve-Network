/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Tactic.NormNum.Prime
import RNSNetwork.Nodes.InadmissibleOccurrences.Conclusions

/-!
# Proofs for InadmissibleOccurrences

Imports claims only, never other nodes' proofs. Both claims are proved
directly from the definition of `w`; the second uses the first.
-/

namespace RNS.InadmissibleOccurrences

/-- **A covered wheel forces its prime into every occurrence**, proved. The
pattern's remainders fill the whole wheel, so one of them is the position that
makes `n + t` a multiple of `p`; a prime multiple of `p` is `p`. -/
theorem inadmissible_occurrence_contains_prime_holds : inadmissible_occurrence_contains_prime := by
  intro T p n hp hw hprime
  have hsub : T.image (fun t => t % p) ⊆ Finset.range p := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
  have heq : T.image (fun t => t % p) = Finset.range p := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_range]
    unfold w at hw
    omega
  have hmem : (p - n % p) % p ∈ T.image (fun t => t % p) := by
    rw [heq]
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
  obtain ⟨t, ht, htm⟩ := Finset.mem_image.mp hmem
  refine ⟨t, ht, ?_⟩
  have hdvd : p ∣ n + t := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, htm]
    have hlt := Nat.mod_lt n hp.pos
    rcases Nat.eq_zero_or_pos (n % p) with h0 | h0
    · simp [h0]
    · rw [Nat.mod_eq_of_lt (by omega : p - n % p < p), Nat.add_sub_cancel' (by omega),
        Nat.mod_self]
  exact (((hprime t ht).eq_one_or_self_of_dvd p hdvd).resolve_left hp.one_lt.ne').symm

/-- **The gap block 2, 4, 2, 4, 2 occurs once**, proved. The offsets cover all
five positions on the wheel of size 5, so some member is 5; only the start 5
works (the start 3 would make 9 a member). -/
theorem gap_block_24242_unique_holds : gap_block_24242_unique := by
  intro n h0 h2 h6 h8 h12 h14
  have hw : w ({0, 2, 6, 8, 12, 14} : Finset Nat) 5 = 5 := by decide
  have hall : ∀ t ∈ ({0, 2, 6, 8, 12, 14} : Finset Nat), (n + t).Prime := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using h0
    · exact h2
    · exact h6
    · exact h8
    · exact h12
    · exact h14
  obtain ⟨t, ht, hnt⟩ :=
    inadmissible_occurrence_contains_prime_holds _ 5 n (by norm_num) hw hall
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · have h3 : n = 3 := by omega
    subst h3
    norm_num at h6
  all_goals omega

end RNS.InadmissibleOccurrences

#print axioms RNS.InadmissibleOccurrences.inadmissible_occurrence_contains_prime_holds
#print axioms RNS.InadmissibleOccurrences.gap_block_24242_unique_holds
