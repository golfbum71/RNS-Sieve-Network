/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PrimeGapsBridge.Conclusions

/-!
# Proofs for PrimeGapsBridge

Imports claims only, never other nodes' proofs. Rests on no other node.

Built clean by the GitHub Actions build on 2026-11-05.

Idea: on the wheel of size `p`, the positions the pattern occupies form a
subset of the `p` positions. It has fewer than `p` members exactly when some
position is missing, and a missing position is a residue class that no
member lands in.
-/

namespace RNS.PrimeGapsBridge

/-- On the wheel of size `p`, the pattern occupies fewer than `p` positions
exactly when some position below `p` is hit by no member. -/
private theorem w_lt_iff (T : Finset Nat) {p : Nat} (hp : 0 < p) :
    w T p < p ↔ ∃ a < p, ∀ h ∈ T, h % p ≠ a := by
  have hS : T.image (fun t => t % p) ⊆ Finset.range p := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Nat.mod_lt t hp)
  unfold w
  constructor
  · intro hlt
    by_contra hne
    have hall : ∀ a < p, ∃ h ∈ T, h % p = a := by
      intro a ha
      by_contra hno
      exact hne ⟨a, ha, fun h hh e => hno ⟨h, hh, e⟩⟩
    have hsub : Finset.range p ⊆ T.image (fun t => t % p) := by
      intro a ha
      obtain ⟨h, hh, e⟩ := hall a (Finset.mem_range.mp ha)
      exact Finset.mem_image.mpr ⟨h, hh, e⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_range] at hle
    omega
  · rintro ⟨a, ha, hno⟩
    have hnot : a ∉ T.image (fun t => t % p) := by
      intro hm
      obtain ⟨t, ht, e⟩ := Finset.mem_image.mp hm
      exact hno t ht e
    have hsub : T.image (fun t => t % p) ⊆ (Finset.range p).erase a :=
      Finset.subset_erase.mpr ⟨hS, hnot⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr ha), Finset.card_range] at hle
    omega

/-- For `p` above 0, "some residue class is missed" can always be witnessed by
a class below `p`. -/
private theorem missed_class_iff (T : Finset Nat) {p : Nat} (hp : 0 < p) :
    (∃ a : Nat, ∀ h ∈ T, ¬ (h ≡ a [MOD p])) ↔ ∃ a < p, ∀ h ∈ T, h % p ≠ a := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a % p, Nat.mod_lt a hp, fun h hh e => ha h hh ?_⟩
    show h % p = a % p
    exact e
  · rintro ⟨a, ha, hno⟩
    refine ⟨a, fun h hh hm => hno h hh ?_⟩
    have e : h % p = a % p := hm
    rwa [Nat.mod_eq_of_lt ha] at e

/-- **The two definitions agree**, proved. -/
theorem admissible_iff_primegaps_holds : admissible_iff_primegaps := by
  intro T
  unfold is_admissible primegaps_admissible
  constructor
  · intro h p hp
    exact (missed_class_iff T hp.pos).mpr ((w_lt_iff T hp.pos).mp (h p hp))
  · intro h p hp
    exact (w_lt_iff T hp.pos).mpr ((missed_class_iff T hp.pos).mp (h p hp))

end RNS.PrimeGapsBridge

#print axioms RNS.PrimeGapsBridge.admissible_iff_primegaps_holds
