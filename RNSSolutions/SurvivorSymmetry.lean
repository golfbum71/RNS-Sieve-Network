/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SurvivorSymmetry.Conclusions

/-!
# Proofs for SurvivorSymmetry

Imports claims only, never other nodes' proofs. `survivor_reflection` is
proved directly; `survivor_count_reflection` is proved from it as a step,
joined in `RNSSolutions/Assemble.lean`.
-/

namespace RNS.SurvivorSymmetry

/-- A wheel of the cycle divides a position exactly when it divides the
position's reflection. -/
private theorem dvd_reflection_iff (W : Finset Nat) (k q : Nat) (hk : k ≤ W.prod id)
    (hq : q ∈ W) : q ∣ k ↔ q ∣ W.prod id - k := by
  have hP : q ∣ W.prod id := Finset.dvd_prod_of_mem id hq
  have e : W.prod id - k + k = W.prod id := Nat.sub_add_cancel hk
  constructor
  · intro h
    exact Nat.dvd_sub hP h
  · intro h
    rw [← e] at hP
    exact (Nat.dvd_add_right h).mp hP

/-- **Mirror symmetry**, proved. -/
theorem survivor_reflection_holds : survivor_reflection := by
  intro W k hk
  constructor
  · intro h q hq hd
    exact h q hq ((dvd_reflection_iff W k q hk hq).mpr hd)
  · intro h q hq hd
    exact h q hq ((dvd_reflection_iff W k q hk hq).mp hd)

/-- **Mirror symmetry, counting form**, from the position-by-position form.
Split the cycle's survivors at `t`. Those up to `t` are the survivors up to
`t`. Those after `t` stop short of the cycle length itself (every wheel
divides it), and reflecting them in the cycle matches them one-for-one with
the survivors up to the cycle length minus `t` minus 1. -/
theorem survivor_count_reflection_step (hrefl : survivor_reflection) :
    survivor_count_reflection := by
  intro W t hW ht
  have hPns : ¬ ∀ q ∈ W, ¬ q ∣ W.prod id := by
    obtain ⟨q, hq⟩ := hW
    exact fun h => h q hq (Finset.dvd_prod_of_mem id hq)
  rw [← Finset.card_filter_add_card_filter_not (s := survivors_upto W (W.prod id))
    (fun k => k ≤ t)]
  congr 1
  · congr 1
    ext k
    simp only [survivors_upto, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨⟨h1, by omega⟩, h3⟩, h2⟩
    · rintro ⟨⟨⟨h1, _⟩, h3⟩, h2⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  · apply Finset.card_nbij' (fun j => W.prod id - j) (fun k => W.prod id - k)
    · intro j hj
      simp only [Finset.mem_coe, survivors_upto, Finset.mem_filter, Finset.mem_Icc] at hj ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hj
      exact ⟨⟨⟨by omega, by omega⟩, (hrefl W j (by omega)).mp h3⟩, by omega⟩
    · intro k hk
      simp only [Finset.mem_coe, survivors_upto, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hk
      have hkP : k ≠ W.prod id := by
        rintro rfl
        exact hPns h3
      exact ⟨⟨by omega, by omega⟩, (hrefl W k h2).mp h3⟩
    · intro j hj
      simp only [Finset.mem_coe, survivors_upto, Finset.mem_filter, Finset.mem_Icc] at hj
      dsimp only
      omega
    · intro k hk
      simp only [Finset.mem_coe, survivors_upto, Finset.mem_filter, Finset.mem_Icc] at hk
      dsimp only
      omega

end RNS.SurvivorSymmetry

#print axioms RNS.SurvivorSymmetry.survivor_reflection_holds
#print axioms RNS.SurvivorSymmetry.survivor_count_reflection_step
