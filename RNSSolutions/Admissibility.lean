/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Algebra.Field.ZMod        -- remainders modulo a prime form a field
import Mathlib.Tactic.Push               -- `push Not`
import Mathlib.Tactic.NormNum.Prime            -- `norm_num` proving small numbers prime
import RNSNetwork.Nodes.Admissibility.Conclusions

/-!
# Proofs for Admissibility

Proves the four conclusions of `RNS.Admissibility`. Each tactic proof is
copied from `rns_sieve_6.lean` (Part B Step 1 and Part D); the only changes
are an `unfold` of the stated claim at the start, and the helper
`admissible_of_large_primes` renamed `admissible_of_large_primes_aux` so it
does not collide with the claim of the same name.
-/

namespace RNS.Admissibility

private theorem w_le_card (T : Finset Nat) (p : Nat) : w T p ≤ T.card := by
  unfold w
  exact Finset.card_image_le

private theorem admissible_of_large_primes_aux (T : Finset Nat) :
    (∀ p, p.Prime → p ≤ T.card → w T p < p) → is_admissible T := by
  intro h p hp
  by_cases hle : p ≤ T.card
  · exact h p hp hle
  · push Not at hle
    exact lt_of_le_of_lt (w_le_card T p) hle

theorem admissible_of_large_primes_holds : admissible_of_large_primes := by
  unfold admissible_of_large_primes
  exact admissible_of_large_primes_aux

theorem zero_two_admissible_holds : zero_two_admissible := by
  unfold zero_two_admissible
  apply admissible_of_large_primes_aux
  intro p hp hle
  have hcard : ({0, 2} : Finset Nat).card = 2 := by decide
  rw [hcard] at hle
  have hp2 : p = 2 := by
    have := hp.two_le
    omega
  subst hp2
  decide

theorem zero_two_four_not_admissible_holds : zero_two_four_not_admissible := by
  unfold zero_two_four_not_admissible
  intro h
  have h3 := h 3 (by norm_num)
  exact absurd h3 (by decide)

private theorem ap_offsets_card (d k : Nat) (hd : d ≠ 0) : (ap_offsets d k).card = k := by
  unfold ap_offsets
  have hinj : Function.Injective (fun i : Nat => i * d) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd) hab
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

private theorem w_ap_offsets_of_dvd (d k p : Nat) (_hp : p.Prime) (hdvd : p ∣ d)
    (hk : 1 ≤ k) : w (ap_offsets d k) p = 1 := by
  unfold w ap_offsets
  rw [Finset.image_image]
  show ((Finset.range k).image (fun i => i * d % p)).card = 1
  have himg : (Finset.range k).image (fun i => i * d % p) = {0} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨i, _, rfl⟩
      obtain ⟨c, hc⟩ := hdvd.mul_left i
      rw [hc]
      exact Nat.mul_mod_right p c
    · rintro rfl
      exact ⟨0, by omega, by simp⟩
  rw [himg]
  exact Finset.card_singleton 0

private theorem w_ap_offsets_of_not_dvd (d k p : Nat) (hp : p.Prime) (hnd : ¬ p ∣ d)
    (hpk : p ≤ k) : w (ap_offsets d k) p = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.pos.ne'⟩
  unfold w ap_offsets
  rw [Finset.image_image]
  show ((Finset.range k).image (fun i => i * d % p)).card = p
  have himg : (Finset.range k).image (fun i => i * d % p) = Finset.range p := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact Nat.mod_lt _ hp.pos
    · intro hxp
      have hdne : (d : ZMod p) ≠ 0 := fun h => hnd ((ZMod.natCast_eq_zero_iff d p).mp h)
      set y : ZMod p := (x : ZMod p) * (d : ZMod p)⁻¹ with hydef
      have hylt : y.val < p := ZMod.val_lt y
      have hyk : y.val < k := lt_of_lt_of_le hylt hpk
      refine ⟨y.val, hyk, ?_⟩
      have hcast : ((y.val * d : ℕ) : ZMod p) = (x : ZMod p) := by
        push_cast
        rw [ZMod.natCast_rightInverse y, hydef, mul_assoc, inv_mul_cancel₀ hdne, mul_one]
      have hlt : (y.val * d) % p < p := Nat.mod_lt _ hp.pos
      have heqcast : (((y.val * d) % p : ℕ) : ZMod p) = ((x : ℕ) : ZMod p) := by
        rw [ZMod.natCast_mod (y.val * d) p]
        exact hcast
      have hveq := congrArg ZMod.val heqcast
      rwa [ZMod.val_cast_of_lt hlt, ZMod.val_cast_of_lt hxp] at hveq
  rw [himg, Finset.card_range]

theorem ap_offsets_admissible_iff_holds : ap_offsets_admissible_iff := by
  unfold ap_offsets_admissible_iff
  intro d k hd
  constructor
  · intro hadm p hp hpk
    unfold is_admissible at hadm
    by_contra hnd
    have hw := w_ap_offsets_of_not_dvd d k p hp hnd hpk
    have hlt := hadm p hp
    omega
  · intro hall
    apply admissible_of_large_primes_aux
    intro p hp hple
    rw [ap_offsets_card d k hd] at hple
    have h2 := hp.two_le
    have hk1 : 1 ≤ k := by omega
    have hdvd := hall p hp hple
    rw [w_ap_offsets_of_dvd d k p hp hdvd hk1]
    exact hp.one_lt

end RNS.Admissibility

#print axioms RNS.Admissibility.admissible_of_large_primes_holds
#print axioms RNS.Admissibility.zero_two_admissible_holds
#print axioms RNS.Admissibility.zero_two_four_not_admissible_holds
#print axioms RNS.Admissibility.ap_offsets_admissible_iff_holds
