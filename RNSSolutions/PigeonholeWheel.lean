/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib
import RNSNetwork.Nodes.PigeonholeWheel.Conclusions

/-!
# Proofs for PigeonholeWheel

Rests on no other node. The one-pigeon lemmas (`lift_slot_injective`,
`lift_slot_bijective`, the closed copy and the open count) were checked on
Comparator Live (Lean v4.36.0-rc2, latest Mathlib) on 2026-11-09 before
being placed here.

The pigeonhole step is `Fintype.bijective_iff_injective_and_card`: the copies
of a position land on pairwise different slots, and there are as many copies
as slots, so every slot receives exactly one.
-/

namespace RNS.PigeonholeWheel

/-! ## One pigeon per wheel -/

/-- No two copies share a slot, because `q` does not divide `M`. -/
theorem lift_slot_injective (q M start : Nat) (hq : q.Prime) (hM : ¬ q ∣ M) :
    Function.Injective (lift_slot q M start) := by
  have : Fact q.Prime := ⟨hq⟩
  intro i j hij
  unfold lift_slot at hij
  have hMne : (M : ZMod q) ≠ 0 := fun h => hM ((ZMod.natCast_eq_zero_iff M q).mp h)
  push_cast at hij
  have hmul : (i.val : ZMod q) * (M : ZMod q) = (j.val : ZMod q) * (M : ZMod q) :=
    add_left_cancel hij
  have hicast : (i.val : ZMod q) = (j.val : ZMod q) := mul_right_cancel₀ hMne hmul
  have hival : (i.val : ZMod q).val = i.val := ZMod.val_cast_of_lt i.isLt
  have hjval : (j.val : ZMod q).val = j.val := ZMod.val_cast_of_lt j.isLt
  rw [hicast, hjval] at hival
  exact Fin.ext hival.symm

/-- **Pigeonhole.** `q` copies into `q` slots with no two sharing a slot:
every slot receives exactly one copy. -/
theorem lift_slot_bijective (q M start : Nat) (hq : q.Prime) (hM : ¬ q ∣ M) :
    Function.Bijective (lift_slot q M start) := by
  have : NeZero q := ⟨hq.ne_zero⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨lift_slot_injective q M start hq hM, ?_⟩
  rw [Fintype.card_fin, ZMod.card]

theorem one_closed_copy_holds : one_closed_copy := by
  intro q M start hq hM
  exact (lift_slot_bijective q M start hq hM).existsUnique 0

theorem open_copies_holds : open_copies := by
  intro q M start hq hM
  have : NeZero q := ⟨hq.ne_zero⟩
  have hbij := lift_slot_bijective q M start hq hM
  have himg : (Finset.univ.filter (fun i : Fin q => lift_slot q M start i ≠ 0)).image
      (lift_slot q M start) = Finset.univ.erase (0 : ZMod q) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      obtain ⟨i, hi⟩ := hbij.2 x
      exact ⟨i, by rw [hi]; exact hx, hi⟩
  rw [← Finset.card_image_of_injective _ hbij.1, himg,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-- A copy sits on the blocked slot exactly when the wheel divides it. -/
theorem lift_slot_eq_zero_iff (q M start : Nat) (i : Fin q) :
    lift_slot q M start i = 0 ↔ q ∣ start + i.val * M := by
  unfold lift_slot
  exact ZMod.natCast_eq_zero_iff _ q

/-! ## Survivors carried wheel by wheel -/

/-- A wheel that divides the cycle length closes a copy only if it closes the
original position. -/
private theorem dvd_of_dvd_lift {d x M i : Nat} (hdM : d ∣ M) (h : d ∣ x + i * M) :
    d ∣ x := by
  have h' : d ∣ i * M + x := by rwa [Nat.add_comm] at h
  exact (Nat.dvd_add_right (hdM.mul_left i)).mp h'

/-- **One wheel step.** An open position `x` of the cycle of length `M` has a
copy, on slot 1 of the new wheel `a`, that is open on every wheel; the
pigeonhole step picks it. -/
private theorem lift_survivor (W : Finset Nat) (a M x : Nat) (ha : a.Prime)
    (haM : ¬ a ∣ M) (h6 : 6 ∣ M) (hWM : ∀ q ∈ W, q ∣ M) (hx : x < M)
    (hsx : survives W x) :
    ∃ i : Fin a, x + i.val * M < a * M ∧ (x + i.val * M) % M = x ∧
      survives (insert a W) (x + i.val * M) := by
  have : Fact a.Prime := ⟨ha⟩
  obtain ⟨i, hi⟩ := (lift_slot_bijective a M x ha haM).2 1
  refine ⟨i, ?_, ?_, ?_⟩
  · have hi1 : i.val + 1 ≤ a := i.isLt
    have h1 : (i.val + 1) * M ≤ a * M := Nat.mul_le_mul hi1 (le_refl M)
    have h2 : (i.val + 1) * M = i.val * M + M := by ring
    linarith
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  · unfold survives at hsx ⊢
    obtain ⟨h2x, h3x, hWx⟩ := hsx
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact h2x (dvd_of_dvd_lift (dvd_trans (by norm_num : (2 : Nat) ∣ 6) h6) h)
    · intro h
      exact h3x (dvd_of_dvd_lift (dvd_trans (by norm_num : (3 : Nat) ∣ 6) h6) h)
    · intro q hq hdvd
      rcases Finset.mem_insert.mp hq with hqa | hqW
      · rw [hqa] at hdvd
        have hzero : lift_slot a M x i = 0 := (lift_slot_eq_zero_iff a M x i).mpr hdvd
        rw [hi] at hzero
        exact one_ne_zero hzero
      · exact hWx q hqW (dvd_of_dvd_lift (hWM q hqW) hdvd)

private theorem two_survivors (W : Finset Nat) :
    (∀ q ∈ W, q.Prime ∧ 5 ≤ q) →
    ∃ x y, x < 6 * ∏ p ∈ W, p ∧ y < 6 * ∏ p ∈ W, p ∧ x ≠ y ∧
      survives W x ∧ survives W y := by
  induction W using Finset.induction with
  | empty =>
    intro _
    rw [Finset.prod_empty]
    refine ⟨1, 5, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · unfold survives
      exact ⟨by decide, by decide, by simp⟩
    · unfold survives
      exact ⟨by decide, by decide, by simp⟩
  | @insert a W ha ih =>
    intro hW
    have ha' := hW a (Finset.mem_insert_self a W)
    have hW' : ∀ q ∈ W, q.Prime ∧ 5 ≤ q := fun q hq => hW q (Finset.mem_insert_of_mem hq)
    obtain ⟨x, y, hx, hy, hxy, hsx, hsy⟩ := ih hW'
    have h6 : 6 ∣ 6 * ∏ p ∈ W, p := Nat.dvd_mul_right 6 _
    have hWM : ∀ q ∈ W, q ∣ 6 * ∏ p ∈ W, p := fun q hq =>
      Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun p => p) hq) 6
    have haM : ¬ a ∣ 6 * ∏ p ∈ W, p := by
      have hap := ha'.1
      have ha2 : a ≠ 2 := by have := ha'.2; omega
      have ha3 : a ≠ 3 := by have := ha'.2; omega
      have hc2 : Nat.Coprime a 2 := (Nat.coprime_primes hap Nat.prime_two).mpr ha2
      have hc3 : Nat.Coprime a 3 := (Nat.coprime_primes hap Nat.prime_three).mpr ha3
      have hc6 : Nat.Coprime a 6 := Nat.Coprime.mul_right hc2 hc3
      have hcW : Nat.Coprime a (∏ p ∈ W, p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        have hne : a ≠ p := fun h => ha (by rw [h]; exact hp)
        exact (Nat.coprime_primes hap (hW' p hp).1).mpr hne
      exact (Nat.Prime.coprime_iff_not_dvd hap).mp (Nat.Coprime.mul_right hc6 hcW)
    obtain ⟨i, hxlt, hxmod, hsx'⟩ := lift_survivor W a _ x ha'.1 haM h6 hWM hx hsx
    obtain ⟨j, hylt, hymod, hsy'⟩ := lift_survivor W a _ y ha'.1 haM h6 hWM hy hsy
    rw [Finset.prod_insert ha]
    have hcyc : 6 * (a * ∏ p ∈ W, p) = a * (6 * ∏ p ∈ W, p) := by ring
    rw [hcyc]
    refine ⟨_, _, hxlt, hylt, ?_, hsx', hsy'⟩
    intro heq
    apply hxy
    rw [← hxmod, ← hymod, heq]

theorem two_survivors_persist_holds : two_survivors_persist :=
  two_survivors

/-! ## Two survivors, one safe spot -/

theorem pigeonhole_primes_unbounded_holds : pigeonhole_primes_unbounded := by
  intro limit
  by_contra hcon
  push Not at hcon
  have hW : ∀ q ∈ (Finset.range limit).filter (fun q => q.Prime ∧ 5 ≤ q),
      q.Prime ∧ 5 ≤ q := fun q hq => (Finset.mem_filter.mp hq).2
  obtain ⟨x, y, _, _, hxy, hsx, hsy⟩ := two_survivors _ hW
  have hone : ∀ z, survives ((Finset.range limit).filter (fun q => q.Prime ∧ 5 ≤ q)) z →
      z = 1 := by
    intro z hz
    unfold survives at hz
    obtain ⟨h2, h3, hWz⟩ := hz
    by_contra hz1
    have hp := Nat.minFac_prime hz1
    have hpd := Nat.minFac_dvd z
    have hplt := hcon _ hp
    by_cases hp2 : z.minFac = 2
    · rw [hp2] at hpd
      exact h2 hpd
    by_cases hp3 : z.minFac = 3
    · rw [hp3] at hpd
      exact h3 hpd
    have hp4 : z.minFac ≠ 4 := fun h => by
      rw [h] at hp
      norm_num at hp
    have h5 : 5 ≤ z.minFac := by
      have := hp.two_le
      omega
    exact hWz _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hplt, hp, h5⟩) hpd
  exact hxy ((hone x hsx).trans (hone y hsy).symm)

end RNS.PigeonholeWheel

#print axioms RNS.PigeonholeWheel.one_closed_copy_holds
#print axioms RNS.PigeonholeWheel.open_copies_holds
#print axioms RNS.PigeonholeWheel.two_survivors_persist_holds
#print axioms RNS.PigeonholeWheel.pigeonhole_primes_unbounded_holds
