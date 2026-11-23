/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.ResidueReduction.Conclusions
import Mathlib.Tactic

/-!
# Proofs for ResidueReduction

Built clean by `lake build RNSSolutions` on 2026-11-23; `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`.

Suppose a counterexample has no speed divisible by the wheel. Its remainders
for the modulus are none of them multiples of the wheel (the wheel divides the
modulus). Leaving out one speed, any common factor of the rest and the modulus
divides those speeds; if it also divided the left-out speed it would divide
all, so it is 1; otherwise `TeamShift` (with the conjecture for one runner
fewer) makes the whole set lonely. So the remainders pass the check's
conditions, the check gives a time, and since only remainders matter
(`far_mod`), that time is lonely for the speeds themselves.
-/

namespace RNS.ResidueReduction

open RNS.PileUpLock

theorem far_congr (n m : ℕ) (y y' : ℤ) (h : y % (m : ℤ) = y' % (m : ℤ)) :
    far n m y ↔ far n m y' := by
  unfold far
  rw [h]

theorem far_mod_holds : far_mod := by
  intro n m y
  exact far_congr n m _ _ (Int.emod_emod y m)

/-- A number is its remainder plus a multiple of the modulus, so anything
dividing the modulus and the remainder divides the number. -/
theorem dvd_of_dvd_emod {d y m : ℤ} (hm : d ∣ m) (hr : d ∣ y % m) : d ∣ y := by
  have h := Int.emod_add_ediv_mul y m
  rw [← h]
  exact dvd_add hr (dvd_mul_of_dvd_right hm _)

theorem residue_check_forces_divisor_step (hTS : RNS.TeamShift.team_shift) :
    residue_check_forces_divisor := by
  intro k p hk hp hLR hcheck S hcard h0 hgcd hS
  by_contra hnone
  have hnd : ∀ v ∈ S, ¬ (p : ℤ) ∣ v := fun v hv h => hnone ⟨v, hv, h⟩
  set Mn : ℕ := (k + 1) * p with hMn
  have hMpos : 0 < Mn := Nat.mul_pos (by omega) hp
  have hM : (0 : ℤ) < (Mn : ℤ) := by exact_mod_cast hMpos
  have hpM : (p : ℤ) ∣ (Mn : ℤ) := ⟨(k + 1 : ℕ), by rw [hMn]; push_cast; ring⟩
  set f : ℤ → ℤ := fun v => v % (Mn : ℤ) with hf
  set R : Multiset ℤ := S.val.map f with hR
  have hRcard : Multiset.card R = k := by
    rw [hR, Multiset.card_map]
    exact hcard
  -- the remainders meet the size and wheel conditions
  have hRent : ∀ r ∈ R, 0 ≤ r ∧ r < (Mn : ℤ) ∧ ¬ (p : ℤ) ∣ r := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hr
    refine ⟨Int.emod_nonneg v (ne_of_gt hM), Int.emod_lt_of_pos v hM, ?_⟩
    intro hpr
    exact hnd v (Finset.mem_val.mp hv) (dvd_of_dvd_emod hpM (show (p : ℤ) ∣ v % (Mn : ℤ) from hpr))
  -- leaving out one speed, the rest share no factor with the modulus
  have hRgcd : ∀ r ∈ R, Int.gcd (R.erase r).gcd (Mn : ℤ) = 1 := by
    intro r hr
    obtain ⟨u, hu', rfl⟩ := Multiset.mem_map.mp hr
    have hu : u ∈ S := Finset.mem_val.mp hu'
    have herase : R.erase (f u) = (S.erase u).val.map f := by
      rw [hR, Finset.erase_val, Multiset.map_erase_of_mem f S.val hu']
    set q : ℤ := (Int.gcd (R.erase (f u)).gcd (Mn : ℤ) : ℤ) with hq
    have hqA : q ∣ (R.erase (f u)).gcd := Int.gcd_dvd_left _ _
    have hqM : q ∣ (Mn : ℤ) := Int.gcd_dvd_right _ _
    have hqT : ∀ v ∈ S.erase u, q ∣ v := by
      intro v hv
      have hmem : f v ∈ R.erase (f u) := by
        rw [herase]
        exact Multiset.mem_map_of_mem f (Finset.mem_val.mpr hv)
      exact dvd_of_dvd_emod hqM (show q ∣ v % (Mn : ℤ) from dvd_trans hqA (Multiset.gcd_dvd hmem))
    by_cases hqu : q ∣ u
    · have hall : ∀ v ∈ S, q ∣ id v := by
        intro v hv
        by_cases hvu : v = u
        · rw [hvu]; exact hqu
        · exact hqT v (Finset.mem_erase.mpr ⟨hvu, hv⟩)
      have h1 : q ∣ 1 := by
        rw [← hgcd]
        exact Finset.dvd_gcd hall
      have hq1 : q = 1 := Int.eq_one_of_dvd_one (by rw [hq]; positivity) h1
      rw [hq] at hq1
      exact_mod_cast hq1
    · exfalso
      apply hS
      have hTcard : (S.erase u).card = k - 1 := by
        rw [Finset.card_erase_of_mem hu, hcard]
      have hT0 : 0 ∉ S.erase u := fun h => h0 (Finset.mem_of_mem_erase h)
      have hTlonely : has_lonely_time (S.erase u) := hLR (S.erase u) hT0 (by omega)
      have := hTS (S.erase u) u q (by omega) (Finset.notMem_erase u S) hqT hqu hTlonely
      rwa [Finset.insert_erase hu] at this
  -- the check gives a time, and only remainders matter
  obtain ⟨t, ht⟩ := hcheck R hRcard hRent hRgcd
  apply hS
  refine ⟨Mn, t, hMpos, fun v hv => ?_⟩
  have hfar := ht (f v) (Multiset.mem_map_of_mem f (Finset.mem_val.mpr hv))
  rw [hcard]
  have hy : (f v * t) % (Mn : ℤ) = (v * t) % (Mn : ℤ) := by
    show (v % (Mn : ℤ) * t) % (Mn : ℤ) = (v * t) % (Mn : ℤ)
    rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  exact (far_congr (k + 1) Mn _ _ hy).mp hfar

end RNS.ResidueReduction

#print axioms RNS.ResidueReduction.far_mod_holds
#print axioms RNS.ResidueReduction.residue_check_forces_divisor_step
