/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.ModulusLift.Conclusions
import Mathlib.Tactic

/-!
# Proofs for ModulusLift

Draft (2026-11-23).

The remainder of `c * y` for `c * d` is `c` times the remainder of `y` for `d`,
so both distances from the start scale by `c`. A good time `t / d` is the time
`(t * e) / (d * e)`. Remainders: `(r % d) * t` and `r * t` leave the same
remainder for `d`. A common factor of a number and `d` divides every multiple of
`d`, hence divides the number's greatest common factor with that multiple.
-/

namespace RNS.ModulusLift

open RNS.PileUpLock

theorem far_scale_holds : far_scale := by
  intro n d c y hc
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  unfold far
  have hmod : ((c : ℤ) * y) % ((c * d : ℕ) : ℤ) = (c : ℤ) * (y % (d : ℤ)) := by
    push_cast
    exact Int.mul_emod_mul_of_pos _ _ hc'
  rw [hmod]
  push_cast
  set r := y % (d : ℤ)
  have e1 : (n : ℤ) * ((c : ℤ) * r) = (c : ℤ) * ((n : ℤ) * r) := by ring
  have e2 : (n : ℤ) * ((c : ℤ) * (d : ℤ) - (c : ℤ) * r) = (c : ℤ) * ((n : ℤ) * ((d : ℤ) - r)) := by
    ring
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_of_mul_le_mul_left h1 hc', le_of_mul_le_mul_left h2 hc'⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_le_mul_of_nonneg_left h1 hc'.le, mul_le_mul_of_nonneg_left h2 hc'.le⟩

theorem good_lifts_step (h : far_scale) : good_lifts := by
  intro n d d' R hd' hdd ⟨t, ht⟩
  obtain ⟨e, rfl⟩ := hdd
  have he : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hd')
  refine ⟨t * e, fun r hr => ?_⟩
  have key := (h n d e (r * t) he).mpr (ht r hr)
  rw [show d * e = e * d by ring]
  rw [show r * (t * (e : ℤ)) = (e : ℤ) * (r * t) by ring]
  exact key

theorem good_lifts_holds : good_lifts := good_lifts_step far_scale_holds

theorem good_residues_holds : good_residues := by
  intro n d R
  have key : ∀ (r t : ℤ), far n d ((r % (d : ℤ)) * t) ↔ far n d (r * t) := by
    intro r t
    have hy : ((r % (d : ℤ)) * t) % (d : ℤ) = (r * t) % (d : ℤ) := by
      rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
    unfold far
    rw [hy]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun r hr => (key r t).mp (ht _ (Multiset.mem_map_of_mem _ hr))⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, fun r hr => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hr
    exact (key a t).mpr (ht a ha)

theorem bad_lists_lift_step (hL : good_lifts) (hR : good_residues) : bad_lists_lift := by
  intro n d d' R hd' hdd hgood
  rw [hR n d R] at hgood
  rw [hR n d' R]
  exact hL n d d' R hd' hdd hgood

theorem bad_lists_lift_holds : bad_lists_lift :=
  bad_lists_lift_step good_lifts_holds good_residues_holds

theorem proper_lifts_holds : proper_lifts := by
  intro A d d' hdd hne hone
  apply hne
  have h1 : ((Int.gcd A d : ℕ) : ℤ) ∣ A := Int.gcd_dvd_left A d
  have h2 : ((Int.gcd A d : ℕ) : ℤ) ∣ (d' : ℤ) :=
    dvd_trans (Int.gcd_dvd_right A d) (Int.natCast_dvd_natCast.mpr hdd)
  have h3 : Int.gcd A d ∣ Int.gcd A d' := Int.dvd_gcd h1 h2
  rw [hone] at h3
  exact Nat.dvd_one.mp h3

end RNS.ModulusLift

#print axioms RNS.ModulusLift.far_scale_holds
#print axioms RNS.ModulusLift.good_lifts_holds
#print axioms RNS.ModulusLift.good_residues_holds
#print axioms RNS.ModulusLift.bad_lists_lift_holds
#print axioms RNS.ModulusLift.proper_lifts_holds
