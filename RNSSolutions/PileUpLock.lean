/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PileUpLock.Conclusions
import Mathlib.Tactic

/-!
# Proofs for PileUpLock

Draft (2026-11-23).

* Pack together: each pack speed times `k` is a multiple of `m` exactly when the
  greatest common factor of those products is; that factor is the greatest
  common factor of the speeds times `k` (`Finset.gcd_mul_right'`).
* Locked: the target's speed times `k` is then a multiple of `m` too.
* Freed: with the greatest common factor `g` of the pack written as `d * e`,
  where `d` is the greatest common factor of `g` and the target speed `u`, the
  target's spots at the times `k / |g|` are the multiples of `d`, and Bézout's
  identity reaches any of them. Taking `e / 2` of them lands the target between
  a third and two thirds of a lap. If every pack speed is 0 the pack never moves,
  and the time `u / (2 u²)` puts the target at half a lap.
-/

namespace RNS.PileUpLock

theorem pack_together_iff_holds : pack_together_iff := by
  intro ι P sp m k
  constructor
  · intro h
    have h1 : (m : ℤ) ∣ P.gcd (fun i => sp i * k) := Finset.dvd_gcd h
    exact dvd_trans h1 (Finset.gcd_mul_right' P sp k).dvd
  · intro h i hi
    exact dvd_trans h (mul_dvd_mul_right (Finset.gcd_dvd (f := sp) hi) k)

theorem locked_never_separated_holds : locked_never_separated := by
  intro ι P sp u m k _ hpack hgu
  have hg : (m : ℤ) ∣ P.gcd sp * k := (pack_together_iff_holds ι P sp m k).mp hpack
  exact Int.emod_eq_zero_of_dvd (dvd_trans hg (mul_dvd_mul_right hgu k))

theorem pile_up_frees_iff_holds : pile_up_frees_iff := by
  intro ι P sp u
  constructor
  · rintro ⟨m, k, hm, hpack, hfar⟩ hgu
    have h0 := locked_never_separated_holds ι P sp u m k hm hpack hgu
    have h1 := hfar.1
    rw [h0] at h1
    have : (0 : ℤ) < m := by exact_mod_cast hm
    linarith
  · intro hgu
    by_cases hg0 : P.gcd sp = 0
    · -- every pack speed is 0: the pack stays at the start
      have hu : u ≠ 0 := by
        rintro rfl
        exact hgu (dvd_zero _)
      have hall : ∀ i ∈ P, sp i = 0 := Finset.gcd_eq_zero_iff.mp hg0
      have hpos : 0 < u.natAbs := Int.natAbs_pos.mpr hu
      refine ⟨u.natAbs * u.natAbs * 2, u, Nat.mul_pos (Nat.mul_pos hpos hpos) (by norm_num), ?_, ?_⟩
      · intro i hi
        rw [hall i hi, zero_mul]
        exact dvd_zero _
      · have hc : ((u.natAbs * u.natAbs * 2 : ℕ) : ℤ) = u * u * 2 := by
          push_cast
          rw [abs_mul_abs_self]
        have huu : 0 < u * u := mul_self_pos.mpr hu
        have hmod : (u * u) % (u * u * 2) = u * u :=
          Int.emod_eq_of_lt (le_of_lt huu) (by linarith)
        unfold far
        rw [hc, hmod]
        constructor <;> push_cast <;> linarith
    · -- the pack's greatest common factor g is not 0
      set g := P.gcd sp with hgdef
      set D : ℤ := (Int.gcd u g : ℤ) with hD
      have hDu : D ∣ u := Int.gcd_dvd_left u g
      have hDg : D ∣ g := Int.gcd_dvd_right u g
      obtain ⟨e, he⟩ := hDg
      have hD0 : D ≠ 0 := by
        rintro h
        rw [h, zero_mul] at he
        exact hg0 he
      have hDnn : 0 ≤ D := by rw [hD]; positivity
      have hDpos : 0 < D := lt_of_le_of_ne hDnn (Ne.symm hD0)
      have he0 : e ≠ 0 := by
        rintro rfl
        rw [mul_zero] at he
        exact hg0 he
      set E : ℤ := |e| with hE
      have hE1 : 1 ≤ E := by
        have : 0 < |e| := abs_pos.mpr he0
        rw [hE]; omega
      have hE2 : 2 ≤ E := by
        by_contra hlt
        have hE_eq : |e| = 1 := by rw [← hE]; omega
        apply hgu
        rcases (abs_eq zero_le_one).mp hE_eq with h | h
        · rw [he, h, mul_one]; exact hDu
        · rw [he, h, mul_neg_one]; exact (neg_dvd).mpr hDu
      have habs : |g| = D * E := by
        rw [he, abs_mul, abs_of_nonneg hDnn]
      set c : ℤ := E / 2 with hc
      have hc0 : 1 ≤ c := by omega
      have hc1 : E ≤ 3 * c := by omega
      have hc2 : E ≤ 3 * (E - c) := by omega
      have hcE : c < E := by omega
      -- the time numerator, from Bézout's identity
      have hbez : D = u * Int.gcdA u g + g * Int.gcdB u g := Int.gcd_eq_gcd_ab u g
      obtain ⟨σ, hσ⟩ := abs_dvd_self g
      refine ⟨g.natAbs, Int.gcdA u g * c, Int.natAbs_pos.mpr hg0, ?_, ?_⟩
      · intro i hi
        rw [Int.natCast_natAbs]
        exact dvd_mul_of_dvd_left ((abs_dvd g (sp i)).mpr (Finset.gcd_dvd (f := sp) hi)) _
      · have hm : ((g.natAbs : ℕ) : ℤ) = D * E := by rw [Int.natCast_natAbs, habs]
        have hsplit : u * (Int.gcdA u g * c) = c * D + (D * E) * (-(σ * Int.gcdB u g * c)) := by
          rw [← habs]
          have : g = |g| * σ := hσ
          calc u * (Int.gcdA u g * c)
              = c * (u * Int.gcdA u g + g * Int.gcdB u g) - c * g * Int.gcdB u g := by ring
            _ = c * D - c * (|g| * σ) * Int.gcdB u g := by rw [← hbez, ← this]
            _ = c * D + |g| * (-(σ * Int.gcdB u g * c)) := by ring
        have hcD : 0 ≤ c * D := mul_nonneg (by omega) hDnn
        have hcDlt : c * D < D * E := by nlinarith
        have hmod : (u * (Int.gcdA u g * c)) % (D * E) = c * D := by
          rw [hsplit, Int.add_mul_emod_self_left]
          exact Int.emod_eq_of_lt hcD hcDlt
        unfold far
        rw [hm, hmod]
        constructor
        · push_cast; nlinarith
        · push_cast; nlinarith

theorem shared_point_pile_up_step (h : pile_up_frees_iff) : shared_point_pile_up := by
  intro ι P sp a u
  exact h ι P (fun i => sp i - a) (u - a)

theorem shared_point_pile_up_holds : shared_point_pile_up :=
  shared_point_pile_up_step pile_up_frees_iff_holds

end RNS.PileUpLock

#print axioms RNS.PileUpLock.pack_together_iff_holds
#print axioms RNS.PileUpLock.locked_never_separated_holds
#print axioms RNS.PileUpLock.pile_up_frees_iff_holds
#print axioms RNS.PileUpLock.shared_point_pile_up_holds
