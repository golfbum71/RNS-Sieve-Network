/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.CRT.Conclusions
import RNSNetwork.Nodes.BlockingRuns.Conclusions

/-!
# Proofs for BlockingRuns

Imports claims only, never other nodes' proofs. `blocked_run_is_shift` is
proved as a step from `CRT`'s `crt_map_bijective`, taken as a named
hypothesis; `longest_blocked_run_eq_max_gap_sub_one` is proved as a step from
`blocked_run_is_shift`. `RNSSolutions/Assemble.lean` joins them up.
-/

namespace RNS.BlockingRuns

open RNS.CRT

/-- The cycle length is not zero. -/
private theorem primorial_ne_zero (limit : Nat) : primorial_modulus limit ≠ 0 := by
  unfold primorial_modulus
  exact Finset.prod_ne_zero_iff.mpr fun q hq => (Finset.mem_filter.mp hq).2.ne_zero

/-- Every active wheel divides the cycle length. -/
private theorem dvd_primorial {limit q : Nat} (hq : q ∈ active_primes limit) :
    q ∣ primorial_modulus limit :=
  Finset.dvd_prod_of_mem id hq

/-- 1 survives every wheel. -/
private theorem one_survives (limit : Nat) : ∀ q ∈ active_primes limit, ¬ q ∣ 1 := by
  intro q hq h
  have := (Finset.mem_filter.mp hq).2.one_lt
  have := Nat.le_of_dvd Nat.one_pos h
  omega

/-- Adding multiples of the cycle length keeps a survivor a survivor. -/
private theorem survives_add (limit n k : Nat) (h : ∀ q ∈ active_primes limit, ¬ q ∣ n) :
    ∀ q ∈ active_primes limit, ¬ q ∣ n + primorial_modulus limit * k := by
  intro q hq hd
  exact h q hq ((Nat.dvd_add_left (Dvd.dvd.mul_right (dvd_primorial hq) k)).mp hd)

/-- **Every setting of the wheels is a shift of the ordinary sieve**, as a step
from the Chinese Remainder Theorem. -/
theorem blocked_run_is_shift_step (hC : crt_map_bijective) : blocked_run_is_shift := by
  intro limit s L b hrun
  have hP := primorial_ne_zero limit
  have : NeZero (primorial_modulus limit) := ⟨hP⟩
  obtain ⟨x, hx⟩ := (hC limit).2 (fun q => - b q)
  have hc : ∀ q : active_primes limit, ((x.val : Nat) : ZMod (q : Nat)) = - b q := by
    intro q
    have h := congrFun hx q
    simp only [crt_map, ZMod.castHom_apply, ZMod.cast_eq_val] at h
    exact h
  refine ⟨s + x.val + primorial_modulus limit, by have := Nat.pos_of_ne_zero hP; omega,
    fun i hi => ?_⟩
  obtain ⟨q, hq⟩ := hrun i hi
  refine ⟨q, q.2, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  have hPq : ((primorial_modulus limit : Nat) : ZMod (q : Nat)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_primorial q.2)
  have e : s + x.val + primorial_modulus limit + i = (s + i) + x.val + primorial_modulus limit := by
    omega
  rw [e, Nat.cast_add, Nat.cast_add, hq, hc q, hPq, add_neg_cancel, add_zero]

/-- **The longest blocked run is one less than the largest survivor gap**, as a
step from `blocked_run_is_shift`. -/
theorem longest_blocked_run_eq_max_gap_sub_one_step (hS : blocked_run_is_shift) :
    longest_blocked_run_eq_max_gap_sub_one := by
  classical
  intro limit L
  have hP := Nat.pos_of_ne_zero (primorial_ne_zero limit)
  constructor
  · rintro ⟨b, s, hrun⟩
    obtain ⟨s', hs'1, hrun'⟩ := hS limit s L b hrun
    by_cases hL : L = 0
    · -- no run to place: take 1 and the next survivor after it
      subst hL
      have hex : ∃ m, 1 < m ∧ ∀ q ∈ active_primes limit, ¬ q ∣ m :=
        ⟨1 + primorial_modulus limit * 1, by omega, survives_add limit 1 1 (one_survives limit)⟩
      refine ⟨1, Nat.find hex, one_survives limit, (Nat.find_spec hex).2, (Nat.find_spec hex).1,
        fun m hm1 hm2 => ?_, by have := (Nat.find_spec hex).1; omega⟩
      by_contra hno
      push Not at hno
      exact absurd (Nat.find_min' hex ⟨hm1, hno⟩) (by omega)
    · -- the run sits between the last survivor before it and the first after it
      have hblk0 := hrun' 0 (by omega)
      have hs'2 : 2 ≤ s' := by
        by_contra h
        have h1 : s' = 1 := by omega
        obtain ⟨q, hq, hd⟩ := hblk0
        rw [h1] at hd
        exact one_survives limit q hq (by simpa using hd)
      let P := fun n => ∀ q ∈ active_primes limit, ¬ q ∣ n
      have hex : ∃ m, s' + L ≤ m ∧ P m := by
        refine ⟨1 + primorial_modulus limit * (s' + L), ?_, survives_add limit 1 _ (one_survives limit)⟩
        have : s' + L ≤ primorial_modulus limit * (s' + L) := Nat.le_mul_of_pos_left _ hP
        omega
      have ha : P (Nat.findGreatest P (s' - 1)) :=
        Nat.findGreatest_spec (m := 1) (by omega) (one_survives limit)
      have hale : Nat.findGreatest P (s' - 1) ≤ s' - 1 := Nat.findGreatest_le _
      refine ⟨Nat.findGreatest P (s' - 1), Nat.find hex, ha, (Nat.find_spec hex).2,
        by have := (Nat.find_spec hex).1; omega, fun m hm1 hm2 => ?_,
        by have := (Nat.find_spec hex).1; omega⟩
      by_contra hno
      push Not at hno
      by_cases h1 : m ≤ s' - 1
      · exact Nat.findGreatest_is_greatest hm1 h1 hno
      · by_cases h2 : m < s' + L
        · obtain ⟨q, hq, hd⟩ := hrun' (m - s') (by omega)
          have e : s' + (m - s') = m := by omega
          rw [e] at hd
          exact hno q hq hd
        · exact absurd (Nat.find_min' hex ⟨by omega, hno⟩) (by omega)
  · rintro ⟨a, c, _, _, hac, hbetween, hlen⟩
    refine ⟨fun _ => 0, a + 1, fun i hi => ?_⟩
    obtain ⟨q, hq, hd⟩ := hbetween (a + 1 + i) (by omega) (by omega)
    exact ⟨⟨q, hq⟩, (ZMod.natCast_eq_zero_iff _ _).mpr hd⟩

end RNS.BlockingRuns
