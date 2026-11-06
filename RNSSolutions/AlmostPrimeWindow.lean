/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.AlmostPrimeWindow.Conclusions
import Mathlib.Data.Nat.Prime.Basic               -- `Nat.not_prime_mul`

/-!
# Proofs for AlmostPrimeWindow

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. Every prime factor of a number no wheel divides is at least the cutoff.
If such a number is composite, write it as its smallest prime factor times a
cofactor. The cofactor is at least the cutoff; if it were composite it would
be at least the cutoff squared, and the number at least the cutoff cubed. So
the cofactor is prime. Conversely a product of two primes each at least the
cutoff is composite and has no wheel factor.
-/

namespace RNS.AlmostPrimeWindow

/-- Every prime factor of a wheel-free number is at least the cutoff. -/
private theorem factor_ge {cutoff n : Nat} (hfree : wheel_free cutoff n) {q : Nat}
    (hq : q.Prime) (hqn : q ∣ n) : cutoff ≤ q := by
  by_contra h
  apply hfree q _ hqn
  unfold active_primes
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩

/-- A composite wheel-free number below the cube is a product of two primes,
each at least the cutoff. -/
private theorem composite_split {cutoff n : Nat} (hc : 2 ≤ cutoff) (hn : cutoff ≤ n)
    (hcube : n < cutoff * cutoff * cutoff) (hfree : wheel_free cutoff n) (hnp : ¬ n.Prime) :
    ∃ p r : Nat, p.Prime ∧ r.Prime ∧ cutoff ≤ p ∧ cutoff ≤ r ∧ n = p * r := by
  have hpP : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hpL : cutoff ≤ n.minFac := factor_ge hfree hpP (Nat.minFac_dvd n)
  obtain ⟨r, hr⟩ := Nat.minFac_dvd n
  generalize n.minFac = p at hr hpP hpL
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hnp (by rw [hr, mul_one]; exact hpP)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    omega
  have hrn : r ∣ n := ⟨p, by rw [hr, Nat.mul_comm]⟩
  have hrp : r.Prime := by
    by_contra hrp
    have hdm : r.minFac ∣ n := (Nat.minFac_dvd r).trans hrn
    have hL2 : cutoff ≤ r.minFac := factor_ge hfree (Nat.minFac_prime hr1) hdm
    have hsq : r.minFac ^ 2 ≤ r := Nat.minFac_sq_le_self (by omega) hrp
    rw [pow_two] at hsq
    have hLLr : cutoff * cutoff ≤ r := le_trans (Nat.mul_le_mul hL2 hL2) hsq
    have hbig : cutoff * cutoff * cutoff ≤ n := by
      rw [hr, Nat.mul_comm (cutoff * cutoff) cutoff]
      exact Nat.mul_le_mul hpL hLLr
    omega
  exact ⟨p, r, hpP, hrp, hpL, factor_ge hfree hrp hrn, hr⟩

theorem window_almost_prime_holds : window_almost_prime := by
  intro cutoff n hc hn hcube hfree
  by_cases hnp : n.Prime
  · exact Or.inl hnp
  · obtain ⟨p, r, hp, hr, _, _, rfl⟩ := composite_split hc hn hcube hfree hnp
    exact Or.inr (Nat.Prime.mul_isAlmostPrime_two hp hr)

theorem window_composite_iff_holds : window_composite_iff := by
  intro cutoff n hc hn hcube
  constructor
  · rintro ⟨hfree, hnp⟩
    exact composite_split hc hn hcube hfree hnp
  · rintro ⟨p, r, hp, hr, hpc, hrc, rfl⟩
    refine ⟨?_, Nat.not_prime_mul hp.one_lt.ne' hr.one_lt.ne'⟩
    intro q hq hqd
    unfold active_primes at hq
    rcases Finset.mem_filter.mp hq with ⟨hqr, hqp⟩
    have hqlt : q < cutoff := Finset.mem_range.mp hqr
    rcases (Nat.Prime.dvd_mul hqp).mp hqd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hqp hp).mp h
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hqp hr).mp h
      omega

theorem window_prime_iff_odd_factors_holds : window_prime_iff_odd_factors := by
  intro cutoff n hc hn hcube hfree
  constructor
  · intro hp
    rw [ArithmeticFunction.cardFactors_apply_prime hp]
    exact odd_one
  · intro hodd
    rcases window_almost_prime_holds cutoff n hc hn hcube hfree with hp | hs
    · exact hp
    · exfalso
      have h2 : ArithmeticFunction.cardFactors n = 2 := hs.2
      rw [h2] at hodd
      have := Nat.odd_iff.mp hodd
      omega

end RNS.AlmostPrimeWindow

#print axioms RNS.AlmostPrimeWindow.window_almost_prime_holds
#print axioms RNS.AlmostPrimeWindow.window_composite_iff_holds
#print axioms RNS.AlmostPrimeWindow.window_prime_iff_odd_factors_holds
