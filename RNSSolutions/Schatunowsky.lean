/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.Schatunowsky.Conclusions
import RNSNetwork.Nodes.BonseCeiling.Conclusions
import Mathlib.Algebra.BigOperators.Associated   -- `Finset.prod_primes_dvd`
import Mathlib.Data.Nat.Prime.Basic             -- `Nat.not_prime_mul`
import Mathlib.Data.Nat.Prime.Infinite          -- `Nat.exists_infinite_primes`
import Mathlib.Tactic.NormNum.Prime             -- `norm_num` deciding small numbers prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Proofs for Schatunowsky

Imports claims only, never other nodes' proofs. The bound rests on
`BonseCeiling.ceiling_inside_cycle`, taken as a named hypothesis.

Drafted 2026-11-05; awaiting its first `lake build RNSSolutions`.

Idea for the bound. Suppose every survivor of `N` is prime and `N` exceeds 30.
Let `q` be the smallest prime whose square reaches `N`. Every prime below `q`
has its square below `N`, so it divides `N` (the ceiling argument), and so
does their product, the cycle of the wheels below `q`. Hence that cycle is at
most `N`, which is at most `q` squared. If `q` is 11 or more, Bonse's
inequality says `q` squared is below that cycle: impossible. Otherwise `q` is
at most 7, so `N` is at most 49; the wheels 2, 3, 5 have squares below `N`, so
30 divides `N`, and no multiple of 30 lies strictly between 30 and 49.
-/

namespace RNS.Schatunowsky

theorem ceiling_forces_wheels_holds : ceiling_forces_wheels := by
  intro N p hN hp hpp
  by_contra hdvd
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd
  have hcop2 : Nat.gcd (p * p) N = 1 := Nat.coprime_mul_iff_left.mpr ⟨hcop, hcop⟩
  have h2 := hp.two_le
  have hprime := hN (p * p) (by nlinarith) hpp hcop2
  exact Nat.not_prime_mul (by omega) (by omega) hprime

theorem thirty_survivors_all_prime_holds : thirty_survivors_all_prime := by
  intro m h1 h2 hc
  interval_cases m <;> first | exact absurd hc (by decide) | norm_num

theorem schatunowsky_bound_step (h_bonse : RNS.BonseCeiling.ceiling_inside_cycle) :
    schatunowsky_bound := by
  classical
  intro N hN
  by_contra hgt
  have h30 : 30 < N := by omega
  have hex : ∃ q : Nat, q.Prime ∧ N ≤ q * q := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes N
    exact ⟨p, hp2, le_trans hp1 (Nat.le_mul_self p)⟩
  have hqspec := Nat.find_spec hex
  have hqmin : ∀ p : Nat, p < Nat.find hex → ¬ (p.Prime ∧ N ≤ p * p) :=
    fun p hp => Nat.find_min hex hp
  generalize Nat.find hex = q at hqspec hqmin
  obtain ⟨hqp, hNq⟩ := hqspec
  -- every wheel below `q` divides `N`
  have hdiv : ∀ p ∈ active_primes q, p ∣ N := by
    intro p hp
    simp only [active_primes, Finset.mem_filter, Finset.mem_range] at hp
    have hlt : p * p < N := by
      by_contra hc
      exact hqmin p hp.1 ⟨hp.2, by omega⟩
    exact ceiling_forces_wheels_holds N p hN hp.2 hlt
  have hprimes : ∀ p ∈ active_primes q, _root_.Prime p := by
    intro p hp
    simp only [active_primes, Finset.mem_filter] at hp
    exact hp.2.prime
  have hprod : primorial_modulus q ∣ N := by
    unfold primorial_modulus
    exact Finset.prod_primes_dvd N hprimes hdiv
  have hle : primorial_modulus q ≤ N := Nat.le_of_dvd (by omega) hprod
  by_cases hq11 : 11 ≤ q
  · have hb := h_bonse q hqp hq11
    rw [pow_two] at hb
    omega
  · have hq7 : q ≤ 7 := by
      by_contra h
      have hcases : q = 8 ∨ q = 9 ∨ q = 10 := by omega
      rcases hcases with rfl | rfl | rfl <;> norm_num at hqp
    have hqq : q * q ≤ 7 * 7 := Nat.mul_le_mul hq7 hq7
    have h2 := ceiling_forces_wheels_holds N 2 hN Nat.prime_two (by omega)
    have h3 := ceiling_forces_wheels_holds N 3 hN Nat.prime_three (by omega)
    have h5 := ceiling_forces_wheels_holds N 5 hN Nat.prime_five (by omega)
    omega

end RNS.Schatunowsky

#print axioms RNS.Schatunowsky.ceiling_forces_wheels_holds
#print axioms RNS.Schatunowsky.thirty_survivors_all_prime_holds
#print axioms RNS.Schatunowsky.schatunowsky_bound_step
