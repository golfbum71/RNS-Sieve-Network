/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Data.Nat.Squarefree       -- `Nat.sq_mul_squarefree`
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push               -- `push Not`
import RNSNetwork.Nodes.Infinitude.Conclusions

/-!
# Proofs for Infinitude

Rests on no other node. Tactic proofs are copied from `rns_sieve_6.lean`.

One adaptation: `rns_sieve_6.lean` (v5.1) switched to `exists_sq_mul_squarefree`,
whose witnesses come in the order (square part, square-free part). At the
Mathlib version pinned here that name does not exist, and
`Nat.sq_mul_squarefree` gives them in the order (square-free part, square
part). So `aOf`/`bOf` are extracted as in the source's earlier v4 file; their
meanings (square-free part, square part) are the same.
-/

namespace RNS.Infinitude

private theorem mem_active_primes_is_prime (limit : Nat) (q : Nat)
    (hq : q ∈ active_primes limit) : q.Prime := by
  unfold active_primes at hq
  exact (Finset.mem_filter.mp hq).2

private theorem primorial_modulus_pos (limit : Nat) : 0 < primorial_modulus limit := by
  unfold primorial_modulus
  apply Finset.prod_pos
  intro q hq
  exact (mem_active_primes_is_prime limit q hq).pos

private theorem active_prime_dvd_primorial_modulus (limit : Nat) (q : Nat)
    (hq : q ∈ active_primes limit) : q ∣ primorial_modulus limit := by
  unfold primorial_modulus
  exact Finset.dvd_prod_of_mem id hq

theorem euclid_primes_unbounded_holds : euclid_primes_unbounded := by
  unfold euclid_primes_unbounded
  intro limit
  set N := primorial_modulus limit + 1 with hNdef
  have hN2 : 2 ≤ N := by
    have := primorial_modulus_pos limit
    omega
  have hN1 : N ≠ 1 := by omega
  set p := N.minFac with hpdef
  have hp_prime : p.Prime := Nat.minFac_prime hN1
  have hp_dvd_N : p ∣ N := Nat.minFac_dvd N
  refine ⟨p, hp_prime, ?_⟩
  by_contra hlt
  push Not at hlt
  have hp_mem : p ∈ active_primes limit := by
    unfold active_primes
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, hp_prime⟩
  have hp_dvd_primorial : p ∣ primorial_modulus limit :=
    active_prime_dvd_primorial_modulus limit p hp_mem
  have hp_dvd_one : p ∣ 1 := by
    have hiff := Nat.dvd_add_right hp_dvd_primorial (c := 1)
    have hp_dvd_N' : p ∣ primorial_modulus limit + 1 := hNdef ▸ hp_dvd_N
    exact hiff.mp hp_dvd_N'
  have hp1 : p = 1 := Nat.dvd_one.mp hp_dvd_one
  exact hp_prime.one_lt.ne' hp1

private theorem wheel_supply_aux (limit : Nat) (hbound : ∀ p, p.Prime → p < limit) :
    False := by
  set M := primorial_modulus limit with hMdef
  have hMpos : 0 < M := primorial_modulus_pos limit
  set X := (M + 2) ^ 2 with hXdef
  have hdecomp : ∀ n : Nat, ∃ a b, b ^ 2 * a = n ∧ Squarefree a :=
    fun n => Nat.sq_mul_squarefree n
  set aOf : Nat → Nat := fun n => (hdecomp n).choose with haOfdef
  set bOf : Nat → Nat := fun n => (hdecomp n).choose_spec.choose with hbOfdef
  have hspec : ∀ n, (bOf n) ^ 2 * (aOf n) = n ∧ Squarefree (aOf n) :=
    fun n => (hdecomp n).choose_spec.choose_spec
  have ha_le : ∀ n ∈ Finset.Icc 1 X, aOf n ≤ M := by
    intro n hn
    obtain ⟨heq, hsf⟩ := hspec n
    have ha_pf_sub : (aOf n).primeFactors ⊆ active_primes limit := by
      intro q hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqlt : q < limit := hbound q hqp
      unfold active_primes
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hqlt, hqp⟩
    have ha_eq : ∏ q ∈ (aOf n).primeFactors, q = aOf n := by
      have h := Nat.prod_primeFactors_sdiff_of_squarefree hsf
        (Finset.empty_subset (aOf n).primeFactors)
      simpa using h
    have ha_dvd : aOf n ∣ M := by
      rw [hMdef]
      unfold primorial_modulus
      rw [← ha_eq]
      exact Finset.prod_dvd_prod_of_subset (aOf n).primeFactors (active_primes limit) id
        ha_pf_sub
    exact Nat.le_of_dvd hMpos ha_dvd
  have hb_le : ∀ n ∈ Finset.Icc 1 X, bOf n ≤ M + 2 := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    obtain ⟨heq, hsf⟩ := hspec n
    by_contra hblt
    push Not at hblt
    have hb2 : (M + 2) ^ 2 < (bOf n) ^ 2 := Nat.pow_lt_pow_left hblt (by norm_num)
    have han0 : aOf n ≠ 0 := by
      intro ha0
      rw [ha0, Nat.mul_zero] at heq
      omega
    have hanpos : 1 ≤ aOf n := Nat.one_le_iff_ne_zero.mpr han0
    have hcalc : (bOf n) ^ 2 ≤ (bOf n) ^ 2 * aOf n := by
      calc (bOf n) ^ 2 = (bOf n) ^ 2 * 1 := by ring
        _ ≤ (bOf n) ^ 2 * aOf n := Nat.mul_le_mul_left _ hanpos
    rw [heq] at hcalc
    have hnX : n ≤ X := hn.2
    rw [hXdef] at hnX
    omega
  have hinj : Set.InjOn (fun n => (bOf n, aOf n)) (Finset.Icc 1 X) := by
    intro n1 _ n2 _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨heqb, heqa⟩ := heq
    have h1 := (hspec n1).1
    have h2 := (hspec n2).1
    rw [heqb, heqa] at h1
    omega
  have hmaps : ∀ n ∈ Finset.Icc 1 X,
      (bOf n, aOf n) ∈ (Finset.range (M + 3)) ×ˢ (Finset.range (M + 1)) := by
    intro n hn
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by have := hb_le n hn; omega, by have := ha_le n hn; omega⟩
  have hcard_le := Finset.card_le_card_of_injOn (fun n => (bOf n, aOf n)) hmaps hinj
  rw [Finset.card_product, Finset.card_range, Finset.card_range] at hcard_le
  have hIcc_card : (Finset.Icc 1 X).card = X := by
    rw [Nat.card_Icc]
    have hXpos : 0 < X := by rw [hXdef]; positivity
    omega
  rw [hIcc_card, hXdef] at hcard_le
  nlinarith [hcard_le]

theorem squarefree_counting_no_finite_supply_holds : squarefree_counting_no_finite_supply := by
  unfold squarefree_counting_no_finite_supply
  exact wheel_supply_aux

end RNS.Infinitude

#print axioms RNS.Infinitude.euclid_primes_unbounded_holds
#print axioms RNS.Infinitude.squarefree_counting_no_finite_supply_holds
