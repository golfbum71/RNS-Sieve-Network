/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP -- Dirichlet's theorem
import Mathlib.Tactic.NormNum.GCD               -- `norm_num` on coprimality
import RNSNetwork.Nodes.DirichletColumns.Conclusions

/-!
# Proofs for DirichletColumns

Rests on no other node; uses Mathlib's `Nat.infinite_setOfPred_prime_and_modEq`
and `Nat.forall_exists_prime_gt_and_modEq` at modulus 6. Tactic proofs are
copied from `rns_sieve_6.lean`, Part I, with the remainder-class lemmas
inlined.
-/

namespace RNS.DirichletColumns

private theorem minus_class_infinite : {p : ℕ | Nat.Prime p ∧ p ≡ 5 [MOD 6]}.Infinite :=
  Nat.infinite_setOfPred_prime_and_modEq (by norm_num) (by norm_num)

private theorem plus_class_infinite : {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD 6]}.Infinite :=
  Nat.infinite_setOfPred_prime_and_modEq (by norm_num) (by norm_num)

theorem col_minus_primes_infinite_holds : col_minus_primes_infinite := by
  unfold col_minus_primes_infinite
  by_contra hinf
  rw [Set.not_infinite] at hinf
  have hsub : {p : ℕ | Nat.Prime p ∧ p ≡ 5 [MOD 6]}
      ⊆ col_minus '' {n : ℕ | (col_minus n).Prime} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    obtain ⟨hprime, hmod⟩ := hp
    unfold Nat.ModEq at hmod
    have hcol : col_minus (p / 6) = p := by unfold col_minus; omega
    rw [Set.mem_image]
    refine ⟨p / 6, ?_, hcol⟩
    simp only [Set.mem_ofPred_eq]
    rw [hcol]
    exact hprime
  exact minus_class_infinite ((hinf.image col_minus).subset hsub)

theorem col_plus_primes_infinite_holds : col_plus_primes_infinite := by
  unfold col_plus_primes_infinite
  by_contra hinf
  rw [Set.not_infinite] at hinf
  have hsub : {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD 6]}
      ⊆ col_plus '' {n : ℕ | (col_plus n).Prime} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    obtain ⟨hprime, hmod⟩ := hp
    unfold Nat.ModEq at hmod
    have hcol : col_plus (p / 6) = p := by unfold col_plus; omega
    rw [Set.mem_image]
    refine ⟨p / 6, ?_, hcol⟩
    simp only [Set.mem_ofPred_eq]
    rw [hcol]
    exact hprime
  exact plus_class_infinite ((hinf.image col_plus).subset hsub)

theorem col_minus_primes_unbounded_holds : col_minus_primes_unbounded := by
  unfold col_minus_primes_unbounded
  intro N
  obtain ⟨p, hpN, hprime, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (6 * N + 5) (q := 6) (a := 5) (by norm_num) (by norm_num)
  unfold Nat.ModEq at hmod
  have hcol : col_minus (p / 6) = p := by unfold col_minus; omega
  refine ⟨p / 6, by omega, ?_⟩
  rw [hcol]
  exact hprime

theorem col_plus_primes_unbounded_holds : col_plus_primes_unbounded := by
  unfold col_plus_primes_unbounded
  intro N
  obtain ⟨p, hpN, hprime, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (6 * N + 1) (q := 6) (a := 1) (by norm_num) (by norm_num)
  unfold Nat.ModEq at hmod
  have hcol : col_plus (p / 6) = p := by unfold col_plus; omega
  refine ⟨p / 6, by omega, ?_⟩
  rw [hcol]
  exact hprime

end RNS.DirichletColumns

#print axioms RNS.DirichletColumns.col_minus_primes_infinite_holds
#print axioms RNS.DirichletColumns.col_plus_primes_infinite_holds
#print axioms RNS.DirichletColumns.col_minus_primes_unbounded_holds
#print axioms RNS.DirichletColumns.col_plus_primes_unbounded_holds
