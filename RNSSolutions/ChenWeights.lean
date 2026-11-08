/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.ChenWeights.Conclusions
import Mathlib

/-!
# Proofs for ChenWeights

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. A number all of whose prime factors are at least the cutoff is at least
the cutoff raised to its number of prime factors. So below the cube of the
cutoff such a number has at most two prime factors. If a number with three or
more prime factors has exactly one wheel dividing it, and not its square,
then dividing by that wheel leaves a number with no wheel factor, below the
cube, with at least two prime factors: exactly two, the smallest factor
first, which is one of the counted ways. Otherwise two wheels, or a wheel and
its square, already take the weight to zero.
-/

namespace RNS.ChenWeights

/-- A number whose prime factors are all at least `y` is at least `y` to its
number of prime factors. -/
private theorem pow_cardFactors_le {y n : Nat} (hn : n ≠ 0)
    (h : ∀ r, r.Prime → r ∣ n → y ≤ r) : y ^ ArithmeticFunction.cardFactors n ≤ n := by
  have hmem : ∀ x ∈ (n.primeFactorsList : Multiset Nat), y ≤ x := by
    intro x hx
    have hx' : x ∈ n.primeFactorsList := Multiset.mem_coe.mp hx
    exact h x (Nat.prime_of_mem_primeFactorsList hx') (Nat.dvd_of_mem_primeFactorsList hx')
  have hp := Multiset.pow_card_le_prod hmem
  rw [Multiset.coe_card, Multiset.prod_coe, Nat.prod_primeFactorsList hn] at hp
  rw [ArithmeticFunction.cardFactors_apply]
  exact hp

/-- Below the cube of `y`, a number whose prime factors are all at least `y`
has at most two prime factors. -/
private theorem cardFactors_le_two {y n : Nat} (hn : n ≠ 0) (hny : n < y ^ 3)
    (h : ∀ r, r.Prime → r ∣ n → y ≤ r) : ArithmeticFunction.cardFactors n ≤ 2 := by
  by_contra hc
  have hy : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · subst h0; simp at hny
    · exact h0
  have h3 : y ^ 3 ≤ y ^ ArithmeticFunction.cardFactors n :=
    Nat.pow_le_pow_right hy (by omega)
  have := pow_cardFactors_le hn h
  omega

theorem chen_weight_le_holds : chen_weight_le := by
  intro y n hn1 hny
  have hn0 : n ≠ 0 := by omega
  have ha0 : (0 : ℝ) ≤ ((small_factors y n).card : ℝ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ ((chen_triples y n).card : ℝ) := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ ((small_square_factors y n).card : ℝ) := Nat.cast_nonneg _
  by_cases hΩ : ArithmeticFunction.cardFactors n ≤ 2
  · rw [if_pos hΩ]
    linarith
  rw [if_neg hΩ]
  suffices hcase : 2 ≤ (small_factors y n).card ∨
      (1 ≤ (small_factors y n).card ∧ 1 ≤ (chen_triples y n).card) ∨
      (1 ≤ (small_factors y n).card ∧ 1 ≤ (small_square_factors y n).card) by
    rcases hcase with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : (2 : ℝ) ≤ ((small_factors y n).card : ℝ) := by exact_mod_cast h
      linarith
    · have : (1 : ℝ) ≤ ((small_factors y n).card : ℝ) := by exact_mod_cast h1
      have : (1 : ℝ) ≤ ((chen_triples y n).card : ℝ) := by exact_mod_cast h2
      linarith
    · have : (1 : ℝ) ≤ ((small_factors y n).card : ℝ) := by exact_mod_cast h1
      have : (1 : ℝ) ≤ ((small_square_factors y n).card : ℝ) := by exact_mod_cast h2
      linarith
  -- No wheel dividing `n` is impossible.
  have hne : (small_factors y n).card ≠ 0 := by
    intro h0
    apply hΩ
    refine cardFactors_le_two hn0 hny (fun r hr hrn => ?_)
    by_contra hlt
    have hmem : r ∈ small_factors y n := by
      unfold small_factors
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hr, hrn, hn0⟩, by omega⟩
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hmem
    exact Finset.notMem_empty r hmem
  rcases Nat.lt_or_ge 1 (small_factors y n).card with h2 | h1
  · left; omega
  have hone : (small_factors y n).card = 1 := by omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hone
  have hpmem : p ∈ small_factors y n := by rw [hp]; exact Finset.mem_singleton_self p
  unfold small_factors at hpmem
  obtain ⟨hpf, hpy⟩ := Finset.mem_filter.mp hpmem
  obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.mp hpf
  -- every prime factor of `n` below `y` is `p`
  have honly : ∀ r, r.Prime → r ∣ n → r < y → r = p := by
    intro r hr hrn hry
    have : r ∈ small_factors y n := by
      unfold small_factors
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hr, hrn, hn0⟩, hry⟩
    rw [hp] at this
    exact Finset.mem_singleton.mp this
  by_cases hsq : p ^ 2 ∣ n
  · right; right
    refine ⟨by omega, Finset.card_pos.mpr ⟨p, ?_⟩⟩
    unfold small_square_factors
    exact Finset.mem_filter.mpr ⟨hpf, hpy, hsq⟩
  right; left
  refine ⟨by omega, Finset.card_pos.mpr ?_⟩
  -- the cofactor
  obtain ⟨m, hm⟩ := hpn
  have hm0 : m ≠ 0 := by rintro rfl; exact hn0 (by simpa using hm)
  have hmlarge : ∀ r, r.Prime → r ∣ m → y ≤ r := by
    intro r hr hrm
    by_contra hry
    have hrp : r = p := honly r hr (by rw [hm]; exact Dvd.dvd.mul_left hrm p) (by omega)
    subst hrp
    apply hsq
    rw [hm, pow_two]
    exact mul_dvd_mul_left r hrm
  have hmn : m < y ^ 3 := by
    have h2p := hpp.two_le
    have : m ≤ n := by rw [hm]; nlinarith
    omega
  have hΩn : ArithmeticFunction.cardFactors n = 1 + ArithmeticFunction.cardFactors m := by
    rw [hm, ArithmeticFunction.cardFactors_mul hpp.ne_zero hm0,
      ArithmeticFunction.cardFactors_apply_prime hpp]
  have hΩm2 : ArithmeticFunction.cardFactors m = 2 := by
    have := cardFactors_le_two hm0 hmn hmlarge
    omega
  have hm1 : m ≠ 1 := by rintro rfl; simp at hΩm2
  have hq₁p : m.minFac.Prime := Nat.minFac_prime hm1
  have hq₁le : ∀ r, r.Prime → r ∣ m → m.minFac ≤ r :=
    fun r hr hrm => Nat.minFac_le_of_dvd hr.two_le hrm
  have hyq₁ : y ≤ m.minFac := hmlarge m.minFac hq₁p (Nat.minFac_dvd m)
  obtain ⟨q₂, hq₂⟩ := Nat.minFac_dvd m
  generalize m.minFac = q₁ at hq₁p hq₁le hyq₁ hq₂
  have hq₂0 : q₂ ≠ 0 := by rintro rfl; exact hm0 (by simpa using hq₂)
  have hΩq₂ : ArithmeticFunction.cardFactors q₂ = 1 := by
    have h := ArithmeticFunction.cardFactors_mul hq₁p.ne_zero hq₂0
    rw [← hq₂, hΩm2, ArithmeticFunction.cardFactors_apply_prime hq₁p] at h
    omega
  have hq₂p : q₂.Prime := ArithmeticFunction.cardFactors_eq_one_iff_prime.mp hΩq₂
  have hq₁q₂ : q₁ ≤ q₂ := hq₁le q₂ hq₂p (Dvd.intro_left q₁ hq₂.symm)
  have hn_eq : p * q₁ * q₂ = n := by rw [mul_assoc, ← hq₂, ← hm]
  refine ⟨(p, q₁, q₂), ?_⟩
  unfold chen_triples
  refine Finset.mem_filter.mpr ⟨?_, hpy, hyq₁, hq₁q₂, hn_eq⟩
  refine Finset.mem_product.mpr ⟨hpf, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
  · exact Nat.mem_primeFactors.mpr ⟨hq₁p, ⟨p * q₂, by rw [← hn_eq]; ring⟩, hn0⟩
  · exact Nat.mem_primeFactors.mpr ⟨hq₂p, ⟨p * q₁, by rw [← hn_eq]; ring⟩, hn0⟩

#print axioms RNS.ChenWeights.chen_weight_le_holds

end RNS.ChenWeights
