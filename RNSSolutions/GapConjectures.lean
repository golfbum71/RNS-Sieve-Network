/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push               -- `push Not`
import RNSNetwork.Nodes.GapConjectures.Conclusions

/-!
# Proofs for GapConjectures

Rests on no other node. Tactic proofs are copied from
`rns_open_conjectures.lean`, Parts 1–5, with `brocard_blocked` written as the
identical `legendre_blocked`. Classical decidability is opened file-wide,
exactly as in the source and in this node's `Conclusions.lean`.
-/

open scoped Classical

namespace RNS.GapConjectures

/-! ## Part 1: Legendre from the survivor bound -/

private theorem composite_in_gap_is_blocked (n x : Nat) (hn : 1 ≤ n)
    (hx1 : n ^ 2 < x) (hx2 : x < (n + 1) ^ 2) (hcomp : ¬ x.Prime) :
    legendre_blocked n x := by
  have hn2 : 1 ≤ n ^ 2 := by nlinarith [Nat.mul_le_mul hn hn]
  have hx2' : 2 ≤ x := by omega
  have hx1' : x ≠ 1 := by omega
  set p := x.minFac
  have hp_prime : p.Prime := Nat.minFac_prime hx1'
  have hp_dvd : p ∣ x := Nat.minFac_dvd x
  obtain ⟨b, hb⟩ := hp_dvd
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hb
    omega
  have hb1 : b ≠ 1 := by
    intro h1
    apply hcomp
    rw [h1, Nat.mul_one] at hb
    rw [hb]
    exact hp_prime
  have hb2 : 2 ≤ b := by omega
  have hbdvd : b ∣ x := ⟨p, by rw [hb]; ring⟩
  have hple : p ≤ b := Nat.minFac_le_of_dvd hb2 hbdvd
  have hpp_le_x : p * p ≤ x := by
    calc p * p ≤ p * b := Nat.mul_le_mul (le_refl p) hple
      _ = x := hb.symm
  have hn1sq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  have hp_le_n : p ≤ n := by
    by_contra hcon
    push Not at hcon
    have hcon' : n + 1 ≤ p := hcon
    have hsq : (n + 1) * (n + 1) ≤ p * p := Nat.mul_le_mul hcon' hcon'
    nlinarith [hpp_le_x, hx2, hn1sq, hsq]
  exact ⟨p, hp_prime, hp_le_n, ⟨b, hb⟩⟩

theorem legendre_of_jacobsthal_holds : legendre_of_jacobsthal := by
  unfold legendre_of_jacobsthal legendre_conjecture
  intro H n hn
  obtain ⟨i, hi_lt, hi_not_blocked⟩ := H n hn (n ^ 2 + 1)
  have hn1sq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  have hx1 : n ^ 2 < n ^ 2 + 1 + i := by
    generalize n ^ 2 = m
    omega
  have hx2 : n ^ 2 + 1 + i < (n + 1) ^ 2 := by
    rw [hn1sq]
    generalize n ^ 2 = m
    omega
  refine ⟨n ^ 2 + 1 + i, ?_, hx1, hx2⟩
  by_contra hxp
  exact hi_not_blocked (composite_in_gap_is_blocked n (n ^ 2 + 1 + i) hn hx1 hx2 hxp)

/-! ## Part 2: Brocard from the four-survivor bound -/

private theorem composite_in_prime_gap_is_blocked (p q y : Nat) (hpq : consecutive_primes p q)
    (hy1 : p ^ 2 ≤ y) (hy2 : y < q ^ 2) (hcomp : ¬ y.Prime) :
    legendre_blocked p y := by
  obtain ⟨hp_prime, hq_prime, hpq_lt, hnone⟩ := hpq
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hy2' : 2 ≤ y := by nlinarith [hy1, Nat.mul_le_mul hp2 hp2]
  have hy1' : y ≠ 1 := by omega
  set r := y.minFac
  have hr_prime : r.Prime := Nat.minFac_prime hy1'
  have hr_dvd : r ∣ y := Nat.minFac_dvd y
  obtain ⟨b, hb⟩ := hr_dvd
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hb
    omega
  have hb1 : b ≠ 1 := by
    intro h1
    apply hcomp
    rw [h1, Nat.mul_one] at hb
    rw [hb]
    exact hr_prime
  have hb2 : 2 ≤ b := by omega
  have hbdvd : b ∣ y := ⟨r, by rw [hb]; ring⟩
  have hrle : r ≤ b := Nat.minFac_le_of_dvd hb2 hbdvd
  have hrr_le_y : r * r ≤ y := by
    calc r * r ≤ r * b := Nat.mul_le_mul (le_refl r) hrle
      _ = y := hb.symm
  have hr_lt_q : r < q := by
    by_contra hcon
    push Not at hcon
    have hqq : q * q ≤ r * r := Nat.mul_le_mul hcon hcon
    have hqsq : q ^ 2 = q * q := by ring
    nlinarith [hrr_le_y, hy2, hqsq, hqq]
  have hr_le_p : r ≤ p := by
    by_contra hcon
    push Not at hcon
    exact hnone r hr_prime hcon hr_lt_q
  exact ⟨r, hr_prime, hr_le_p, ⟨b, hb⟩⟩

theorem brocard_of_four_survivors_holds : brocard_of_four_survivors := by
  unfold brocard_of_four_survivors brocard_conjecture
  intro H p q hpq hp3
  obtain ⟨hp_prime, hq_prime, hpq_lt, hnone⟩ := hpq
  have hp_odd : p % 2 = 1 := by
    rcases hp_prime.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  have hq_odd : q % 2 = 1 := by
    rcases hq_prime.eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  have hq_ge : p + 2 ≤ q := by omega
  have hqsq : (p + 2) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq_ge 2
  have hqsq' : p ^ 2 + (4 * p + 4) ≤ q ^ 2 := by
    have heq : (p + 2) ^ 2 = p ^ 2 + 4 * p + 4 := by ring
    rw [heq] at hqsq
    omega
  have hsub : (Finset.Ico (p ^ 2) (p ^ 2 + (4 * p + 4))).filter (fun y => ¬ legendre_blocked p y)
      ⊆ (Finset.Ico (p ^ 2) (q ^ 2)).filter Nat.Prime := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_Ico] at hy ⊢
    obtain ⟨⟨hy1, hy2⟩, hynb⟩ := hy
    have hy2' : y < q ^ 2 := by omega
    refine ⟨⟨hy1, hy2'⟩, ?_⟩
    by_contra hcomp
    exact hynb (composite_in_prime_gap_is_blocked p q y ⟨hp_prime, hq_prime, hpq_lt, hnone⟩
      hy1 hy2' hcomp)
  have h4 := H p hp_prime hp3 (p ^ 2)
  exact le_trans h4 (Finset.card_le_card hsub)

/-! ## Part 3: Oppermann from the two-sided survivor bound -/

private theorem composite_below_succ_sq_is_blocked (m y : Nat) (hy0 : 2 ≤ y)
    (hylt : y < (m + 1) ^ 2) (hcomp : ¬ y.Prime) : legendre_blocked m y := by
  have hy1' : y ≠ 1 := by omega
  set p := y.minFac
  have hp_prime : p.Prime := Nat.minFac_prime hy1'
  have hp_dvd : p ∣ y := Nat.minFac_dvd y
  obtain ⟨b, hb⟩ := hp_dvd
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, Nat.mul_zero] at hb
    omega
  have hb1 : b ≠ 1 := by
    intro h1
    apply hcomp
    rw [h1, Nat.mul_one] at hb
    rw [hb]
    exact hp_prime
  have hb2 : 2 ≤ b := by omega
  have hbdvd : b ∣ y := ⟨p, by rw [hb]; ring⟩
  have hple : p ≤ b := Nat.minFac_le_of_dvd hb2 hbdvd
  have hpp_le_y : p * p ≤ y := by
    calc p * p ≤ p * b := Nat.mul_le_mul (le_refl p) hple
      _ = y := hb.symm
  have hm1sq : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
  have hp_le_m : p ≤ m := by
    by_contra hcon
    push Not at hcon
    have hcon' : m + 1 ≤ p := hcon
    have hsq : (m + 1) * (m + 1) ≤ p * p := Nat.mul_le_mul hcon' hcon'
    nlinarith [hpp_le_y, hylt, hm1sq, hsq]
  exact ⟨p, hp_prime, hp_le_m, ⟨b, hb⟩⟩

private theorem composite_in_oppermann_lower_is_blocked (n y : Nat) (hn : 2 ≤ n)
    (hy1 : n ^ 2 - n < y) (hy2 : y < n ^ 2) (hcomp : ¬ y.Prime) :
    legendre_blocked (n - 1) y := by
  have hm1 : (n - 1) + 1 = n := by omega
  have hy2' : y < ((n - 1) + 1) ^ 2 := by rw [hm1]; exact hy2
  have h2n : 2 * n ≤ n ^ 2 := by nlinarith [Nat.mul_le_mul hn (le_refl n)]
  have hy0 : 2 ≤ y := by
    generalize n ^ 2 = X at hy1 h2n
    omega
  exact composite_below_succ_sq_is_blocked (n - 1) y hy0 hy2' hcomp

private theorem composite_in_oppermann_upper_is_blocked (n y : Nat) (hn : 2 ≤ n)
    (hy1 : n ^ 2 < y) (hy2 : y < n ^ 2 + n) (hcomp : ¬ y.Prime) :
    legendre_blocked n y := by
  have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  have hy2' : y < (n + 1) ^ 2 := by
    rw [hexp]
    generalize n ^ 2 = X at hy2 ⊢
    omega
  have hnn : 1 ≤ n ^ 2 := by nlinarith [Nat.mul_le_mul hn hn]
  have hy0 : 2 ≤ y := by
    generalize n ^ 2 = X at hy1 hnn
    omega
  exact composite_below_succ_sq_is_blocked n y hy0 hy2' hcomp

theorem oppermann_of_bound_holds : oppermann_of_bound := by
  unfold oppermann_of_bound oppermann_conjecture
  intro H n hn
  obtain ⟨Hlo, Hhi⟩ := H n hn
  constructor
  · obtain ⟨i, hi_lt, hi_nb⟩ := Hlo (n ^ 2 - n + 1)
    have h2n : 2 * n ≤ n ^ 2 := by nlinarith [Nat.mul_le_mul hn (le_refl n)]
    have hy_lo : n ^ 2 - n < n ^ 2 - n + 1 + i := by omega
    have hy_hi : n ^ 2 - n + 1 + i < n ^ 2 := by
      generalize n ^ 2 = X at h2n ⊢
      omega
    refine ⟨n ^ 2 - n + 1 + i, ?_, hy_lo, hy_hi⟩
    by_contra hyp
    exact hi_nb (composite_in_oppermann_lower_is_blocked n (n ^ 2 - n + 1 + i) hn hy_lo hy_hi
      hyp)
  · obtain ⟨i, hi_lt, hi_nb⟩ := Hhi (n ^ 2 + 1)
    have hy_lo : n ^ 2 < n ^ 2 + 1 + i := by omega
    have hy_hi : n ^ 2 + 1 + i < n ^ 2 + n := by omega
    refine ⟨n ^ 2 + 1 + i, ?_, hy_lo, hy_hi⟩
    by_contra hyp
    exact hi_nb (composite_in_oppermann_upper_is_blocked n (n ^ 2 + 1 + i) hn hy_lo hy_hi hyp)

/-! ## Part 4: Andrica from Oppermann -/

private theorem prime_ne_mul_of_ge_two (p a b : Nat) (hp : p.Prime) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (heq : p = a * b) : False := by
  have hdvd : a ∣ p := ⟨b, heq⟩
  rcases hp.eq_one_or_self_of_dvd a hdvd with h1 | hself
  · omega
  · rw [hself] at heq
    have hp_pos : 0 < p := hp.pos
    have heq2 : p * 1 = p * b := by rw [mul_one]; exact heq
    have hb1 : 1 = b := Nat.eq_of_mul_eq_mul_left hp_pos heq2
    omega

private theorem exists_sqrt_window (p : Nat) : ∃ m : Nat, m ^ 2 ≤ p ∧ p < (m + 1) ^ 2 := by
  induction p with
  | zero => exact ⟨0, by norm_num, by norm_num⟩
  | succ k ih =>
    obtain ⟨m, hm1, hm2⟩ := ih
    by_cases h : k + 1 < (m + 1) ^ 2
    · refine ⟨m, ?_, h⟩
      generalize m ^ 2 = X at hm1 ⊢
      omega
    · have heq : k + 1 = (m + 1) ^ 2 := by
        generalize (m + 1) ^ 2 = X at h hm2 ⊢
        omega
      refine ⟨m + 1, ?_, ?_⟩
      · generalize (m + 1) ^ 2 = X at heq ⊢
        omega
      · have hexp : (m + 1 + 1) ^ 2 = (m + 1) ^ 2 + 2 * (m + 1) + 1 := by ring
        generalize hX : (m + 1) ^ 2 = X at heq hexp
        generalize (m + 1 + 1) ^ 2 = Y at hexp ⊢
        omega

private theorem cross_window_LU (m p q : Nat) (hm : 2 ≤ m)
    (hp1 : m ^ 2 - m + 1 ≤ p) (hpq : p < q) (hq2 : q ≤ m ^ 2 + m - 1) :
    (q - p - 1) ^ 2 < 4 * p := by
  obtain ⟨g, hg⟩ : ∃ g, q = p + 1 + g := ⟨q - p - 1, by omega⟩
  have hgeq : q - p - 1 = g := by omega
  rw [hgeq]
  have hbound : p + g + 2 ≤ m ^ 2 + m := by
    generalize m ^ 2 = X at hp1 hq2
    omega
  have hp1' : m ^ 2 + 1 ≤ p + m := by
    generalize m ^ 2 = X at hp1
    omega
  have hg2m3 : g + 3 ≤ 2 * m := by
    generalize hM : m ^ 2 = M at hbound hp1'
    omega
  obtain ⟨d, hd⟩ : ∃ d, d + 3 = 2 * m := ⟨2 * m - 3, by omega⟩
  have hg_le_d : g ≤ d := by omega
  have hsq_g : g ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hg_le_d 2
  have hd2 : d ^ 2 + 6 * d + 9 = 4 * m ^ 2 := by
    have h1 : (d + 3) ^ 2 = (2 * m) ^ 2 := by rw [hd]
    nlinarith [h1]
  have hfinal : d ^ 2 < 4 * p := by
    generalize hM : m ^ 2 = M at hp1' hd2
    generalize hD : d ^ 2 = D at hd2 ⊢
    omega
  exact lt_of_le_of_lt hsq_g hfinal

private theorem cross_window_UL (m p q : Nat) (hm : 2 ≤ m)
    (hp1 : m ^ 2 + 1 ≤ p) (hpq : p < q) (hq2 : q ≤ m ^ 2 + 2 * m) :
    (q - p - 1) ^ 2 < 4 * p := by
  obtain ⟨g, hg⟩ : ∃ g, q = p + 1 + g := ⟨q - p - 1, by omega⟩
  have hgeq : q - p - 1 = g := by omega
  rw [hgeq]
  have hbound : p + g + 1 ≤ m ^ 2 + 2 * m := by
    generalize m ^ 2 = X at hp1 hq2
    omega
  have hg2m2 : g + 2 ≤ 2 * m := by
    generalize hM : m ^ 2 = M at hbound hp1
    omega
  obtain ⟨d, hd⟩ : ∃ d, d + 2 = 2 * m := ⟨2 * m - 2, by omega⟩
  have hg_le_d : g ≤ d := by omega
  have hsq_g : g ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hg_le_d 2
  have hd2 : d ^ 2 + 4 * d + 4 = 4 * m ^ 2 := by
    have h1 : (d + 2) ^ 2 = (2 * m) ^ 2 := by rw [hd]
    nlinarith [h1]
  have hfinal : d ^ 2 < 4 * p := by
    generalize hM : m ^ 2 = M at hp1 hd2
    generalize hD : d ^ 2 = D at hd2 ⊢
    omega
  exact lt_of_le_of_lt hsq_g hfinal

theorem andrica_of_oppermann_holds : andrica_of_oppermann := by
  unfold andrica_of_oppermann andrica_conjecture
  intro H p q hpq hp3
  obtain ⟨hp_prime, hq_prime, hpq_lt, hnone⟩ := hpq
  obtain ⟨m, hm1, hm2⟩ := exists_sqrt_window p
  have hpm2 : p ≠ m ^ 2 := by
    intro heq
    rcases Nat.lt_or_ge m 2 with hm_small | hm_ge2
    · interval_cases m <;> simp_all
    · exact prime_ne_mul_of_ge_two p m m hp_prime hm_ge2 hm_ge2 (by rw [heq]; ring)
  have hm2_lt : m ^ 2 < p := by omega
  have hpmm : p ≠ m ^ 2 + m := by
    intro heq
    rcases Nat.lt_or_ge m 2 with hm_small | hm_ge2
    · interval_cases m <;> simp_all
    · have hfac : m ^ 2 + m = m * (m + 1) := by ring
      rw [hfac] at heq
      exact prime_ne_mul_of_ge_two p m (m + 1) hp_prime hm_ge2 (by omega) heq
  rcases Nat.lt_or_ge p (m ^ 2 + m) with hcase | hcase
  · have hm_ge2 : 2 ≤ m := by
      by_contra hcon
      push Not at hcon
      interval_cases m <;> omega
    obtain ⟨⟨p', hp'_prime, hp'_lo, hp'_hi⟩, -⟩ := H (m + 1) (by omega)
    have hexp : (m + 1) ^ 2 - (m + 1) = m ^ 2 + m := by
      have : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
      omega
    rw [hexp] at hp'_lo
    have hexp2 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
    rw [hexp2] at hp'_hi
    have hp_lt_p' : p < p' := by omega
    have hq_le_p' : q ≤ p' := by
      by_contra hcon
      push Not at hcon
      exact hnone p' hp'_prime hp_lt_p' (by omega)
    exact cross_window_UL m p q hm_ge2 (by omega) hpq_lt (by omega)
  · have hcase' : m ^ 2 + m < p := by omega
    have hm_ge2' : 2 ≤ m + 1 := by
      by_contra hcon
      push Not at hcon
      have hm0 : m = 0 := by omega
      rw [hm0] at hm2
      norm_num at hm2
      omega
    obtain ⟨-, ⟨p', hp'_prime, hp'_lo, hp'_hi⟩⟩ := H (m + 1) hm_ge2'
    have hexp2 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
    rw [hexp2] at hp'_lo
    have hexp3 : (m + 1) ^ 2 + (m + 1) = m ^ 2 + 3 * m + 2 := by ring
    rw [hexp3] at hp'_hi
    have hp_lt_p' : p < p' := by
      have : p < (m + 1) ^ 2 := hm2
      omega
    have hq_le_p' : q ≤ p' := by
      by_contra hcon
      push Not at hcon
      exact hnone p' hp'_prime hp_lt_p' (by omega)
    have hp1' : (m + 1) ^ 2 - (m + 1) + 1 ≤ p := by
      rw [hexp2]
      omega
    have hq2' : q ≤ (m + 1) ^ 2 + (m + 1) - 1 := by
      rw [hexp2]
      omega
    exact cross_window_LU (m + 1) p q (by omega) hp1' hpq_lt hq2'

/-! ## Part 5: Legendre from Oppermann -/

theorem legendre_of_oppermann_holds : legendre_of_oppermann := by
  unfold legendre_of_oppermann legendre_conjecture
  intro H n hn
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · have hn_eq : n = 1 := by omega
    subst hn_eq
    exact ⟨2, Nat.prime_two, by norm_num, by norm_num⟩
  · obtain ⟨-, ⟨p, hp_prime, hp_lo, hp_hi⟩⟩ := H n hn2
    refine ⟨p, hp_prime, hp_lo, ?_⟩
    have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [hsq]
    generalize n ^ 2 = X at hp_hi ⊢
    omega

end RNS.GapConjectures

#print axioms RNS.GapConjectures.legendre_of_jacobsthal_holds
#print axioms RNS.GapConjectures.brocard_of_four_survivors_holds
#print axioms RNS.GapConjectures.oppermann_of_bound_holds
#print axioms RNS.GapConjectures.andrica_of_oppermann_holds
#print axioms RNS.GapConjectures.legendre_of_oppermann_holds
