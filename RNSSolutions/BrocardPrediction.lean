/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib
import RNSNetwork.Nodes.BrocardPrediction.Conclusions

/-!
# Proofs for BrocardPrediction

Draft (2026-11-14): not yet built.

Rests on no other node (Mathlib only).

* `window_exact_count`: for one slot, the alternating sum over the sets of
  smaller wheels whose product divides it is 1 when no smaller wheel divides
  it and 0 otherwise (the sets are all the subsets of the smaller wheels that
  do divide it). Summing over the slots the wheel divides, and writing each
  slot divisible by a product as the product times a number on the tracks,
  gives the count.
* `window_prime_count`: a slot that is not prime has a smallest prime factor,
  which is a wheel from 5 up to the base prime; sorting the slots by it gives
  the first-blocked sets.
* `cycling_blocked_closed_form`: the pairs (wheel, set of smaller wheels) are
  the nonempty sets of wheels up to the base prime, listed by their largest
  member (induction on the largest wheel). A set of wheels up to the window
  length whose product fits in the window is a set of wheels up to the base
  prime, or one single prime above it. The sets of wheels are the squarefree
  numbers on the tracks, and the sign is the Möbius function.
* `twin_prediction_closed_form`: a step from `cycling_blocked_closed_form`.
-/

namespace RNS.BrocardPrediction

/-! ## Small facts about the wheels -/

private theorem mem_wheels_below {z r : ℕ} :
    r ∈ wheels_below z ↔ r < z ∧ r.Prime ∧ 5 ≤ r := by
  unfold wheels_below
  rw [Finset.mem_filter, Finset.mem_range]

/-- A prime dividing a number on the 6n±1 tracks is at least 5. -/
private theorem five_le_of_prime_dvd {m r : ℕ} (h2 : m % 2 ≠ 0) (h3 : m % 3 ≠ 0)
    (hr : r.Prime) (hd : r ∣ m) : 5 ≤ r := by
  by_contra hlt
  have h2le := hr.two_le
  have hr5 : r < 5 := by omega
  interval_cases r
  · exact h2 (Nat.mod_eq_zero_of_dvd hd)
  · exact h3 (Nat.mod_eq_zero_of_dvd hd)
  · exact absurd hr (by decide)

/-- A prime below 5 does not divide a product of primes from 5 up. -/
private theorem not_dvd_prod {s : Finset ℕ} (hs : ∀ r ∈ s, r.Prime ∧ 5 ≤ r)
    {k : ℕ} (hk : k.Prime) (hk5 : k < 5) : ¬ k ∣ ∏ r ∈ s, r := by
  intro h
  obtain ⟨r, hr, hkr⟩ := (hk.prime.dvd_finsetProd_iff (fun r => r)).mp h
  have hkr' : k ∣ r := hkr
  have heq : k = r := (Nat.prime_dvd_prime_iff_eq hk (hs r hr).1).mp hkr'
  have := (hs r hr).2
  omega

/-- A prime below 5 does not divide a wheel times a product of wheels. -/
private theorem small_not_dvd {q : ℕ} {D : Finset ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hD : ∀ r ∈ D, r.Prime ∧ 5 ≤ r) {k : ℕ} (hk : k.Prime) (hk5 : k < 5) :
    ¬ k ∣ q * ∏ r ∈ D, r := by
  intro h
  rcases hk.dvd_mul.mp h with h1 | h1
  · have heq : k = q := (Nat.prime_dvd_prime_iff_eq hk hq).mp h1
    omega
  · exact not_dvd_prod hD hk hk5 h1

/-! ## The exact count -/

/-- For one number: the alternating sum over the sets of wheels whose product
divides it is 1 when no wheel divides it, and 0 otherwise. -/
private theorem alt_indicator (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) (m : ℕ) :
    ∑ D ∈ S.powerset, (-1 : ℤ) ^ D.card * (if (∏ r ∈ D, r) ∣ m then (1 : ℤ) else 0)
      = if ∀ r ∈ S, ¬ r ∣ m then (1 : ℤ) else 0 := by
  have h1 : ∀ D ∈ S.powerset,
      (-1 : ℤ) ^ D.card * (if (∏ r ∈ D, r) ∣ m then (1 : ℤ) else 0)
        = if D ∈ (S.filter (fun r => r ∣ m)).powerset then (-1 : ℤ) ^ D.card else 0 := by
    intro D hD
    have hDS := Finset.mem_powerset.mp hD
    have hiff : (∏ r ∈ D, r) ∣ m ↔ D ∈ (S.filter (fun r => r ∣ m)).powerset := by
      constructor
      · intro h
        refine Finset.mem_powerset.mpr (fun r hr => ?_)
        have hrd : r ∣ ∏ x ∈ D, x := Finset.dvd_prod_of_mem (fun x => x) hr
        exact Finset.mem_filter.mpr ⟨hDS hr, hrd.trans h⟩
      · intro h
        have h' := Finset.mem_powerset.mp h
        exact Finset.prod_primes_dvd m (fun r hr => (hS r (hDS hr)).prime)
          (fun r hr => (Finset.mem_filter.mp (h' hr)).2)
    by_cases hc : (∏ r ∈ D, r) ∣ m
    · rw [if_pos hc, if_pos (hiff.mp hc), mul_one]
    · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h)), mul_zero]
  have h2 : S.powerset.filter (fun D => D ∈ (S.filter (fun r => r ∣ m)).powerset)
      = (S.filter (fun r => r ∣ m)).powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨fun x hx => (Finset.mem_filter.mp (h hx)).1, h⟩⟩
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, h2, Finset.sum_powerset_neg_one_pow_card]
  by_cases hc : ∀ r ∈ S, ¬ r ∣ m
  · have he : S.filter (fun r => r ∣ m) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun r hr => hc r hr)
    rw [if_pos hc, if_pos he]
  · have hne : ¬ S.filter (fun r => r ∣ m) = ∅ := by
      intro he
      apply hc
      intro r hr hd
      have hmem : r ∈ S.filter (fun r => r ∣ m) := Finset.mem_filter.mpr ⟨hr, hd⟩
      rw [he] at hmem
      exact absurd hmem (Finset.notMem_empty r)
    rw [if_neg hc, if_neg hne]

/-- Legendre's count for any finite set of numbers and any set of prime wheels. -/
private theorem sifted_card (X S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) :
    ((X.filter (fun m => ∀ r ∈ S, ¬ r ∣ m)).card : ℤ)
      = ∑ D ∈ S.powerset,
          (-1 : ℤ) ^ D.card * ((X.filter (fun m => (∏ r ∈ D, r) ∣ m)).card : ℤ) := by
  have hL : ((X.filter (fun m => ∀ r ∈ S, ¬ r ∣ m)).card : ℤ)
      = ∑ m ∈ X, if ∀ r ∈ S, ¬ r ∣ m then (1 : ℤ) else 0 :=
    Finset.natCast_card_filter _ _
  have hR : ∀ D ∈ S.powerset,
      (-1 : ℤ) ^ D.card * ((X.filter (fun m => (∏ r ∈ D, r) ∣ m)).card : ℤ)
        = ∑ m ∈ X, (-1 : ℤ) ^ D.card * (if (∏ r ∈ D, r) ∣ m then (1 : ℤ) else 0) := by
    intro D _
    have hc : ((X.filter (fun m => (∏ r ∈ D, r) ∣ m)).card : ℤ)
        = ∑ m ∈ X, if (∏ r ∈ D, r) ∣ m then (1 : ℤ) else 0 :=
      Finset.natCast_card_filter _ _
    rw [hc, Finset.mul_sum]
  rw [hL, Finset.sum_congr rfl hR, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun m _ => (alt_indicator S hS m).symm)

/-- The numbers of the window on the tracks that `n` divides are `n` times the
shared slots of `n`. -/
private theorem shared_card (A B n : ℕ) (hn : 0 < n) (h2 : ¬ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    ((Finset.Ioo A B).filter (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0 ∧ n ∣ m)).card
      = shared_slots A B n := by
  unfold shared_slots
  refine Finset.card_nbij' (fun m => m / n) (fun t => n * t) ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨hI, hm2, hm3, hd⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hm)
    have hI' := Finset.mem_Ioo.mp hI
    have he : n * (m / n) = m := Nat.mul_div_cancel' hd
    have hlt : m / n < B := lt_of_le_of_lt (Nat.div_le_self m n) hI'.2
    have hc2 : (m / n) % 2 ≠ 0 := by
      intro h
      have h' : 2 ∣ n * (m / n) := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) n
      rw [he] at h'
      exact hm2 (Nat.mod_eq_zero_of_dvd h')
    have hc3 : (m / n) % 3 ≠ 0 := by
      intro h
      have h' : 3 ∣ n * (m / n) := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) n
      rw [he] at h'
      exact hm3 (Nat.mod_eq_zero_of_dvd h')
    have hA : A < n * (m / n) := by rw [he]; exact hI'.1
    have hB : n * (m / n) < B := by rw [he]; exact hI'.2
    exact Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hc2, hc3, hA, hB⟩)
  · intro t ht
    obtain ⟨_, ht2, ht3, hA, hB⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
    have hc2 : (n * t) % 2 ≠ 0 := by
      intro h
      rcases Nat.prime_two.dvd_mul.mp (Nat.dvd_of_mod_eq_zero h) with h' | h'
      · exact h2 h'
      · exact ht2 (Nat.mod_eq_zero_of_dvd h')
    have hc3 : (n * t) % 3 ≠ 0 := by
      intro h
      rcases Nat.prime_three.dvd_mul.mp (Nat.dvd_of_mod_eq_zero h) with h' | h'
      · exact h3 h'
      · exact ht3 (Nat.mod_eq_zero_of_dvd h')
    exact Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hA, hB⟩, hc2, hc3, Dvd.intro t rfl⟩)
  · intro m hm
    obtain ⟨_, _, _, hd⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hm)
    show n * (m / n) = m
    exact Nat.mul_div_cancel' hd
  · intro t _
    show n * t / n = t
    exact Nat.mul_div_cancel_left t hn

theorem window_exact_count_holds : window_exact_count := by
  intro A B q hq hq5
  have hfb : first_blocked A B q
      = (((Finset.Ioo A B).filter (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0 ∧ q ∣ m)).filter
          (fun m => ∀ r ∈ wheels_below q, ¬ r ∣ m)).card := by
    unfold first_blocked
    rw [Finset.filter_filter]
    apply congrArg Finset.card
    refine Finset.filter_congr (fun m _ => ?_)
    constructor
    · rintro ⟨a, b, c, d⟩
      exact ⟨⟨a, b, c⟩, d⟩
    · rintro ⟨⟨a, b, c⟩, d⟩
      exact ⟨a, b, c, d⟩
  rw [hfb, sifted_card ((Finset.Ioo A B).filter (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0 ∧ q ∣ m))
    (wheels_below q) (fun r hr => (mem_wheels_below.mp hr).2.1)]
  refine Finset.sum_congr rfl (fun D hD => ?_)
  have hDS := Finset.mem_powerset.mp hD
  have hDp : ∀ r ∈ D, r.Prime ∧ 5 ≤ r := fun r hr => (mem_wheels_below.mp (hDS hr)).2
  have hqD : q ∉ D := fun h => lt_irrefl q (mem_wheels_below.mp (hDS h)).1
  have hpos : 0 < q * ∏ r ∈ D, r :=
    Nat.mul_pos hq.pos (Finset.prod_pos (fun r hr => (hDp r hr).1.pos))
  have hins : ∏ r ∈ insert q D, r = q * ∏ r ∈ D, r := Finset.prod_insert hqD
  have hiff : ∀ m : ℕ, (q ∣ m ∧ (∏ r ∈ D, r) ∣ m) ↔ (q * ∏ r ∈ D, r) ∣ m := by
    intro m
    constructor
    · rintro ⟨h1, h2⟩
      rw [← hins]
      refine Finset.prod_primes_dvd m (fun r hr => ?_) (fun r hr => ?_)
      · rcases Finset.mem_insert.mp hr with h | h
        · rw [h]; exact hq.prime
        · exact (hDp r h).1.prime
      · rcases Finset.mem_insert.mp hr with h | h
        · rw [h]; exact h1
        · have hrd : r ∣ ∏ x ∈ D, x := Finset.dvd_prod_of_mem (fun x => x) h
          exact hrd.trans h2
    · intro h
      exact ⟨(dvd_mul_right q _).trans h, (dvd_mul_left _ q).trans h⟩
  have hcard : (((Finset.Ioo A B).filter (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0 ∧ q ∣ m)).filter
        (fun m => (∏ r ∈ D, r) ∣ m)).card = shared_slots A B (q * ∏ r ∈ D, r) := by
    rw [← shared_card A B (q * ∏ r ∈ D, r) hpos
      (small_not_dvd hq hq5 hDp Nat.prime_two (by norm_num))
      (small_not_dvd hq hq5 hDp Nat.prime_three (by norm_num)), Finset.filter_filter]
    apply congrArg Finset.card
    refine Finset.filter_congr (fun m _ => ?_)
    constructor
    · rintro ⟨⟨a, b, c⟩, d⟩
      exact ⟨a, b, (hiff m).mp ⟨c, d⟩⟩
    · rintro ⟨a, b, c⟩
      exact ⟨⟨a, b, ((hiff m).mpr c).1⟩, ((hiff m).mpr c).2⟩
  rw [hcard]

/-! ## Primes plus first-blocked slots -/

theorem window_prime_count_holds : window_prime_count := by
  intro p P hp hp5 hnext
  have hp25 : 25 ≤ p ^ 2 := by
    have := Nat.pow_le_pow_left hp5 2
    norm_num at this
    exact this
  have hpsq : p ≤ p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ 2 := Nat.pow_le_pow_right (by omega) (by norm_num)
  -- the slots
  have hslots : shared_slots (p ^ 2) (P ^ 2) 1
      = ((Finset.Ioo (p ^ 2) (P ^ 2)).filter (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0)).card := by
    rw [← shared_card (p ^ 2) (P ^ 2) 1 Nat.one_pos (by decide) (by decide)]
    apply congrArg Finset.card
    refine Finset.filter_congr (fun m _ => ?_)
    constructor
    · rintro ⟨a, b, _⟩
      exact ⟨a, b⟩
    · rintro ⟨a, b⟩
      exact ⟨a, b, one_dvd m⟩
  -- split the slots into primes and the rest
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.Ioo (p ^ 2) (P ^ 2)).filter (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0))
    (fun m => Nat.Prime m)
  -- the prime slots are the primes of the window
  have ha : (((Finset.Ioo (p ^ 2) (P ^ 2)).filter (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0)).filter
        (fun m => Nat.Prime m)).card
      = ((Finset.Ioo (p ^ 2) (P ^ 2)).filter Nat.Prime).card := by
    apply congrArg Finset.card
    ext m
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hI, _⟩, hm⟩
      exact ⟨hI, hm⟩
    · rintro ⟨hI, hm⟩
      have hI' := Finset.mem_Ioo.mp hI
      refine ⟨⟨hI, ?_, ?_⟩, hm⟩
      · intro h
        have heq : 2 = m :=
          (Nat.prime_dvd_prime_iff_eq Nat.prime_two hm).mp (Nat.dvd_of_mod_eq_zero h)
        omega
      · intro h
        have heq : 3 = m :=
          (Nat.prime_dvd_prime_iff_eq Nat.prime_three hm).mp (Nat.dvd_of_mod_eq_zero h)
        omega
  -- the smallest prime factor of a slot that is not prime is a wheel up to p
  have hmaps : ((((Finset.Ioo (p ^ 2) (P ^ 2)).filter (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0)).filter
        (fun m => ¬ Nat.Prime m) : Finset ℕ) : Set ℕ).MapsTo Nat.minFac
        (wheels_below (p + 1) : Set ℕ) := by
    intro m hm
    obtain ⟨hm1, hnp⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hm)
    obtain ⟨hI, h2, h3⟩ := Finset.mem_filter.mp hm1
    have hI' := Finset.mem_Ioo.mp hI
    have hm1' : m ≠ 1 := by omega
    have hmp : m.minFac.Prime := Nat.minFac_prime hm1'
    have h5 : 5 ≤ m.minFac := five_le_of_prime_dvd h2 h3 hmp (Nat.minFac_dvd m)
    have hsq : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
    have hltP : m.minFac < P := by
      by_contra hge
      have hge' : P ≤ m.minFac := by omega
      have := Nat.pow_le_pow_left hge' 2
      omega
    have hle := hnext m.minFac hmp hltP
    exact Finset.mem_coe.mpr (mem_wheels_below.mpr ⟨by omega, hmp, h5⟩)
  have hfiber : ∀ q ∈ wheels_below (p + 1),
      ((((Finset.Ioo (p ^ 2) (P ^ 2)).filter (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0)).filter
        (fun m => ¬ Nat.Prime m)).filter (fun m => Nat.minFac m = q)).card
        = first_blocked (p ^ 2) (P ^ 2) q := by
    intro q hq
    obtain ⟨hqlt, hqp, hq5⟩ := mem_wheels_below.mp hq
    unfold first_blocked
    apply congrArg Finset.card
    ext m
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨hI, h2, h3⟩, _⟩, hmf⟩
      refine ⟨hI, h2, h3, ?_, ?_⟩
      · rw [← hmf]
        exact Nat.minFac_dvd m
      · intro r hr hd
        obtain ⟨hrlt, hrp, _⟩ := mem_wheels_below.mp hr
        have := Nat.minFac_le_of_dvd hrp.two_le hd
        omega
    · rintro ⟨hI, h2, h3, hqd, hsm⟩
      have hI' := Finset.mem_Ioo.mp hI
      have hm1' : m ≠ 1 := by omega
      refine ⟨⟨⟨hI, h2, h3⟩, ?_⟩, ?_⟩
      · intro hpm
        have heq : q = m := (Nat.prime_dvd_prime_iff_eq hqp hpm).mp hqd
        omega
      · have hle : m.minFac ≤ q := Nat.minFac_le_of_dvd hqp.two_le hqd
        have hmp : m.minFac.Prime := Nat.minFac_prime hm1'
        have h5 : 5 ≤ m.minFac := five_le_of_prime_dvd h2 h3 hmp (Nat.minFac_dvd m)
        by_contra hne
        have hlt : m.minFac < q := by omega
        exact hsm m.minFac (mem_wheels_below.mpr ⟨hlt, hmp, h5⟩) (Nat.minFac_dvd m)
  have hb : (((Finset.Ioo (p ^ 2) (P ^ 2)).filter (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0)).filter
        (fun m => ¬ Nat.Prime m)).card
      = ∑ q ∈ wheels_below (p + 1), first_blocked (p ^ 2) (P ^ 2) q := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    exact Finset.sum_congr rfl hfiber
  rw [hslots, ← hsplit, ha, hb]

/-! ## The closed form of the cycling-only count -/

/-- The weight of a set of wheels: nothing when its product is longer than the
window; otherwise plus or minus the window length over three times the
product. -/
private noncomputable def wt (L : ℕ) (s : Finset ℕ) : ℝ :=
  if (∏ r ∈ s, r) ≤ L then
    (-1 : ℝ) ^ s.card * ((L : ℝ) / (3 * ((∏ r ∈ s, r : ℕ) : ℝ)))
  else 0

/-- Listing the nonempty sets of wheels by their largest member. -/
private theorem max_split (f : Finset ℕ → ℝ) (W : Finset ℕ) :
    ∑ q ∈ W, ∑ D ∈ (W.filter (fun r => r < q)).powerset, f (insert q D)
      = ∑ s ∈ W.powerset, f s - f ∅ := by
  induction W using Finset.induction_on_max with
  | empty => simp
  | insert a W hlt ih =>
    have haW : a ∉ W := fun h => lt_irrefl a (hlt a h)
    have hfa : (insert a W).filter (fun r => r < a) = W := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨h | h, hr⟩
        · omega
        · exact h
      · intro h
        exact ⟨Or.inr h, hlt r h⟩
    have hfq : ∀ q ∈ W, (insert a W).filter (fun r => r < q) = W.filter (fun r => r < q) := by
      intro q hq
      have hqa := hlt q hq
      ext r
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨h | h, hr⟩
        · omega
        · exact ⟨h, hr⟩
      · rintro ⟨h, hr⟩
        exact ⟨Or.inr h, hr⟩
    have hsum : ∑ q ∈ W, ∑ D ∈ ((insert a W).filter (fun r => r < q)).powerset, f (insert q D)
        = ∑ q ∈ W, ∑ D ∈ (W.filter (fun r => r < q)).powerset, f (insert q D) := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      rw [hfq q hq]
    rw [Finset.sum_insert haW, hfa, hsum, ih, Finset.sum_powerset_insert haW]
    ring

/-- The Möbius function of a product of distinct primes. -/
private theorem moebius_prod (s : Finset ℕ) (hs : ∀ r ∈ s, r.Prime) :
    ArithmeticFunction.moebius (∏ r ∈ s, r) = (-1 : ℤ) ^ s.card := by
  have h1 : ArithmeticFunction.moebius (∏ r ∈ s, r)
      = ∏ r ∈ s, ArithmeticFunction.moebius r :=
    ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime s hs
  have h2 : ∏ r ∈ s, ArithmeticFunction.moebius r = ∏ _r ∈ s, (-1 : ℤ) :=
    Finset.prod_congr rfl (fun r hr => ArithmeticFunction.moebius_apply_prime (hs r hr))
  rw [h1, h2, Finset.prod_const]

/-- The Möbius sum is the sum of the weights of the sets of wheels up to the
window length. -/
private theorem moebius_side (L : ℕ) :
    (L : ℝ) / 3 * moebius_sum L = ∑ s ∈ (wheels_below (L + 1)).powerset, wt L s := by
  unfold moebius_sum
  rw [Finset.mul_sum]
  have hsq : ∑ n ∈ ((Finset.Icc 1 L).filter (fun n => n % 2 ≠ 0 ∧ n % 3 ≠ 0)).filter
          (fun n => ArithmeticFunction.moebius n ≠ 0),
        (L : ℝ) / 3 * (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ))
      = ∑ n ∈ (Finset.Icc 1 L).filter (fun n => n % 2 ≠ 0 ∧ n % 3 ≠ 0),
        (L : ℝ) / 3 * (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)) := by
    refine Finset.sum_filter_of_ne (fun n _ hne => ?_)
    intro hmu
    apply hne
    rw [hmu]
    simp
  have hwt : ∑ s ∈ (wheels_below (L + 1)).powerset, wt L s
      = ∑ s ∈ (wheels_below (L + 1)).powerset.filter (fun s => (∏ r ∈ s, r) ≤ L),
          (-1 : ℝ) ^ s.card * ((L : ℝ) / (3 * ((∏ r ∈ s, r : ℕ) : ℝ))) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun s _ => rfl)
  rw [← hsq, hwt]
  refine Finset.sum_nbij' (fun n => n.primeFactors) (fun s => ∏ r ∈ s, r) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn1, hmu⟩ := Finset.mem_filter.mp hn
    obtain ⟨hI, h2, h3⟩ := Finset.mem_filter.mp hn1
    have hIcc := Finset.mem_Icc.mp hI
    have hsqf : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
    have hprod : ∏ r ∈ n.primeFactors, r = n := Nat.prod_primeFactors_of_squarefree hsqf
    have hle : (∏ r ∈ n.primeFactors, r) ≤ L := hprod.le.trans hIcc.2
    have hsub : n.primeFactors ⊆ wheels_below (L + 1) := by
      intro r hr
      have hrp := Nat.prime_of_mem_primeFactors hr
      have hrd := Nat.dvd_of_mem_primeFactors hr
      have hrle := Nat.le_of_mem_primeFactors hr
      exact mem_wheels_below.mpr ⟨by omega, hrp, five_le_of_prime_dvd h2 h3 hrp hrd⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hle⟩
  · intro s hs
    obtain ⟨hsP, hle⟩ := Finset.mem_filter.mp hs
    have hle' : (∏ r ∈ s, r) ≤ L := hle
    have hsQ := Finset.mem_powerset.mp hsP
    have hs5 : ∀ r ∈ s, r.Prime ∧ 5 ≤ r := fun r hr => (mem_wheels_below.mp (hsQ hr)).2
    have hpos : 0 < ∏ r ∈ s, r := Finset.prod_pos (fun r hr => (hs5 r hr).1.pos)
    have hmu : ArithmeticFunction.moebius (∏ r ∈ s, r) ≠ 0 := by
      rw [moebius_prod s (fun r hr => (hs5 r hr).1)]
      exact pow_ne_zero _ (by norm_num)
    have hc2 : (∏ r ∈ s, r) % 2 ≠ 0 := fun h =>
      not_dvd_prod hs5 Nat.prime_two (by norm_num) (Nat.dvd_of_mod_eq_zero h)
    have hc3 : (∏ r ∈ s, r) % 3 ≠ 0 := fun h =>
      not_dvd_prod hs5 Nat.prime_three (by norm_num) (Nat.dvd_of_mod_eq_zero h)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hle'⟩, hc2, hc3⟩, hmu⟩
  · intro n hn
    obtain ⟨_, hmu⟩ := Finset.mem_filter.mp hn
    have hsqf : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
    show ∏ r ∈ n.primeFactors, r = n
    exact Nat.prod_primeFactors_of_squarefree hsqf
  · intro s hs
    obtain ⟨hsP, _⟩ := Finset.mem_filter.mp hs
    have hsQ := Finset.mem_powerset.mp hsP
    show (∏ r ∈ s, r).primeFactors = s
    exact Nat.primeFactors_prod (fun r hr => (mem_wheels_below.mp (hsQ hr)).2.1)
  · intro n hn
    obtain ⟨_, hmu⟩ := Finset.mem_filter.mp hn
    have hsqf : Squarefree n := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
    have hprod : ∏ r ∈ n.primeFactors, r = n := Nat.prod_primeFactors_of_squarefree hsqf
    have hmu' : ArithmeticFunction.moebius n = (-1 : ℤ) ^ n.primeFactors.card := by
      have h := moebius_prod n.primeFactors (fun r hr => Nat.prime_of_mem_primeFactors hr)
      rw [hprod] at h
      exact h
    show (L : ℝ) / 3 * (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ))
      = (-1 : ℝ) ^ n.primeFactors.card
          * ((L : ℝ) / (3 * ((∏ r ∈ n.primeFactors, r : ℕ) : ℝ)))
    rw [hprod, hmu']
    push_cast
    ring

/-- A set of wheels up to the window length whose product fits in the window
is a set of wheels up to the base prime, or one single prime above it. -/
private theorem split_side (p L : ℕ) (hp3 : 3 ≤ p) (hpL : p ≤ L) (hL5 : L < 5 * (p + 1)) :
    ∑ s ∈ (wheels_below (L + 1)).powerset, wt L s
      = ∑ s ∈ (wheels_below (p + 1)).powerset, wt L s
          - (L : ℝ) / 3 * prime_reciprocals p L := by
  have hsub : wheels_below (p + 1) ⊆ wheels_below (L + 1) := by
    intro r hr
    have h := mem_wheels_below.mp hr
    exact mem_wheels_below.mpr ⟨by omega, h.2⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not ((wheels_below (L + 1)).powerset)
    (fun s => s ⊆ wheels_below (p + 1)) (wt L)
  have hA : (wheels_below (L + 1)).powerset.filter (fun s => s ⊆ wheels_below (p + 1))
      = (wheels_below (p + 1)).powerset := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hsub, h⟩⟩
  -- a single prime above the base
  have hsingle : ∀ r ∈ (Finset.Ioc p L).filter Nat.Prime,
      wt L {r} = -((L : ℝ) / 3 * ((1 : ℝ) / (r : ℝ))) := by
    intro r hr
    obtain ⟨hI, _⟩ := Finset.mem_filter.mp hr
    have hI' := Finset.mem_Ioc.mp hI
    have hps : ∏ x ∈ ({r} : Finset ℕ), x = r := Finset.prod_singleton (fun x => x) r
    unfold wt
    rw [hps, if_pos hI'.2, Finset.card_singleton, pow_one]
    ring
  have hB : ∑ s ∈ (wheels_below (L + 1)).powerset.filter
        (fun s => ¬ s ⊆ wheels_below (p + 1)), wt L s
      = ∑ r ∈ (Finset.Ioc p L).filter Nat.Prime, wt L {r} := by
    have himg : ∑ s ∈ ((Finset.Ioc p L).filter Nat.Prime).image (fun r => ({r} : Finset ℕ)),
          wt L s
        = ∑ s ∈ (wheels_below (L + 1)).powerset.filter
            (fun s => ¬ s ⊆ wheels_below (p + 1)), wt L s := by
      refine Finset.sum_subset ?_ ?_
      · intro s hs
        obtain ⟨r, hr, hrs⟩ := Finset.mem_image.mp hs
        obtain ⟨hI, hrp⟩ := Finset.mem_filter.mp hr
        have hI' := Finset.mem_Ioc.mp hI
        have hr4 : r ≠ 4 := by
          intro h
          rw [h] at hrp
          exact absurd hrp (by decide)
        have hrw : r ∈ wheels_below (L + 1) := mem_wheels_below.mpr ⟨by omega, hrp, by omega⟩
        have hrs' : ({r} : Finset ℕ) = s := hrs
        rw [← hrs']
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_singleton.mp hx]
          exact hrw
        · intro hsubW
          have h := mem_wheels_below.mp (hsubW (Finset.mem_singleton_self r))
          omega
      · intro s hs hnot
        obtain ⟨hsP, hns⟩ := Finset.mem_filter.mp hs
        have hsQ := Finset.mem_powerset.mp hsP
        obtain ⟨r, hrs, hrW⟩ := Finset.not_subset.mp hns
        have hrQ := mem_wheels_below.mp (hsQ hrs)
        have hrp : p < r := by
          by_contra h
          exact hrW (mem_wheels_below.mpr ⟨by omega, hrQ.2⟩)
        have hne : s ≠ {r} := by
          intro h
          apply hnot
          rw [h]
          exact Finset.mem_image.mpr
            ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hrp, by omega⟩, hrQ.2.1⟩, rfl⟩
        obtain ⟨x, hxs, hxr⟩ : ∃ x ∈ s, x ≠ r := by
          by_contra hall
          apply hne
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hrs, fun x hx => ?_⟩
          by_contra hxr
          exact hall ⟨x, hx, hxr⟩
        have hx5 := (mem_wheels_below.mp (hsQ hxs)).2.2
        have hxe : x ∈ s.erase r := Finset.mem_erase.mpr ⟨hxr, hxs⟩
        have hprod : r * ∏ y ∈ s.erase r, y = ∏ y ∈ s, y :=
          Finset.mul_prod_erase s (fun y => y) hrs
        have hpos : 0 < ∏ y ∈ s.erase r, y :=
          Finset.prod_pos (fun y hy =>
            (mem_wheels_below.mp (hsQ (Finset.mem_of_mem_erase hy))).2.1.pos)
        have hxd : x ∣ ∏ y ∈ s.erase r, y := Finset.dvd_prod_of_mem (fun y => y) hxe
        have hxle : x ≤ ∏ y ∈ s.erase r, y := Nat.le_of_dvd hpos hxd
        have hbig : (p + 1) * 5 ≤ r * ∏ y ∈ s.erase r, y :=
          Nat.mul_le_mul (by omega) (hx5.trans hxle)
        have hgt : ¬ (∏ y ∈ s, y) ≤ L := by
          rw [← hprod]
          omega
        unfold wt
        exact if_neg hgt
    rw [← himg]
    exact Finset.sum_image (fun a _ b _ hab => Finset.singleton_injective hab)
  have hU : ∑ r ∈ (Finset.Ioc p L).filter Nat.Prime, wt L {r}
      = -((L : ℝ) / 3 * prime_reciprocals p L) := by
    unfold prime_reciprocals
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hsingle
  rw [← hsplit, hA, hB, hU]
  ring

theorem cycling_blocked_closed_form_holds : cycling_blocked_closed_form := by
  intro p L hp3 hpL hL5
  -- the cycling-only count, written with the weights of the nonempty sets
  have hterm : ∀ q ∈ wheels_below (p + 1), ∀ D ∈ (wheels_below q).powerset,
      (if q * (∏ r ∈ D, r) ≤ L then
          (-1 : ℝ) ^ D.card * ((L : ℝ) / (3 * ((q * ∏ r ∈ D, r : ℕ) : ℝ)))
        else 0)
        = -wt L (insert q D) := by
    intro q _ D hD
    have hqD : q ∉ D :=
      fun h => lt_irrefl q (mem_wheels_below.mp (Finset.mem_powerset.mp hD h)).1
    have hins : ∏ r ∈ insert q D, r = q * ∏ r ∈ D, r := Finset.prod_insert hqD
    unfold wt
    rw [hins, Finset.card_insert_of_notMem hqD]
    by_cases hc : q * (∏ r ∈ D, r) ≤ L
    · simp only [if_pos hc]
      ring
    · simp only [if_neg hc, neg_zero]
  have hfil : ∀ q ∈ wheels_below (p + 1),
      wheels_below q = (wheels_below (p + 1)).filter (fun r => r < q) := by
    intro q hq
    have hq' := (mem_wheels_below.mp hq).1
    ext r
    rw [Finset.mem_filter, mem_wheels_below, mem_wheels_below]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h1⟩
      exact ⟨h1, h2⟩
  have hsum : cycling_blocked p L
      = ∑ q ∈ wheels_below (p + 1),
          ∑ D ∈ ((wheels_below (p + 1)).filter (fun r => r < q)).powerset,
            -wt L (insert q D) := by
    unfold cycling_blocked
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [← hfil q hq]
    exact Finset.sum_congr rfl (fun D hD => hterm q hq D hD)
  have hms : ∑ q ∈ wheels_below (p + 1),
        ∑ D ∈ ((wheels_below (p + 1)).filter (fun r => r < q)).powerset,
          -wt L (insert q D)
      = ∑ s ∈ (wheels_below (p + 1)).powerset, -wt L s - -wt L ∅ :=
    max_split (fun s => -wt L s) (wheels_below (p + 1))
  have hempty : wt L ∅ = (L : ℝ) / 3 := by
    have hpe : ∏ r ∈ (∅ : Finset ℕ), r = 1 := Finset.prod_empty
    have h1L : (1 : ℕ) ≤ L := by omega
    unfold wt
    rw [hpe, if_pos h1L, Finset.card_empty, pow_zero, Nat.cast_one]
    ring
  have h1 : cycling_blocked p L
      = (L : ℝ) / 3 - ∑ s ∈ (wheels_below (p + 1)).powerset, wt L s := by
    rw [hsum, hms, Finset.sum_neg_distrib, hempty]
    ring
  have h2 := moebius_side L
  have h3 := split_side p L hp3 hpL hL5
  have h4 : ∑ s ∈ (wheels_below (p + 1)).powerset, wt L s
      = (L : ℝ) / 3 * moebius_sum L + (L : ℝ) / 3 * prime_reciprocals p L := by
    linarith
  rw [h1, h4]
  ring

/-- Step: the twin prediction's closed form from the closed form of the
cycling-only count. -/
theorem twin_prediction_closed_form_step (h : cycling_blocked_closed_form) :
    twin_prediction_closed_form := by
  intro p hp5
  unfold twin_prediction
  rw [h p (4 * p + 4) (by omega) (by omega) (by omega)]
  ring

#print axioms window_exact_count_holds
#print axioms window_prime_count_holds
#print axioms cycling_blocked_closed_form_holds
#print axioms twin_prediction_closed_form_step

end RNS.BrocardPrediction
