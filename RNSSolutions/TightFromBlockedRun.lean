/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.TightFromBlockedRun.Conclusions
import Mathlib.Tactic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.Interval

/-!
# Proofs for TightFromBlockedRun

Draft (2026-11-23).

* `near_of_small`: a signed distance of at most one part is near.
* Dirichlet: the remainders of `j * k` for `j = 0, …, n - 1`, sorted into `n`
  equal boxes of the lap, together with the end of the lap put in the last box:
  two share a box, and their difference is a consecutive speed at most one part
  from the start.
* One-step replacement: write the old runner's position as a whole number of
  laps `a` plus a signed remainder `e`. If `a` shares a prime wheel with `r`,
  the runner `r / p` is near. Otherwise the inverse of `a` for `r` gives a speed
  `b` in the right range, and `b * k` is a whole number of laps plus
  `(M ± b * e) / r`, which the range bounds keep within one part.
* Tightness: check the two conditions from the blocked run.
-/

namespace RNS.TightFromBlockedRun

open RNS.PileUpLock

theorem near_congr (n M : ℕ) (y y' : ℤ) (h : y % (M : ℤ) = y' % (M : ℤ)) :
    near n M y ↔ near n M y' := by
  unfold near
  rw [h]

theorem near_of_small (n M : ℕ) (z : ℤ) (hn : 2 ≤ n) (hM : 0 < M)
    (h1 : (n : ℤ) * z ≤ M) (h2 : -(M : ℤ) ≤ (n : ℤ) * z) : near n M z := by
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  unfold near
  rcases le_or_gt 0 z with hz | hz
  · left
    have hzM : z < M := by nlinarith
    rw [Int.emod_eq_of_lt hz hzM]
    exact h1
  · right
    have hzM : -(M : ℤ) < z := by nlinarith
    have hmod : z % (M : ℤ) = z + M := by
      rw [← Int.add_mul_emod_self_left z M 1, mul_one]
      exact Int.emod_eq_of_lt (by linarith) (by linarith)
    rw [hmod]
    linarith

theorem consecutive_covered_holds : consecutive_covered := by
  intro n hn M hM k
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  set x : ℕ → ℤ := fun j => ((j : ℤ) * k) % (M : ℤ) with hx
  have hx0 : ∀ j, 0 ≤ x j := fun j => Int.emod_nonneg _ (ne_of_gt hM')
  have hx1 : ∀ j, x j < M := fun j => Int.emod_lt_of_pos _ hM'
  set f : ℕ → ℤ := fun j => if j < n then ((n : ℤ) * x j) / (M : ℤ) else (n : ℤ) - 1 with hf
  have hmaps : Set.MapsTo f (Finset.range (n + 1) : Set ℕ) (Finset.Ico (0 : ℤ) n : Set ℤ) := by
    intro j _
    rw [Finset.mem_coe, Finset.mem_Ico]
    by_cases hj : j < n
    · simp only [hf, hj, ↓reduceIte]
      refine ⟨Int.ediv_nonneg (by nlinarith [hx0 j]) hM'.le, ?_⟩
      apply Int.ediv_lt_of_lt_mul hM'
      nlinarith [hx1 j]
    · simp only [hf, hj, ↓reduceIte]
      constructor <;> linarith
  have hcard : (Finset.Ico (0 : ℤ) n).card < (Finset.range (n + 1)).card := by
    rw [Int.card_Ico, Finset.card_range]
    simp
  obtain ⟨i, hi, j, hj, hij, hfij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_range] at hi hj
  -- the box bounds
  have box : ∀ l, l < n → (f l) * M ≤ (n : ℤ) * x l ∧ (n : ℤ) * x l < (f l + 1) * M := by
    intro l hl
    simp only [hf, hl, ↓reduceIte]
    exact ⟨Int.ediv_mul_le _ (ne_of_gt hM'), Int.lt_ediv_add_one_mul_self _ hM'⟩
  -- two points in one box give a consecutive speed near the start
  have key : ∀ a b : ℕ, a < b → b ≤ n → f a = f b →
      ∃ v ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1), near n M (v * k) := by
    intro a b hab hb hfab
    by_cases hbn : b < n
    · obtain ⟨ha1, ha2⟩ := box a (by omega)
      obtain ⟨hb1, hb2⟩ := box b hbn
      rw [hfab] at ha1 ha2
      refine ⟨(b : ℤ) - a, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        constructor
        · have : (a : ℤ) < b := by exact_mod_cast hab
          linarith
        · have : (b : ℤ) < n := by exact_mod_cast hbn
          linarith
      · have hcong : (((b : ℤ) - a) * k) % (M : ℤ) = (x b - x a) % (M : ℤ) := by
          rw [sub_mul, Int.sub_emod]
        rw [near_congr n M _ _ hcong]
        have e1 : (f b + 1) * (M : ℤ) = f b * M + M := by ring
        rw [e1] at ha2 hb2
        apply near_of_small n M _ hn hM
        · linarith
        · linarith
    · have hbn' : b = n := by omega
      have hfb : f b = (n : ℤ) - 1 := by simp [hf, hbn']
      have ha0 : a ≠ 0 := by
        rintro rfl
        have h0 : f 0 = 0 := by simp [hf, hx, show 0 < n by omega]
        rw [h0, hfb] at hfab
        linarith
      obtain ⟨ha1, _⟩ := box a (by omega)
      rw [hfab, hfb] at ha1
      refine ⟨(a : ℤ), ?_, ?_⟩
      · rw [Finset.mem_Icc]
        constructor
        · have : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
          exact_mod_cast this
        · have : (a : ℤ) < n := by exact_mod_cast (show a < n by omega)
          linarith
      · unfold near
        right
        have : (x a) = ((a : ℤ) * k) % (M : ℤ) := rfl
        rw [← this]
        linarith
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i j h (by omega) hfij
  · exact key j i h (by omega) hfij.symm

theorem blocked_run_short_holds : blocked_run_short := by
  intro r lo hi hr hrun
  by_contra hlong
  have hlong' := not_le.mp hlong
  have hr' : (0 : ℤ) < r := by omega
  set b : ℤ := lo + (1 - lo) % r with hb
  have h0 : 0 ≤ (1 - lo) % r := Int.emod_nonneg _ (ne_of_gt hr')
  have h1 : (1 - lo) % r < r := Int.emod_lt_of_pos _ hr'
  apply hrun b (by linarith) (by linarith)
  rw [← Int.isCoprime_iff_gcd_eq_one]
  have hdecomp := Int.emod_add_ediv_mul (1 - lo) r
  refine ⟨(1 - lo) / r, 1, ?_⟩
  rw [hb]
  linarith

theorem one_step_replacement_holds : one_step_replacement := by
  intro n X r m hn hr1 hrn hm hX hpr hq M hM k
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hr0 : (0 : ℤ) < r := by omega
  obtain ⟨x, hx, hnear⟩ := hX M hM k
  by_cases hxr : x = r
  swap
  · exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxr, hx⟩), hnear⟩
  rw [hxr] at hnear
  by_cases hmr : near n M (m * r * k)
  · exact ⟨m * r, Finset.mem_insert_self _ _, hmr⟩
  -- the old runner: a whole number of laps plus a signed remainder
  obtain ⟨a, e, hy, he1, he2⟩ : ∃ a e : ℤ, r * k = a * M + e ∧ (n : ℤ) * e ≤ M ∧
      -(M : ℤ) ≤ (n : ℤ) * e := by
    have hd := Int.emod_add_ediv_mul (r * k) M
    have hρ0 : 0 ≤ (r * k) % (M : ℤ) := Int.emod_nonneg _ (ne_of_gt hM')
    have hρ1 : (r * k) % (M : ℤ) < M := Int.emod_lt_of_pos _ hM'
    rcases hnear with h | h
    · exact ⟨(r * k) / M, (r * k) % M, by linarith, h, by nlinarith⟩
    · refine ⟨(r * k) / M + 1, (r * k) % M - M, ?_, by nlinarith, by nlinarith⟩
      linarith [show ((r * k) / (M : ℤ) + 1) * M = (r * k) / M * M + M by ring]
  -- the sped-up runner is not near, so m * e is more than one part
  have hbig : (M : ℤ) < (n : ℤ) * (m * e) ∨ (n : ℤ) * (m * e) < -(M : ℤ) := by
    by_contra hsmall
    rw [not_or, not_lt, not_lt] at hsmall
    apply hmr
    have hcong : (m * r * k) % (M : ℤ) = (m * e) % (M : ℤ) := by
      rw [show m * r * k = m * e + M * (m * a) by rw [mul_assoc, hy]; ring]
      exact Int.add_mul_emod_self_left _ _ _
    rw [near_congr n M _ _ hcong]
    exact near_of_small n M _ hn hM hsmall.1 hsmall.2
  by_cases hg : Int.gcd a r = 1
  swap
  · -- a prime wheel of r divides a: the runner r / p is near
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
    have hpd' : (p : ℤ) ∣ (Int.gcd a r : ℤ) := Int.natCast_dvd_natCast.mpr hpd
    have hpa : (p : ℤ) ∣ a := dvd_trans hpd' (Int.gcd_dvd_left a r)
    have hpr' : (p : ℤ) ∣ r := dvd_trans hpd' (Int.gcd_dvd_right a r)
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    obtain ⟨w, hw⟩ := hpr'
    obtain ⟨a', ha'⟩ := hpa
    have hwmem := hpr p hp ⟨w, hw⟩
    have hrw : r / (p : ℤ) = w := by rw [hw]; exact Int.mul_ediv_cancel_left w (by omega)
    rw [hrw] at hwmem
    refine ⟨w, hwmem, ?_⟩
    set e' : ℤ := w * k - a' * M with he'
    have hee : e = (p : ℤ) * e' := by
      rw [he']
      have : (p : ℤ) * (w * k) = (p : ℤ) * a' * M + e := by rw [← mul_assoc, ← hw, ← ha']; exact hy
      linear_combination -this
    have hcong : (w * k) % (M : ℤ) = e' % (M : ℤ) := by
      rw [show w * k = e' + M * a' by rw [he']; ring]
      exact Int.add_mul_emod_self_left _ _ _
    rw [near_congr n M _ _ hcong]
    have hz : (n : ℤ) * e = (p : ℤ) * ((n : ℤ) * e') := by rw [hee]; ring
    rcases le_or_gt 0 ((n : ℤ) * e') with hpos | hneg
    · apply near_of_small n M _ hn hM
      · nlinarith
      · linarith
    · apply near_of_small n M _ hn hM
      · linarith
      · nlinarith
  · -- a shares no factor with r: use the inverse of a for r
    obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hg
    have hrn' : (0 : ℤ) ≤ (n : ℤ) - r := by linarith
    rcases lt_trichotomy e 0 with hneg | hzero | hpos
    · -- e < 0: the speed b with a * b leaving remainder 1
      have hmne : (n : ℤ) * (m * e) < -(M : ℤ) := by
        have hme : m * e < 0 := mul_neg_of_pos_of_neg (by omega) hneg
        have hnme : (n : ℤ) * (m * e) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hme.le
        rcases hbig with h | h
        · exfalso; linarith
        · exact h
      obtain ⟨b, hbmem, hb2, hb1, c, hc⟩ := hq u ⟨a, v, by linarith⟩
      have hab : a * b = 1 + r * (a * c - v) := by linear_combination a * hc + huv
      have hb0 : 0 ≤ b := by nlinarith
      refine ⟨b, hbmem, ?_⟩
      have hthis : r * (b * k) = b * (a * M + e) := by rw [← hy]; ring
      obtain ⟨z, hz⟩ : r ∣ (M : ℤ) + b * e :=
        ⟨b * k - (a * c - v) * M, by linear_combination -hthis - (M : ℤ) * hab⟩
      have hbk : b * k = z + M * (a * c - v) := by
        apply mul_left_cancel₀ (ne_of_gt hr0)
        linear_combination hthis + (M : ℤ) * hab + hz
      have hcong : (b * k) % (M : ℤ) = z % (M : ℤ) := by
        rw [hbk]; exact Int.add_mul_emod_self_left _ _ _
      rw [near_congr n M _ _ hcong]
      have hrz' : r * ((n : ℤ) * z) = (n : ℤ) * M + (n : ℤ) * b * e := by
        rw [show r * ((n : ℤ) * z) = (n : ℤ) * (r * z) by ring, ← hz]; ring
      have h1 : b * ((n : ℤ) * e) ≤ (m * ((n : ℤ) - r)) * ((n : ℤ) * e) :=
        mul_le_mul_of_nonpos_right hb2 (by nlinarith)
      have h2 : ((n : ℤ) - r) * ((n : ℤ) * (m * e)) ≤ ((n : ℤ) - r) * (-(M : ℤ)) :=
        mul_le_mul_of_nonneg_left hmne.le hrn'
      have h3 : b * (-((n : ℤ) * e)) ≤ ((n : ℤ) + r) * M :=
        mul_le_mul hb1 (by linarith) (by nlinarith) (by linarith)
      apply near_of_small n M _ hn hM
      · apply le_of_mul_le_mul_left _ hr0
        linarith
      · apply le_of_mul_le_mul_left _ hr0
        linarith
    · exfalso
      rw [hzero, mul_zero, mul_zero] at hbig
      rcases hbig with h | h <;> linarith
    · -- e > 0: the speed b with a * b leaving remainder -1
      have hmne : (M : ℤ) < (n : ℤ) * (m * e) := by
        have hme : 0 < m * e := mul_pos (by omega) hpos
        have hnme : 0 ≤ (n : ℤ) * (m * e) := mul_nonneg (by positivity) hme.le
        rcases hbig with h | h
        · exact h
        · exfalso; linarith
      obtain ⟨b, hbmem, hb2, hb1, c, hc⟩ := hq (-u) ⟨-a, v, by linarith⟩
      have hab : a * b = -1 + r * (a * c + v) := by linear_combination a * hc - huv
      have hb0 : 0 ≤ b := by nlinarith
      refine ⟨b, hbmem, ?_⟩
      have hthis : r * (b * k) = b * (a * M + e) := by rw [← hy]; ring
      obtain ⟨z, hz⟩ : r ∣ b * e - (M : ℤ) :=
        ⟨b * k - (a * c + v) * M, by linear_combination -hthis - (M : ℤ) * hab⟩
      have hbk : b * k = z + M * (a * c + v) := by
        apply mul_left_cancel₀ (ne_of_gt hr0)
        linear_combination hthis + (M : ℤ) * hab + hz
      have hcong : (b * k) % (M : ℤ) = z % (M : ℤ) := by
        rw [hbk]; exact Int.add_mul_emod_self_left _ _ _
      rw [near_congr n M _ _ hcong]
      have hrz' : r * ((n : ℤ) * z) = (n : ℤ) * b * e - (n : ℤ) * M := by
        rw [show r * ((n : ℤ) * z) = (n : ℤ) * (r * z) by ring, ← hz]; ring
      have h1 : b * ((n : ℤ) * e) ≤ ((n : ℤ) + r) * M :=
        mul_le_mul hb1 he1 (by nlinarith) (by linarith)
      have h2 : (m * ((n : ℤ) - r)) * ((n : ℤ) * e) ≤ b * ((n : ℤ) * e) :=
        mul_le_mul_of_nonneg_right hb2 (by nlinarith)
      have h3 : ((n : ℤ) - r) * (M : ℤ) ≤ ((n : ℤ) - r) * ((n : ℤ) * (m * e)) :=
        mul_le_mul_of_nonneg_left hmne.le hrn'
      apply near_of_small n M _ hn hM
      · apply le_of_mul_le_mul_left _ hr0
        linarith
      · apply le_of_mul_le_mul_left _ hr0
        linarith

theorem single_acceleration_tight_step (hF : RNS.FieldSizeTimes.field_size_far_iff) :
    single_acceleration_tight := by
  intro n r m hn hr1 hrn hm hrun
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  -- r is at least 2: for r = 1 nothing is blocked
  have hr2 : 2 ≤ r := by
    by_contra hlt
    have hr : r = 1 := by omega
    apply hrun ((n : ℤ) - r) le_rfl (by rw [hr]; nlinarith)
    rw [hr, ← Int.isCoprime_iff_gcd_eq_one]
    exact isCoprime_one_left
  -- the blocked run is short, so m * (n - r) < n and m * r > n - 1
  have hshort := blocked_run_short_holds r _ _ hr1 hrun
  have hmn : m * ((n : ℤ) - r) ≤ (n : ℤ) - 1 := by linarith
  have hpos : 0 < m * ((n : ℤ) - r) := mul_pos (by omega) (by omega)
  have h2n : 2 * (n : ℤ) ≤ m * n := by nlinarith
  have hmr : (n : ℤ) - 1 < m * r := by linarith
  -- the size of the set
  have hrmem : r ∈ Finset.Icc (1 : ℤ) ((n : ℤ) - 1) := Finset.mem_Icc.mpr ⟨hr1, hrn⟩
  have hmrnot : m * r ∉ (Finset.Icc (1 : ℤ) ((n : ℤ) - 1)).erase r := by
    intro h
    have := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase h)).2
    linarith
  have hcard : (accelerated n r m).card = n - 1 := by
    unfold accelerated
    rw [Finset.card_insert_of_notMem hmrnot, Finset.card_erase_of_mem hrmem, Int.card_Icc]
    have h := Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n : ℤ) - 1 + 1 - 1 by omega)
    have h2 : 1 ≤ ((n : ℤ) - 1 + 1 - 1).toNat := by omega
    omega
  refine ⟨hcard, ?_, ?_⟩
  · -- lonely at the time 1 / n
    refine ⟨by omega, fun v hv => ?_⟩
    rw [hcard, Nat.sub_add_cancel (by omega)]
    rw [hF n (v * 1) (by omega), mul_one]
    intro hdiv
    unfold accelerated at hv
    rcases Finset.mem_insert.mp hv with h | h
    · rw [h] at hdiv
      have h2 : (n : ℤ) ∣ m * ((n : ℤ) - r) := by
        have : m * ((n : ℤ) - r) = (n : ℤ) * m - m * r := by ring
        rw [this]
        exact dvd_sub (dvd_mul_right _ _) hdiv
      have := Int.le_of_dvd hpos h2
      linarith
    · have hvI := Finset.mem_Icc.mp (Finset.mem_of_mem_erase h)
      have := Int.le_of_dvd (by linarith) hdiv
      linarith
  · -- never strictly lonely, by one replacement
    apply one_step_replacement_holds n _ r m hn hr1 (by linarith) hm (consecutive_covered_holds n hn)
    · -- r / p is an unchanged speed
      intro p hp hpr
      obtain ⟨w, hw⟩ := hpr
      have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
      have hrw : r / (p : ℤ) = w := by rw [hw]; exact Int.mul_ediv_cancel_left w (by omega)
      rw [hrw]
      have hw1 : 1 ≤ w := by
        by_contra h
        have h' := not_le.mp h
        nlinarith
      have hwr : w < r := by nlinarith
      apply Finset.mem_insert_of_mem
      exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨hw1, by omega⟩⟩
    · -- each coprime remainder has an unchanged speed from n - r to n - 1
      intro q hq
      have hr0 : (0 : ℤ) < r := by omega
      set b : ℤ := ((n : ℤ) - r) + (q - ((n : ℤ) - r)) % r with hb
      have h0 : 0 ≤ (q - ((n : ℤ) - r)) % r := Int.emod_nonneg _ (ne_of_gt hr0)
      have h1 : (q - ((n : ℤ) - r)) % r < r := Int.emod_lt_of_pos _ hr0
      have hdecomp := Int.emod_add_ediv_mul (q - ((n : ℤ) - r)) r
      have hbq : b - q = r * (-((q - ((n : ℤ) - r)) / r)) := by rw [hb]; linarith
      have hcop : IsCoprime b r := by
        obtain ⟨s, t, hst⟩ := hq
        refine ⟨s, t + s * ((q - ((n : ℤ) - r)) / r), ?_⟩
        have : b = q + r * (-((q - ((n : ℤ) - r)) / r)) := by linarith
        rw [this]
        linear_combination hst
      have hbig : m * ((n : ℤ) - r) ≤ b := by
        by_contra hlt
        have hlt' := not_le.mp hlt
        exact hrun b (by linarith) (by linarith) (Int.isCoprime_iff_gcd_eq_one.mp hcop.symm)
      have hbr : b ≠ r := by
        intro h
        rw [h] at hcop
        rcases Int.isUnit_iff.mp (isCoprime_self.mp hcop) with h1 | h1 <;> omega
      refine ⟨b, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hbr, Finset.mem_Icc.mpr
        ⟨by linarith, by linarith⟩⟩), hbig, by linarith, ⟨-((q - ((n : ℤ) - r)) / r), hbq⟩⟩

end RNS.TightFromBlockedRun

#print axioms RNS.TightFromBlockedRun.consecutive_covered_holds
#print axioms RNS.TightFromBlockedRun.blocked_run_short_holds
#print axioms RNS.TightFromBlockedRun.one_step_replacement_holds
#print axioms RNS.TightFromBlockedRun.single_acceleration_tight_step
