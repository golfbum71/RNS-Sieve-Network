/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.GapCertificate.Conclusions
import Mathlib.Tactic.NormNum.Prime    -- `norm_num` deciding small numbers prime or not
import Mathlib.Tactic.IntervalCases    -- the fourteen cases below 14

/-!
# Proofs for GapCertificate

Imports claims only, never other nodes' proofs. Rests on no other node.

Built clean by `lake build RNSSolutions` on 2026-11-05; `#print axioms` shows only
the standard three.

Idea. Survivorship repeats with the cycle, so a gap occurring anywhere also
occurs starting inside the first cycle (`gapM_iff_exists_lt`). The first cycle
is then checked by a Boolean program that the Lean kernel evaluates
(`decide +kernel`), which adds no axiom beyond the standard three;
`native_decide` is not used. The 30030 starting positions are checked in 30
blocks of 1001. Each gap that does occur gets an explicit starting survivor,
found by direct computation and checked by the kernel.

Evenness: with 2 among the wheels every survivor is odd, so the distance
between two survivors is even.
-/

namespace RNS.GapCertificate

/-! ## Gaps for an arbitrary cycle -/

/-- `gapM M g`: the distance `g` occurs between consecutive survivors of the
cycle `M`. -/
private def gapM (M g : Nat) : Prop :=
  ∃ x : Nat, Nat.gcd x M = 1 ∧ Nat.gcd (x + g) M = 1 ∧
    ∀ j : Nat, 0 < j → j < g → Nat.gcd (x + j) M ≠ 1

/-! ## Boolean checkers (evaluated by the kernel) -/

/-- `x + 1, …, x + k` are all blocked by the cycle `M`. -/
private def blockedUpTo (M x : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => decide (Nat.gcd (x + (k + 1)) M ≠ 1) && blockedUpTo M x k

/-- A gap of size `g` starts at the survivor `x`. -/
private def gapAt (M x g : Nat) : Bool :=
  decide (Nat.gcd x M = 1) && decide (Nat.gcd (x + g) M = 1) &&
    blockedUpTo M x (g - 1)

/-- No gap of size `g` starts at any of the `len` positions from `lo` on. -/
private def noGapIn (M g lo : Nat) : Nat → Bool
  | 0 => true
  | len + 1 => decide (gapAt M (lo + len) g = false) && noGapIn M g lo len

/-- No gap of size `g` starts in the first `n` blocks of width `B`. -/
private def noGapBlocks (M g B : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => noGapIn M g (n * B) B && noGapBlocks M g B n

/-! ## Soundness of the checkers -/

private theorem blockedUpTo_iff (M x k : Nat) :
    blockedUpTo M x k = true ↔ ∀ j : Nat, 0 < j → j ≤ k → Nat.gcd (x + j) M ≠ 1 := by
  induction k with
  | zero =>
    constructor
    · intro _ j hj hjk
      exfalso
      omega
    · intro _
      rfl
  | succ k ih =>
    simp only [blockedUpTo, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hlast, hrest⟩ j hj hjk
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact hrest j hj (by omega)
      · have hj' : j = k + 1 := by omega
        subst hj'
        exact hlast
    · intro h
      exact ⟨h (k + 1) (by omega) (Nat.le_refl _), fun j hj hjk => h j hj (by omega)⟩

private theorem gapAt_iff (M x g : Nat) :
    gapAt M x g = true ↔
      (Nat.gcd x M = 1 ∧ Nat.gcd (x + g) M = 1 ∧
        ∀ j : Nat, 0 < j → j < g → Nat.gcd (x + j) M ≠ 1) := by
  simp only [gapAt, Bool.and_eq_true, decide_eq_true_eq, blockedUpTo_iff]
  constructor
  · rintro ⟨⟨h0, hg⟩, hb⟩
    exact ⟨h0, hg, fun j hj hjg => hb j hj (by omega)⟩
  · rintro ⟨h0, hg, hb⟩
    exact ⟨⟨h0, hg⟩, fun j hj hjg => hb j hj (by omega)⟩

private theorem noGapIn_spec (M g lo len : Nat) (h : noGapIn M g lo len = true) :
    ∀ x : Nat, lo ≤ x → x < lo + len → gapAt M x g = false := by
  induction len with
  | zero =>
    intro x h1 h2
    exfalso
    omega
  | succ len ih =>
    simp only [noGapIn, Bool.and_eq_true, decide_eq_true_eq] at h
    intro x h1 h2
    rcases Nat.lt_or_ge x (lo + len) with hx | hx
    · exact ih h.2 x h1 hx
    · have hx' : x = lo + len := by omega
      rw [hx']
      exact h.1

private theorem noGapBlocks_spec (M g B n : Nat) (h : noGapBlocks M g B n = true) :
    ∀ x : Nat, x < n * B → gapAt M x g = false := by
  induction n with
  | zero =>
    intro x hx
    exfalso
    rw [Nat.zero_mul] at hx
    exact Nat.not_lt_zero x hx
  | succ n ih =>
    simp only [noGapBlocks, Bool.and_eq_true] at h
    intro x hx
    rw [Nat.add_mul, Nat.one_mul] at hx
    rcases Nat.lt_or_ge x (n * B) with h1 | h1
    · exact ih h.2 x h1
    · exact noGapIn_spec M g (n * B) B h.1 x h1 hx

private theorem gapM_of_witness (M g x : Nat) (h : gapAt M x g = true) : gapM M g := by
  unfold gapM
  exact ⟨x, (gapAt_iff M x g).mp h⟩

/-! ## Sliding into the first cycle -/

/-- Survivorship depends only on the position in the cycle. -/
private theorem gcd_mod_self (M x : Nat) : Nat.gcd x M = Nat.gcd (x % M) M := by
  rw [Nat.gcd_comm x M, Nat.gcd_rec M x]

/-- Moving by whole cycles does not change survivorship. -/
private theorem gcd_add_mul_self' (M a q : Nat) : Nat.gcd (a + M * q) M = Nat.gcd a M := by
  rw [gcd_mod_self M (a + M * q), Nat.add_mul_mod_self_left, ← gcd_mod_self M a]

private theorem gcd_shift_mod (M x j : Nat) :
    Nat.gcd (x + j) M = Nat.gcd (x % M + j) M := by
  have h : x + j = (x % M + j) + M * (x / M) := by
    have := Nat.mod_add_div x M
    omega
  rw [h, gcd_add_mul_self']

/-- A gap occurs somewhere iff it starts at a survivor inside the first cycle. -/
private theorem gapM_iff_exists_lt (M g : Nat) (hM : 0 < M) :
    gapM M g ↔ ∃ x : Nat, x < M ∧ gapAt M x g = true := by
  unfold gapM
  constructor
  · rintro ⟨x, h0, hg, hb⟩
    refine ⟨x % M, Nat.mod_lt x hM, ?_⟩
    rw [gapAt_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [← gcd_mod_self]
      exact h0
    · rw [← gcd_shift_mod]
      exact hg
    · intro j hj hjg
      rw [← gcd_shift_mod]
      exact hb j hj hjg
  · rintro ⟨x, -, hx⟩
    exact ⟨x, (gapAt_iff M x g).mp hx⟩

/-! ## The cycle of the wheels up to 13 -/

private theorem active_primes_fourteen : active_primes 14 = {2, 3, 5, 7, 11, 13} := by
  ext x
  simp only [active_primes, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hp⟩
    interval_cases x <;> first | decide | (norm_num at hp)
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num

private theorem primorial_modulus_fourteen : primorial_modulus 14 = 30030 := by
  unfold primorial_modulus
  rw [active_primes_fourteen]
  decide

private theorem survivor_gap_fourteen (g : Nat) : survivor_gap 14 g ↔ gapM 30030 g := by
  unfold survivor_gap gapM
  rw [primorial_modulus_fourteen]

/-! ## Claims -/

theorem survivor_gaps_even_holds : survivor_gaps_even := by
  intro limit g hlimit hgap
  unfold survivor_gap at hgap
  obtain ⟨x, hx, hxg, -⟩ := hgap
  have h2 : 2 ∣ primorial_modulus limit := by
    unfold primorial_modulus
    exact Finset.dvd_prod_of_mem id
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩)
  have hodd : ∀ y : Nat, Nat.gcd y (primorial_modulus limit) = 1 → ¬ 2 ∣ y := by
    intro y hy h2y
    have h21 := Nat.dvd_gcd h2y h2
    rw [hy] at h21
    omega
  have h1 := hodd x hx
  have h3 := hodd (x + g) hxg
  omega

theorem survivor_gaps_30030_miss_20_holds : survivor_gaps_30030_miss_20 := by
  intro hgap
  rw [survivor_gap_fourteen, gapM_iff_exists_lt 30030 20 (by norm_num)] at hgap
  obtain ⟨x, hx, h⟩ := hgap
  have hno : gapAt 30030 x 20 = false :=
    noGapBlocks_spec 30030 20 1001 30 (by decide +kernel) x (by omega)
  rw [hno] at h
  exact absurd h (by decide)

theorem survivor_gaps_30030_present_holds : survivor_gaps_30030_present := by
  intro g hg
  rw [survivor_gap_fourteen]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact gapM_of_witness 30030 2 17 (by decide +kernel)
  · exact gapM_of_witness 30030 4 19 (by decide +kernel)
  · exact gapM_of_witness 30030 6 23 (by decide +kernel)
  · exact gapM_of_witness 30030 8 89 (by decide +kernel)
  · exact gapM_of_witness 30030 10 139 (by decide +kernel)
  · exact gapM_of_witness 30030 12 199 (by decide +kernel)
  · exact gapM_of_witness 30030 14 113 (by decide +kernel)
  · exact gapM_of_witness 30030 16 1 (by decide +kernel)
  · exact gapM_of_witness 30030 18 2183 (by decide +kernel)
  · exact gapM_of_witness 30030 22 9439 (by decide +kernel)

theorem de_polignac_gap_guess_false_holds : de_polignac_gap_guess_false := by
  intro hguess
  have hcons : consecutive_primes 11 13 := by
    unfold consecutive_primes
    refine ⟨by norm_num, by norm_num, by norm_num, fun r hr h1 h2 => ?_⟩
    have hr12 : r = 12 := by omega
    subst hr12
    norm_num at hr
  exact survivor_gaps_30030_miss_20_holds
    (hguess 11 13 hcons 20 (by norm_num) (by norm_num) (by norm_num))

theorem erdos_first_guess_fails_at_13_holds : erdos_first_guess_fails_at_13 :=
  ⟨survivor_gaps_30030_present_holds 22 (by simp), survivor_gaps_30030_miss_20_holds⟩

end RNS.GapCertificate

#print axioms RNS.GapCertificate.survivor_gaps_even_holds
#print axioms RNS.GapCertificate.survivor_gaps_30030_miss_20_holds
#print axioms RNS.GapCertificate.survivor_gaps_30030_present_holds
#print axioms RNS.GapCertificate.de_polignac_gap_guess_false_holds
#print axioms RNS.GapCertificate.erdos_first_guess_fails_at_13_holds
