/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PillaiBrauer.Conclusions
import Mathlib.Data.Nat.Prime.Basic             -- `Nat.minFac_prime`
import Mathlib.Tactic.NormNum.Prime             -- `norm_num` deciding small numbers prime
import Mathlib.Tactic.IntervalCases

/-!
# Proofs for PillaiBrauer

Imports claims only, never other nodes' proofs. Rests on no other node.

Built clean by `lake build RNSSolutions` on 2026-11-05; `#print axioms` shows only
the standard three. The two `decide` calls are
finite checks (17 × 17 × 6 divisibility tests, and six divisibility tests);
the witness was checked numerically beforehand.

`pillai_sixteen` was first cited; its proof (by a kernel-checked pass over the
cycle 30030) is appended at the end of this file.
-/

namespace RNS.PillaiBrauer

/-- **The run of 17 from 2184**, by direct check. -/
theorem pillai_witness_17_holds : pillai_witness_17 := by
  unfold pillai_witness_17 small_wheels
  decide

/-- Every wheel up to 13 divides the cycle 30030. -/
private theorem small_wheels_dvd_cycle : ∀ p ∈ small_wheels, p ∣ 30030 := by
  unfold small_wheels
  decide

/-- Every wheel up to 13 is at least 2. -/
private theorem small_wheels_ge_two : ∀ p ∈ small_wheels, 2 ≤ p := by
  unfold small_wheels
  decide

/-- A wheel up to 13 dividing a member of the run from 2184 also divides the
same member of the run shifted by `m` cycles. -/
private theorem dvd_shift {p m i : Nat} (hp : p ∈ small_wheels) (h : p ∣ 2184 + i) :
    p ∣ 30030 * m + 2184 + i := by
  have e : 30030 * m + 2184 + i = 30030 * m + (2184 + i) := by omega
  rw [e]
  exact Nat.dvd_add (Dvd.dvd.mul_right (small_wheels_dvd_cycle p hp) m) h

/-- **The run repeats with the cycle**, from the run of 17 from 2184. -/
theorem pillai_witness_17_repeats_holds : pillai_witness_17_repeats := by
  intro m i hi
  obtain ⟨j, hj, hji, p, hp, hpi, hpj⟩ := pillai_witness_17_holds i hi
  refine ⟨j, hj, hji, ?_⟩
  have hdvd : p ∣ Nat.gcd (30030 * m + 2184 + i) (30030 * m + 2184 + j) :=
    Nat.dvd_gcd (dvd_shift hp hpi) (dvd_shift hp hpj)
  have hpos : 0 < Nat.gcd (30030 * m + 2184 + i) (30030 * m + 2184 + j) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  have hle := Nat.le_of_dvd hpos hdvd
  have h2 := small_wheels_ge_two p hp
  omega

end RNS.PillaiBrauer

#print axioms RNS.PillaiBrauer.pillai_witness_17_holds
#print axioms RNS.PillaiBrauer.pillai_witness_17_repeats_holds

/-! ## Pillai's theorem for runs of up to 16

Two members of a run of at most 16 consecutive numbers differ by at most 15,
so a prime dividing both divides their difference and is one of the wheels
2, 3, 5, 7, 11, 13. Hence a member is coprime to every other member as soon
as each of those wheels dividing it has no other multiple in the run, and
that depends only on the run's start modulo the cycle 30030. A Boolean
program, evaluated by the kernel (`decide +kernel`, no extra axiom), finds
such a member for every start in the cycle and every length from 1 to 16
(30 blocks of 1001 starts).
-/

namespace RNS.PillaiBrauer

/-- The member at position `i` of the run of length `k` starting at `r`
passes every wheel up to 13: either the wheel does not divide it, or the
wheel has no other multiple in the run. -/
private def goodAt (r k i : Nat) : Bool :=
  [2, 3, 5, 7, 11, 13].all fun p => (r + i) % p != 0 || (decide (i < p) && decide (k ≤ i + p))

private theorem goodAt_spec {r k i : Nat} (h : goodAt r k i = true) :
    ∀ p ∈ [2, 3, 5, 7, 11, 13], (r + i) % p ≠ 0 ∨ (i < p ∧ k ≤ i + p) := by
  intro p hp
  unfold goodAt at h
  have := List.all_eq_true.mp h p hp
  simpa [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] using this

/-- Some position below `b` passes. -/
private def someGood (r k : Nat) : Nat → Bool
  | 0 => false
  | i + 1 => goodAt r k i || someGood r k i

private theorem someGood_spec {r k : Nat} :
    ∀ b, someGood r k b = true → ∃ i < b, goodAt r k i = true
  | 0, h => by simp [someGood] at h
  | b + 1, h => by
    simp only [someGood, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨b, by omega, h⟩
    · obtain ⟨i, hi, hg⟩ := someGood_spec b h
      exact ⟨i, by omega, hg⟩

/-- Every length from 1 to `K` has a passing position. -/
private def allK (r : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => someGood r (k + 1) (k + 1) && allK r k

private theorem allK_spec {r : Nat} :
    ∀ K, allK r K = true → ∀ k, 1 ≤ k → k ≤ K → someGood r k k = true
  | 0, _, k, h1, h2 => by exfalso; omega
  | K + 1, h, k, h1, h2 => by
    simp only [allK, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge k (K + 1) with hk | hk
    · exact allK_spec K h.2 k h1 (by omega)
    · have hkK : k = K + 1 := by omega
      subst hkK
      exact h.1

/-- Every start from `lo` up to `lo + len` passes for all lengths up to 16. -/
private def allIn (lo : Nat) : Nat → Bool
  | 0 => true
  | len + 1 => allK (lo + len) 16 && allIn lo len

private theorem allIn_spec {lo : Nat} :
    ∀ len, allIn lo len = true → ∀ r, lo ≤ r → r < lo + len → allK r 16 = true
  | 0, _, r, h1, h2 => by exfalso; omega
  | len + 1, h, r, h1, h2 => by
    simp only [allIn, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge r (lo + len) with hr | hr
    · exact allIn_spec len h.2 r h1 hr
    · have hrl : r = lo + len := by omega
      subst hrl
      exact h.1

/-- The first `N` blocks of width `B` all pass. -/
private def allBlocks (B : Nat) : Nat → Bool
  | 0 => true
  | N + 1 => allIn (N * B) B && allBlocks B N

private theorem allBlocks_spec {B : Nat} :
    ∀ N, allBlocks B N = true → ∀ r, r < N * B → allK r 16 = true
  | 0, _, r, hr => by simp at hr
  | N + 1, h, r, hr => by
    simp only [allBlocks, Bool.and_eq_true] at h
    rw [Nat.add_mul, Nat.one_mul] at hr
    rcases Nat.lt_or_ge r (N * B) with h' | h'
    · exact allBlocks_spec N h.2 r h'
    · exact allIn_spec B h.1 r h' (by omega)

/-- The whole cycle 30030 passes. -/
private theorem cycle_checked : ∀ r, r < 30030 → allK r 16 = true := fun r hr =>
  allBlocks_spec (B := 1001) 30 (by decide +kernel) r (by omega)

private theorem list_wheels_dvd_cycle : ∀ q ∈ [2, 3, 5, 7, 11, 13], q ∣ 30030 := by
  decide

/-- A prime dividing a positive number at most 15 is one of the wheels up to 13. -/
private theorem prime_le_fifteen_mem {q d : Nat} (hq : q.Prime) (hd : 0 < d) (hqd : q ∣ d)
    (hd15 : d ≤ 15) : q ∈ [2, 3, 5, 7, 11, 13] := by
  have h2 := hq.two_le
  have hle := Nat.le_of_dvd hd hqd
  have hq15 : q ≤ 15 := by omega
  interval_cases q <;> first | decide | (exfalso; norm_num at hq)

/-- A passing position is coprime to every other member of the run. -/
private theorem coprime_of_good (n k i j : Nat) (hik : i < k) (hjk : j < k) (hji : j ≠ i)
    (hk : k ≤ 16)
    (hg : ∀ p ∈ [2, 3, 5, 7, 11, 13], (n % 30030 + i) % p ≠ 0 ∨ (i < p ∧ k ≤ i + p)) :
    Nat.Coprime (n + i) (n + j) := by
  by_contra hne
  have hq : (Nat.gcd (n + i) (n + j)).minFac.Prime := Nat.minFac_prime hne
  have hqi : (Nat.gcd (n + i) (n + j)).minFac ∣ n + i :=
    (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
  have hqj : (Nat.gcd (n + i) (n + j)).minFac ∣ n + j :=
    (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
  generalize (Nat.gcd (n + i) (n + j)).minFac = q at hq hqi hqj
  have hmod_of (hmem : q ∈ [2, 3, 5, 7, 11, 13]) : (n % 30030 + i) % q = 0 := by
    rw [Nat.add_mod, Nat.mod_mod_of_dvd n (list_wheels_dvd_cycle q hmem), ← Nat.add_mod]
    exact Nat.mod_eq_zero_of_dvd hqi
  rcases Nat.lt_or_gt_of_ne hji with hlt | hlt
  · -- the other member comes first
    have hd : q ∣ i - j := by
      have h := Nat.dvd_sub hqi hqj
      rwa [show n + i - (n + j) = i - j by omega] at h
    have hmem := prime_le_fifteen_mem hq (by omega) hd (by omega)
    rcases hg q hmem with h | ⟨hiq, _⟩
    · exact h (hmod_of hmem)
    · have := Nat.le_of_dvd (by omega) hd
      omega
  · -- the other member comes later
    have hd : q ∣ j - i := by
      have h := Nat.dvd_sub hqj hqi
      rwa [show n + j - (n + i) = j - i by omega] at h
    have hmem := prime_le_fifteen_mem hq (by omega) hd (by omega)
    rcases hg q hmem with h | ⟨_, hkq⟩
    · exact h (hmod_of hmem)
    · have := Nat.le_of_dvd (by omega) hd
      omega

/-- **Pillai's theorem for runs of up to 16**, proved: by the cycle check and
`coprime_of_good`. -/
theorem pillai_sixteen_holds : pillai_sixteen := by
  intro n k _ hk1 hk16
  have hall := cycle_checked (n % 30030) (Nat.mod_lt _ (by norm_num))
  obtain ⟨i, hik, hgood⟩ := someGood_spec k (allK_spec 16 hall k hk1 hk16)
  exact ⟨i, hik, fun j hjk hji => coprime_of_good n k i j hik hjk hji hk16 (goodAt_spec hgood)⟩

end RNS.PillaiBrauer

#print axioms RNS.PillaiBrauer.pillai_sixteen_holds
