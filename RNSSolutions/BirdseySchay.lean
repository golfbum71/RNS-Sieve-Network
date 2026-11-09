/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BirdseySchay.Conclusions
import RNSNetwork.Nodes.TwinShare.Conclusions
import RNSNetwork.Nodes.ShareAsymptotics.Conclusions
import RNSNetwork.Nodes.PrimeNumberTheorem.Conclusions
import RNSNetwork.Nodes.SingularSeries.Conclusions
import RNSNetwork.Nodes.Admissibility.Conclusions
import Mathlib.Data.Nat.PrimeFin                       -- `Nat.infinite_setOfPred_prime`
import Mathlib.Data.Nat.Prime.Nth                      -- `Nat.nth_prime_zero_eq_two`
import Mathlib.Data.Nat.Find                           -- `Nat.findGreatest`
import Mathlib.Order.WellFounded                       -- `StrictMono.id_le`
import Mathlib.Analysis.SpecificLimits.Basic           -- `tendsto_one_div_add_atTop_nhds_zero_nat`
import Mathlib.Order.Filter.AtTopBot.Archimedean       -- `tendsto_natCast_atTop_atTop`
import Mathlib.Topology.Algebra.GroupWithZero          -- `Filter.Tendsto.div`, `.inv₀`
import Mathlib.Topology.Algebra.Order.Field            -- `Filter.Tendsto.div_atTop`
import Mathlib.Topology.Order.LeftRightNhds            -- `Filter.Tendsto.atTop_add`
import Mathlib.Topology.Algebra.Monoid                 -- `Filter.Tendsto.pow`
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Proofs for BirdseySchay

Imports claims only. Every claim is a step from other nodes' claims, taken as
named hypotheses.

Idea.
* `corrected_share_limit`: the twin share among survivors is the twin share of
  the cycle divided by the survivor share of the cycle (`TwinShare`). The first,
  times the log squared, tends to the twin constant times e^(−2γ); the second,
  times the log, to e^(−γ) (`ShareAsymptotics`). So the twin share times the
  log tends to the twin constant times e^(−γ), and e^γ/2 leaves half the
  constant.
* `next_prime_ratio`: the number of primes up to the n-th prime is n + 1, so
  the prime number theorem makes (n + 1)·log(p)/p tend to 1 along the primes.
  Dividing the values at n and n + 1 makes ratio × log p / log p' tend to 1.
  Since log p' is at most log p plus (ratio − 1), the ratio is squeezed to 1.
* `twin_count_at_squares`: at x = p², the heuristic's prediction over Hardy and
  Littlewood's is (corrected share × log p) × (π(x) log x / x) × (2 / constant),
  since log x = 2 log p; the factors tend to (constant/2) × 1 × (2/constant) = 1.
* `birdsey_schay_implies_twin_asymptotic`: every bound N lies between two
  neighbouring prime squares a ≤ N < b. The twin count only grows, so the
  count over the prediction at N lies between its value at a times a/b and its
  value at b times b/a; both tend to 1 because b/a = (p'/p)² tends to 1.
-/

namespace RNS.BirdseySchay

open Filter Topology

/-! ## Small facts -/

private theorem cycle_pos (L : ℕ) : 0 < primorial_modulus L := by
  unfold primorial_modulus
  apply Finset.prod_pos
  intro q hq
  unfold active_primes at hq
  exact (Finset.mem_filter.mp hq).2.pos

/-- The number of primes up to the `n`-th prime (counting 2 as the 0-th) is
`n + 1`. -/
private theorem prime_count_nth (n : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime n) = n :=
    Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime n
  show Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n + 1
  rw [Nat.count_succ, h1]
  simp [Nat.prime_nth_prime n]

private theorem nth_prime_two_le (n : ℕ) : 2 ≤ Nat.nth Nat.Prime n :=
  (Nat.prime_nth_prime n).two_le

private theorem nth_prime_tendsto : Tendsto (fun n => Nat.nth Nat.Prime n) atTop atTop :=
  (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop

/-! ## The corrected share -/

/-- **Step:** `TwinShare` and `ShareAsymptotics` give the corrected share's
limit. -/
theorem corrected_share_limit_step
    (h_ts : RNS.TwinShare.twin_share_eq_prod)
    (h_s : RNS.ShareAsymptotics.survivor_share_asymptotic)
    (h_t : RNS.ShareAsymptotics.twin_share_asymptotic_classical) :
    corrected_share_limit := by
  unfold corrected_share_limit
  unfold RNS.ShareAsymptotics.survivor_share_asymptotic at h_s
  unfold RNS.ShareAsymptotics.twin_share_asymptotic_classical at h_t
  have hE : Real.exp (-Real.eulerMascheroniConstant) ≠ 0 := (Real.exp_pos _).ne'
  have hlim := (h_t.div h_s hE).const_mul (Real.exp Real.eulerMascheroniConstant / 2)
  have h1 : Real.exp Real.eulerMascheroniConstant *
      Real.exp (-Real.eulerMascheroniConstant) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : RNS.TwinConstant.twin_prime_classical_constant *
      Real.exp (-Real.eulerMascheroniConstant) ^ 2 / Real.exp (-Real.eulerMascheroniConstant)
      = RNS.TwinConstant.twin_prime_classical_constant *
        Real.exp (-Real.eulerMascheroniConstant) := by
    rw [pow_two, ← mul_assoc, mul_div_assoc, div_self hE, mul_one]
  have hval : Real.exp Real.eulerMascheroniConstant / 2 *
      (RNS.TwinConstant.twin_prime_classical_constant *
        Real.exp (-Real.eulerMascheroniConstant) ^ 2 / Real.exp (-Real.eulerMascheroniConstant))
      = RNS.TwinConstant.twin_prime_classical_constant / 2 := by
    rw [h2]
    linear_combination (RNS.TwinConstant.twin_prime_classical_constant / 2) * h1
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with q hq
  simp only [Pi.div_apply]
  have hM : (primorial_modulus (q + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (cycle_pos (q + 1)).ne'
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hL : Real.log q ≠ 0 := (Real.log_pos hq1).ne'
  rw [show twin_share q = ((RNS.wheel_survivors (q + 1)).card : ℝ) /
      ((RNS.wheel_survivors_gen {0} (q + 1)).card : ℝ) from (h_ts (q + 1)).symm]
  rcases eq_or_ne ((RNS.wheel_survivors_gen {0} (q + 1)).card : ℝ) 0 with hB | hB
  · simp [hB]
  · first | (field_simp; ring) | field_simp

/-! ## Neighbouring primes -/

/-- **Step:** the prime number theorem gives the ratio of neighbouring primes
tending to 1. -/
theorem next_prime_ratio_step (h_pnt : RNS.PrimeNumberTheorem.prime_number_theorem) :
    next_prime_ratio := by
  unfold next_prime_ratio
  unfold RNS.PrimeNumberTheorem.prime_number_theorem at h_pnt
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have htend : Tendsto (fun n => (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp nth_prime_tendsto
  have hP : ∀ n, (2 : ℝ) ≤ Nat.nth Nat.Prime n := fun n => by
    exact_mod_cast nth_prime_two_le n
  have hLpos : ∀ n, 0 < Real.log (Nat.nth Nat.Prime n) := fun n =>
    Real.log_pos (by linarith [hP n])
  -- (n + 1) log p / p tends to 1
  have ha : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.log (Nat.nth Nat.Prime n) /
      (Nat.nth Nat.Prime n : ℝ)) atTop (𝓝 1) := by
    refine (h_pnt.comp htend).congr (fun n => ?_)
    simp only [Function.comp_apply, Nat.floor_natCast, prime_count_nth, Nat.cast_add,
      Nat.cast_one]
  have ha1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2) * Real.log (Nat.nth Nat.Prime (n + 1)) /
      (Nat.nth Nat.Prime (n + 1) : ℝ)) atTop (𝓝 1) := by
    refine (ha.comp (tendsto_add_atTop_nat 1)).congr (fun n => ?_)
    simp only [Function.comp_apply]
    push_cast
    ring
  have hfrac : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    rw [add_zero] at h
    refine h.congr (fun n => ?_)
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  -- b n = ratio × log p / log p' tends to 1
  have hb : Tendsto (fun n : ℕ => (Nat.nth Nat.Prime (n + 1) : ℝ) / Nat.nth Nat.Prime n *
      Real.log (Nat.nth Nat.Prime n) / Real.log (Nat.nth Nat.Prime (n + 1))) atTop (𝓝 1) := by
    have h := (ha.div ha1 one_ne_zero).mul hfrac
    rw [div_one, mul_one] at h
    refine h.congr (fun n => ?_)
    simp only [Pi.div_apply]
    have h0 : (Nat.nth Nat.Prime n : ℝ) ≠ 0 := by linarith [hP n]
    have h0' : (Nat.nth Nat.Prime (n + 1) : ℝ) ≠ 0 := by linarith [hP (n + 1)]
    have hl : Real.log (Nat.nth Nat.Prime n) ≠ 0 := (hLpos n).ne'
    have hl' : Real.log (Nat.nth Nat.Prime (n + 1)) ≠ 0 := (hLpos (n + 1)).ne'
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
    first | (field_simp; ring) | field_simp
  -- the upper bound b (1 + (b − 1)/(log p − b)) tends to 1
  have hLt : Tendsto (fun n => Real.log (Nat.nth Nat.Prime n)) atTop atTop :=
    Real.tendsto_log_atTop.comp htend
  have hLb : Tendsto (fun n : ℕ => Real.log (Nat.nth Nat.Prime n) -
      ((Nat.nth Nat.Prime (n + 1) : ℝ) / Nat.nth Nat.Prime n *
        Real.log (Nat.nth Nat.Prime n) / Real.log (Nat.nth Nat.Prime (n + 1)))) atTop atTop := by
    refine (hLt.atTop_add hb.neg).congr (fun n => ?_)
    ring
  have hq : Tendsto (fun n : ℕ =>
      ((Nat.nth Nat.Prime (n + 1) : ℝ) / Nat.nth Nat.Prime n *
        Real.log (Nat.nth Nat.Prime n) / Real.log (Nat.nth Nat.Prime (n + 1)) - 1) /
      (Real.log (Nat.nth Nat.Prime n) -
      ((Nat.nth Nat.Prime (n + 1) : ℝ) / Nat.nth Nat.Prime n *
        Real.log (Nat.nth Nat.Prime n) / Real.log (Nat.nth Nat.Prime (n + 1))))) atTop (𝓝 0) :=
    (hb.sub tendsto_const_nhds).div_atTop hLb
  have hu := hb.mul (hq.const_add 1)
  rw [add_zero, mul_one] at hu
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
  · refine Eventually.of_forall (fun n => ?_)
    have hpos : (0 : ℝ) < Nat.nth Nat.Prime n := by linarith [hP n]
    rw [one_le_div hpos]
    exact_mod_cast (hmono (Nat.lt_succ_self n)).le
  · filter_upwards [hLb.eventually_gt_atTop 0] with n hn
    -- names for the pieces
    have hpos : (0 : ℝ) < Nat.nth Nat.Prime n := by linarith [hP n]
    have hpos' : (0 : ℝ) < Nat.nth Nat.Prime (n + 1) := by linarith [hP (n + 1)]
    have hr : (0 : ℝ) < (Nat.nth Nat.Prime (n + 1) : ℝ) / Nat.nth Nat.Prime n :=
      div_pos hpos' hpos
    have hl := hLpos n
    have hl' := hLpos (n + 1)
    generalize hR : (Nat.nth Nat.Prime (n + 1) : ℝ) / Nat.nth Nat.Prime n = r at hr hn ⊢
    generalize hLn : Real.log (Nat.nth Nat.Prime n) = L at hl hn ⊢
    have hL' : Real.log (Nat.nth Nat.Prime (n + 1)) ≤ L + (r - 1) := by
      have heq : (Nat.nth Nat.Prime (n + 1) : ℝ) = r * Nat.nth Nat.Prime n := by
        rw [← hR]; field_simp
      rw [heq, Real.log_mul hr.ne' hpos.ne', hLn]
      linarith [Real.log_le_sub_one_of_pos hr]
    generalize hLn' : Real.log (Nat.nth Nat.Prime (n + 1)) = L' at hl' hL' hn ⊢
    -- b = r L / L'
    have hb0 : 0 ≤ r * L / L' := by positivity
    have hbL : r * L / L' * L' = r * L := by field_simp
    have hkey : r * (L - r * L / L') ≤ r * L / L' * (L - 1) := by
      have h3 := mul_le_mul_of_nonneg_left hL' hb0
      nlinarith [h3, hbL]
    have hform : r * L / L' * (1 + (r * L / L' - 1) / (L - r * L / L')) =
        r * L / L' * (L - 1) / (L - r * L / L') := by
      have hD : L - r * L / L' ≠ 0 := hn.ne'
      rw [one_add_div hD, ← mul_div_assoc]
      congr 1
      ring
    rw [hform, le_div_iff₀ hn]
    exact hkey

/-! ## At the prime squares -/

/-- **Step:** the corrected share, the prime number theorem, `TwinConstant`,
`SingularSeries` and `Admissibility` turn the heuristic into Hardy and
Littlewood's count at the prime squares. -/
theorem twin_count_at_squares_step
    (h_cs : corrected_share_limit)
    (h_pnt : RNS.PrimeNumberTheorem.prime_number_theorem)
    (h_eq : RNS.TwinConstant.twin_prime_constant_eq_classical)
    (h_pos : RNS.SingularSeries.hardy_littlewood_constant_pos)
    (h_adm : RNS.Admissibility.zero_two_admissible) :
    twin_count_at_squares := by
  unfold twin_count_at_squares
  intro hBS
  refine hBS.trans (Asymptotics.isEquivalent_of_tendsto_one ?_)
  unfold corrected_share_limit at h_cs
  unfold RNS.PrimeNumberTheorem.prime_number_theorem at h_pnt
  unfold RNS.TwinConstant.twin_prime_constant_eq_classical at h_eq
  have hcard : ({0, 2} : Finset ℕ).card = 2 := by decide
  have hK : 0 < hardy_littlewood_constant ({0, 2} : Finset ℕ) :=
    h_pos _ h_adm (by rw [hcard]; norm_num)
  have hF1 : Tendsto (fun n => Real.exp Real.eulerMascheroniConstant / 2 *
      twin_share (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n)) atTop
      (𝓝 (hardy_littlewood_constant ({0, 2} : Finset ℕ) / 2)) := by
    have h := h_cs.comp nth_prime_tendsto
    rw [← h_eq] at h
    exact h
  have hx : Tendsto (fun n => ((Nat.nth Nat.Prime n ^ 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono
      (fun n => le_self_pow (Nat.prime_nth_prime n).one_lt.le two_ne_zero) nth_prime_tendsto)
  have hF2 : Tendsto (fun n => (Nat.primeCounting (Nat.nth Nat.Prime n ^ 2) : ℝ) *
      Real.log ((Nat.nth Nat.Prime n ^ 2 : ℕ) : ℝ) / ((Nat.nth Nat.Prime n ^ 2 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    refine (h_pnt.comp hx).congr (fun n => ?_)
    simp only [Function.comp_apply, Nat.floor_natCast]
  have hlim := (hF1.mul hF2).mul_const (2 / hardy_littlewood_constant ({0, 2} : Finset ℕ))
  have hval : hardy_littlewood_constant ({0, 2} : Finset ℕ) / 2 * 1 *
      (2 / hardy_littlewood_constant ({0, 2} : Finset ℕ)) = 1 := by
    have := hK.ne'
    field_simp
  rw [hval] at hlim
  refine hlim.congr (fun n => ?_)
  simp only [Pi.div_apply, hardy_littlewood_main_term, hcard]
  have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime n := by exact_mod_cast nth_prime_two_le n
  have hLp : Real.log (Nat.nth Nat.Prime n) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hX : ((Nat.nth Nat.Prime n ^ 2 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < Nat.nth Nat.Prime n ^ 2 := pow_pos (Nat.prime_nth_prime n).pos 2
    exact_mod_cast this.ne'
  have hKn := hK.ne'
  have hLx : Real.log ((Nat.nth Nat.Prime n ^ 2 : ℕ) : ℝ) =
      2 * Real.log (Nat.nth Nat.Prime n) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  rw [hLx]
  first | (field_simp; ring) | field_simp

/-! ## From the squares to every bound -/

/-- The index of the last term of `s` at or below `N`. -/
private def last_index (s : ℕ → ℕ) (N : ℕ) : ℕ := Nat.findGreatest (fun k => s k ≤ N) N

/-- The count over the prediction, in the form used for the squeeze. -/
private noncomputable def nratio (K : ℝ) (c : ℕ → ℝ) (x : ℕ) : ℝ :=
  c x * Real.log x ^ 2 / (K * x)

/-- **The squeeze.** A growing count whose ratio to K·x/(log x)² tends to 1
along a strictly increasing sequence with neighbouring ratio tending to 1 has
that ratio tending to 1 along every bound. -/
private theorem sandwich (K : ℝ) (hK : 0 < K) (c : ℕ → ℝ) (hc : Monotone c)
    (hc0 : ∀ x, 0 ≤ c x) (s : ℕ → ℕ) (hs : StrictMono s) (hs0 : 3 ≤ s 0)
    (hratio : Tendsto (fun n => (s (n + 1) : ℝ) / s n) atTop (𝓝 1))
    (hsq : Tendsto (fun n => nratio K c (s n)) atTop (𝓝 1)) :
    Tendsto (fun N => nratio K c N) atTop (𝓝 1) := by
  have hsk : ∀ k, k ≤ s k := fun k => hs.id_le k
  have hlow : ∀ N, s 0 ≤ N → s (last_index s N) ≤ N := fun N hN =>
    Nat.findGreatest_spec (P := fun k => s k ≤ N) (Nat.zero_le N) hN
  have hup : ∀ N, N < s (last_index s N + 1) := by
    intro N
    by_contra h
    have h' : s (last_index s N + 1) ≤ N := not_lt.mp h
    exact Nat.findGreatest_is_greatest (P := fun k => s k ≤ N) (Nat.lt_succ_self _)
      (le_trans (hsk _) h') h'
  have hmt : Tendsto (last_index s) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro k
    exact ⟨s k, fun N hN =>
      Nat.le_findGreatest (P := fun j => s j ≤ N) (le_trans (hsk k) hN) hN⟩
  have hspos : ∀ k, (3 : ℝ) ≤ s k := fun k => by
    have : s 0 ≤ s k := hs.monotone (Nat.zero_le k)
    exact_mod_cast le_trans hs0 this
  -- the lower and upper sequences
  have hL : Tendsto (fun n => nratio K c (s n) * ((s n : ℝ) / s (n + 1))) atTop (𝓝 1) := by
    have h := hsq.mul (hratio.inv₀ one_ne_zero)
    rw [inv_one, mul_one] at h
    refine h.congr (fun n => ?_)
    rw [inv_div]
  have hU : Tendsto (fun n => nratio K c (s (n + 1)) * ((s (n + 1) : ℝ) / s n)) atTop (𝓝 1) := by
    have h := (hsq.comp (tendsto_add_atTop_nat 1)).mul hratio
    rw [mul_one] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL.comp hmt) (hU.comp hmt) ?_ ?_
  · filter_upwards [eventually_ge_atTop (s 0)] with N hN
    simp only [Function.comp_apply]
    have ha := hlow N hN
    have hb := hup N
    have haR : (s (last_index s N) : ℝ) ≤ N := by exact_mod_cast ha
    have hbR : (N : ℝ) ≤ s (last_index s N + 1) := by exact_mod_cast hb.le
    have ha3 := hspos (last_index s N)
    have hb3 := hspos (last_index s N + 1)
    have hapos : (0 : ℝ) < s (last_index s N) := by linarith
    have hNpos : (0 : ℝ) < N := by linarith
    have hlogA : 0 ≤ Real.log (s (last_index s N)) := Real.log_nonneg (by linarith)
    have hlogAN : Real.log (s (last_index s N)) ≤ Real.log N := Real.log_le_log hapos haR
    have hform : nratio K c (s (last_index s N)) *
        ((s (last_index s N) : ℝ) / s (last_index s N + 1)) =
        c (s (last_index s N)) * Real.log (s (last_index s N)) ^ 2 /
          (K * s (last_index s N + 1)) := by
      unfold nratio
      have := hapos.ne'
      have : (s (last_index s N + 1) : ℝ) ≠ 0 := by linarith
      have := hK.ne'
      field_simp
    rw [hform]
    unfold nratio
    apply div_le_div₀ (mul_nonneg (hc0 N) (sq_nonneg _))
    · exact mul_le_mul (hc ha) (pow_le_pow_left₀ hlogA hlogAN 2) (sq_nonneg _) (hc0 N)
    · positivity
    · exact mul_le_mul_of_nonneg_left hbR hK.le
  · filter_upwards [eventually_ge_atTop (s 0)] with N hN
    simp only [Function.comp_apply]
    have ha := hlow N hN
    have hb := hup N
    have haR : (s (last_index s N) : ℝ) ≤ N := by exact_mod_cast ha
    have hbR : (N : ℝ) ≤ s (last_index s N + 1) := by exact_mod_cast hb.le
    have ha3 := hspos (last_index s N)
    have hapos : (0 : ℝ) < s (last_index s N) := by linarith
    have hNpos : (0 : ℝ) < N := by linarith
    have hbpos : (0 : ℝ) < s (last_index s N + 1) := by linarith
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
    have hlogNB : Real.log N ≤ Real.log (s (last_index s N + 1)) := Real.log_le_log hNpos hbR
    have hform : nratio K c (s (last_index s N + 1)) *
        ((s (last_index s N + 1) : ℝ) / s (last_index s N)) =
        c (s (last_index s N + 1)) * Real.log (s (last_index s N + 1)) ^ 2 /
          (K * s (last_index s N)) := by
      unfold nratio
      have := hapos.ne'
      have := hbpos.ne'
      have := hK.ne'
      field_simp
    rw [hform]
    unfold nratio
    apply div_le_div₀ (mul_nonneg (hc0 _) (sq_nonneg _))
    · exact mul_le_mul (hc hb.le) (pow_le_pow_left₀ hlogN hlogNB 2) (sq_nonneg _) (hc0 _)
    · exact mul_pos hK hapos
    · exact mul_le_mul_of_nonneg_left haR hK.le

/-- **Step:** the count at the squares and the ratio of neighbouring primes give
the Hardy–Littlewood conjecture for twins from the heuristic. -/
theorem birdsey_schay_implies_twin_asymptotic_step
    (h_sq : twin_count_at_squares)
    (h_r : next_prime_ratio)
    (h_pos : RNS.SingularSeries.hardy_littlewood_constant_pos)
    (h_adm : RNS.Admissibility.zero_two_admissible) :
    birdsey_schay_implies_twin_asymptotic := by
  unfold birdsey_schay_implies_twin_asymptotic
  intro hBS
  have hsqe := h_sq hBS
  unfold next_prime_ratio at h_r
  unfold RNS.HardyLittlewood.hardy_littlewood_conjecture
  have hcard : ({0, 2} : Finset ℕ).card = 2 := by decide
  have hK : 0 < hardy_littlewood_constant ({0, 2} : Finset ℕ) :=
    h_pos _ h_adm (by rw [hcard]; norm_num)
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  -- the count is growing and nonnegative
  have hc : Monotone (fun N : ℕ => (actual_tuple_count ({0, 2} : Finset ℕ) N : ℝ)) := by
    intro a b hab
    simp only
    unfold actual_tuple_count
    exact_mod_cast Finset.card_le_card (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      exact ⟨by omega, hx.2⟩)
  have hc0 : ∀ N, 0 ≤ (fun N : ℕ => (actual_tuple_count ({0, 2} : Finset ℕ) N : ℝ)) N :=
    fun N => Nat.cast_nonneg _
  -- the prime squares
  have hs : StrictMono (fun n => Nat.nth Nat.Prime n ^ 2) := fun a b h =>
    Nat.pow_lt_pow_left (hmono h) two_ne_zero
  have hs0 : 3 ≤ (fun n => Nat.nth Nat.Prime n ^ 2) 0 := by
    simp only [Nat.nth_prime_zero_eq_two]; norm_num
  have hratio : Tendsto (fun n => (((fun n => Nat.nth Nat.Prime n ^ 2) (n + 1) : ℕ) : ℝ) /
      (((fun n => Nat.nth Nat.Prime n ^ 2) n : ℕ) : ℝ)) atTop (𝓝 1) := by
    have h := h_r.pow 2
    rw [one_pow] at h
    refine h.congr (fun n => ?_)
    simp only
    push_cast
    rw [div_pow]
  -- the ratio at the squares
  have hz : ∀ᶠ n in atTop,
      hardy_littlewood_main_term ({0, 2} : Finset ℕ) (Nat.nth Nat.Prime n ^ 2) ≠ 0 := by
    refine Eventually.of_forall (fun n => ?_)
    unfold hardy_littlewood_main_term
    rw [hcard]
    have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime n := by exact_mod_cast nth_prime_two_le n
    have hX : (1 : ℝ) < ((Nat.nth Nat.Prime n ^ 2 : ℕ) : ℝ) := by push_cast; nlinarith
    have := (Real.log_pos hX).ne'
    have := hK.ne'
    have : ((Nat.nth Nat.Prime n ^ 2 : ℕ) : ℝ) ≠ 0 := by linarith
    positivity
  have hsq := (Asymptotics.isEquivalent_iff_tendsto_one hz).mp hsqe
  have hsq' : Tendsto (fun n => nratio (hardy_littlewood_constant ({0, 2} : Finset ℕ))
      (fun N : ℕ => (actual_tuple_count ({0, 2} : Finset ℕ) N : ℝ))
      ((fun n => Nat.nth Nat.Prime n ^ 2) n)) atTop (𝓝 1) := by
    refine hsq.congr (fun n => ?_)
    simp only [Pi.div_apply, twin_pairs_below, hardy_littlewood_main_term, hcard, nratio]
    rw [div_div_eq_mul_div]
  have hall := sandwich _ hK _ hc hc0 _ hs hs0 hratio hsq'
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  refine hall.congr (fun N => ?_)
  simp only [Pi.div_apply, hardy_littlewood_main_term, hcard, nratio]
  rw [div_div_eq_mul_div]

end RNS.BirdseySchay

#print axioms RNS.BirdseySchay.corrected_share_limit_step
#print axioms RNS.BirdseySchay.next_prime_ratio_step
#print axioms RNS.BirdseySchay.twin_count_at_squares_step
#print axioms RNS.BirdseySchay.birdsey_schay_implies_twin_asymptotic_step
