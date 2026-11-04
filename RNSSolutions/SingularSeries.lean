/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.NumberTheory.SumPrimeReciprocals    -- `Nat.Primes.summable_rpow`
import Mathlib.Analysis.SpecialFunctions.Log.Summable  -- `multipliable_one_add_of_summable`
import Mathlib.Analysis.SpecialFunctions.Pow.Real      -- `Real.rpow_neg`, `Real.rpow_natCast`
import Mathlib.Analysis.Normed.Group.InfiniteSum       -- `Summable.of_norm_bounded_eventually`
import Mathlib.Topology.Order.OrderClosed              -- `ge_of_tendsto`
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push                             -- `push Not`
import RNSNetwork.Nodes.SurvivorCount.Conclusions
import RNSNetwork.Nodes.SingularSeries.Conclusions

/-!
# Proofs for SingularSeries

Imports claims only, never other nodes' proofs. Three of the four
conclusions rest on no other node and are proved outright here. The fourth,
`local_density_factorization`, is proved as a step from the claim
`SurvivorCount.general_survivor_count`, taken as the hypothesis `h_gen`;
`RNSSolutions/Assemble.lean` plugs in the finished proof.

Tactic proofs: the convergence and positivity proofs are from the
`HardyLittlewood` repository (already compiled on this Lean version), with
names changed back to the `rns_sieve_6.lean` spelling and every helper made
private. The local-density step is from `rns_sieve_6.lean`, Part B Step 4,
with the survivor-count formula supplied by `h_gen`.
-/

namespace RNS.SingularSeries

private theorem w_eq_card_of_lt (T : Finset Nat) (p : Nat) (hT : ∀ t ∈ T, t < p) :
    w T p = T.card := by
  unfold w
  have himg : T.image (fun t => t % p) = T := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨t, htT, rfl⟩
      rwa [Nat.mod_eq_of_lt (hT t htT)]
    · intro hx
      exact ⟨x, hx, Nat.mod_eq_of_lt (hT x hx)⟩
  rw [himg]

private theorem singular_series_factor_pos (T : Finset Nat) (hT : is_admissible T)
    (p : Nat) (hp : p.Prime) : 0 < singular_series_factor T p := by
  unfold singular_series_factor
  have hw : w T p < p := hT p hp
  have hwR : (w T p : Real) < (p : Real) := by exact_mod_cast hw
  have hp2 : (2 : Real) ≤ (p : Real) := by exact_mod_cast hp.two_le
  have hnum_pos : 0 < (p : Real) - w T p := by linarith
  have hpow_pos : 0 < (p : Real) ^ (T.card - 1) := by
    have : (0 : Real) < (p : Real) := by linarith
    positivity
  have hden_pos : 0 < ((p : Real) - 1) ^ T.card := by
    have : (0 : Real) < (p : Real) - 1 := by linarith
    positivity
  exact div_pos (mul_pos hpow_pos hnum_pos) hden_pos

private noncomputable def singular_series_delta (T : Finset Nat) (p : Nat) : Real :=
  singular_series_factor T p - 1

private theorem factor_eq_one_add (T : Finset Nat) (p : Nat) :
    singular_series_factor T p = 1 + singular_series_delta T p := by
  unfold singular_series_delta
  ring

/-- Core real-analysis lemma. Uses only `abs_le` + `mul_le_mul_of_nonneg_left`
to avoid any risk of a renamed `abs_add`/`abs_mul` in this snapshot. -/
private lemma poly_gap_bound (p : ℝ) (hp1 : 1 ≤ p) :
    ∀ m : ℕ,
      |(p - 1) ^ (m + 2) - p ^ (m + 1) * (p - ((m : ℝ) + 2))|
        ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) / 2 * p ^ m := by
  intro m
  induction m with
  | zero =>
    push_cast
    have heq : (p - 1) ^ (0 + 2) - p ^ (0 + 1) * (p - (0 + 2)) = 1 := by ring
    rw [heq]
    norm_num
  | succ n ih =>
    push_cast
    have hrec :
        (p - 1) ^ (n + 1 + 2) - p ^ (n + 1 + 1) * (p - ((n : ℝ) + 1 + 2))
          = ((n : ℝ) + 2) * p ^ (n + 1)
            + (p - 1) * ((p - 1) ^ (n + 2) - p ^ (n + 1) * (p - ((n : ℝ) + 2))) := by
      ring
    rw [hrec]
    have hpm1 : (0 : ℝ) ≤ p - 1 := by linarith
    obtain ⟨hipbL, hipbR⟩ := abs_le.mp ih
    have hmulR := mul_le_mul_of_nonneg_left hipbR hpm1
    have hmulL := mul_le_mul_of_nonneg_left hipbL hpm1
    have hp1p : p - 1 ≤ p := by linarith
    have hbound_nonneg : (0:ℝ) ≤ ((n:ℝ)+1)*((n:ℝ)+2)/2 * p^n := by positivity
    have hAnonneg : (0:ℝ) ≤ ((n:ℝ)+2) * p^(n+1) := by positivity
    have htarget_eq : ((n:ℝ)+1+1)*((n:ℝ)+1+2)/2 * p^(n+1)
        = ((n:ℝ)+2)*p^(n+1) + p * (((n:ℝ)+1)*((n:ℝ)+2)/2*p^n) := by ring
    rw [abs_le]
    constructor <;> nlinarith [hmulR, hmulL, hp1p, hbound_nonneg, hAnonneg, htarget_eq]

/-- **Key convergence estimate.** Once `p` exceeds every offset in `T`
(so `w T p = T.card` exactly, by `w_eq_card_of_lt`), the correction factor's
deviation from 1 shrinks like `O(1/p^2)` — fast enough for the sum over
all primes to converge. -/
private theorem delta_bound_aux (T : Finset Nat) (hk : 1 ≤ T.card) :
    ∃ C : Real, 0 ≤ C ∧ ∀ p : Nat, p.Prime → (∀ t ∈ T, t < p) →
      |singular_series_delta T p| ≤ C / (p : Real) ^ 2 := by
  set k := T.card with hkdef
  have hkR1 : (1 : Real) ≤ (k : Real) := by exact_mod_cast hk
  have hC_nonneg : 0 ≤ (k:Real) * ((k:Real) - 1) * 2 ^ (k - 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  refine ⟨(k : Real) * ((k : Real) - 1) * 2 ^ (k - 1), hC_nonneg, ?_⟩
  intro p hp hp_gt
  have hpR2 : (2 : Real) ≤ (p : Real) := by exact_mod_cast hp.two_le
  have hpR1 : (1 : Real) ≤ (p : Real) := by linarith
  have hp2pos : (0 : Real) < (p : Real) ^ 2 := pow_pos (by linarith) 2
  have hpm1 : (p : Real) - 1 ≠ 0 := by linarith
  have hw : w T p = k := w_eq_card_of_lt T p hp_gt
  have hδ_eq : singular_series_delta T p
      = -(((p:Real) - 1) ^ k - (p:Real) ^ (k - 1) * ((p:Real) - k)) / ((p:Real) - 1) ^ k := by
    unfold singular_series_delta singular_series_factor
    rw [← hkdef, hw]
    field_simp
    ring
  by_cases hk1 : k = 1
  · have hδ0 : singular_series_delta T p = 0 := by
      rw [hδ_eq, hk1]
      norm_num
    rw [hδ0]
    simp only [abs_zero, ge_iff_le]
    positivity
  · have hk2 : 2 ≤ k := by omega
    have hden_pos : (0:Real) < ((p:Real) - 1) ^ k := by positivity
    obtain ⟨m, hm⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have h1 : k - 1 = m + 1 := by omega
    have h2 : k - 2 = m := by omega
    have hbound_k : |((p:Real) - 1) ^ k - (p:Real) ^ (k - 1) * ((p:Real) - k)|
        ≤ ((k:Real) - 1) * (k:Real) / 2 * (p:Real) ^ (k - 2) := by
      have hb := poly_gap_bound (p:Real) hpR1 m
      have hLHS_eq : ((p:Real) - 1) ^ k - (p:Real) ^ (k - 1) * ((p:Real) - k)
          = (p - 1) ^ (m + 2) - p ^ (m + 1) * (p - ((m:Real) + 2)) := by
        rw [h1, hm]; push_cast; ring
      have hRHS_eq : ((k:Real) - 1) * (k:Real) / 2 * (p:Real) ^ (k - 2)
          = ((m:Real) + 1) * ((m:Real) + 2) / 2 * p ^ m := by
        rw [h2, hm]; push_cast; ring
      rw [hLHS_eq, hRHS_eq]
      exact hb
    have hpk_le : (p:Real)^k ≤ 2^k * ((p:Real)-1)^k := by
      have hstep : (p:Real) ≤ 2 * ((p:Real) - 1) := by linarith
      have hmono := pow_le_pow_left₀ (by positivity : (0:Real) ≤ (p:Real)) hstep k
      rwa [mul_pow] at hmono
    have hXp2 : |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| * (p:Real)^2
        ≤ ((k:Real)*((k:Real)-1)/2) * (p:Real)^k := by
      have h0 := mul_le_mul_of_nonneg_right hbound_k (le_of_lt hp2pos)
      have hexp2 : (k-2)+2 = k := by omega
      calc |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| * (p:Real)^2
          ≤ (((k:Real)-1)*(k:Real)/2 * (p:Real)^(k-2)) * (p:Real)^2 := h0
        _ = ((k:Real)*((k:Real)-1)/2) * (p:Real)^k := by
            rw [mul_assoc, ← pow_add, hexp2]; ring
    have hCD : ((k:Real)*((k:Real)-1)/2) * (p:Real)^k
        ≤ ((k:Real)*((k:Real)-1)*2^(k-1)) * ((p:Real)-1)^k := by
      have hksucc : k = (k - 1) + 1 := by omega
      have h2k : (2:Real)^k = 2 * 2^(k-1) := by
        conv_lhs => rw [hksucc]
        rw [pow_succ]
        ring
      have hcoef_nonneg : (0:Real) ≤ (k:Real)*((k:Real)-1)/2 := by nlinarith
      calc ((k:Real)*((k:Real)-1)/2) * (p:Real)^k
          ≤ ((k:Real)*((k:Real)-1)/2) * (2^k * ((p:Real)-1)^k) :=
            mul_le_mul_of_nonneg_left hpk_le hcoef_nonneg
        _ = ((k:Real)*((k:Real)-1)*2^(k-1)) * ((p:Real)-1)^k := by rw [h2k]; ring
    have hnum_nonneg : ((k:Real)*((k:Real)-1)*2^(k-1)) * ((p:Real)-1)^k
        - |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| * (p:Real)^2 ≥ 0 := by
      linarith [hXp2, hCD]
    rw [hδ_eq, abs_div, abs_neg, abs_of_pos hden_pos]
    have expand : (k:Real)*((k:Real)-1)*2^(k-1) / (p:Real)^2
        - |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| / ((p:Real)-1)^k
        = (((k:Real)*((k:Real)-1)*2^(k-1)) * ((p:Real)-1)^k
            - |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| * (p:Real)^2)
          / ((p:Real)^2 * ((p:Real)-1)^k) := by
      field_simp
    have hge : (k:Real)*((k:Real)-1)*2^(k-1) / (p:Real)^2
        - |((p:Real)-1)^k - (p:Real)^(k-1)*((p:Real)-k)| / ((p:Real)-1)^k ≥ 0 := by
      rw [expand]
      exact div_nonneg hnum_nonneg (by positivity)
    linarith [hge]

/-- `∑ ‖δ(p)‖` over all primes converges. Requires `T` nonempty (`hk`),
matching `delta_bound_aux`'s hypothesis. -/
private theorem delta_summable (T : Finset Nat) (hk : 1 ≤ T.card) :
    Summable (fun p : Nat.Primes => ‖singular_series_delta T p‖) := by
  obtain ⟨C, hC_nonneg, hC⟩ := delta_bound_aux T hk
  have hrpow : Summable (fun p : Nat.Primes => (p:ℝ) ^ (-2:ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have hconv : ∀ p : Nat.Primes, (p:ℝ) ^ (-2:ℝ) = 1 / (p:ℝ) ^ 2 := by
    intro p
    have hp_pos : (0:ℝ) < (p:ℝ) := by exact_mod_cast p.2.pos
    have step1 : (p:ℝ) ^ (-2:ℝ) = ((p:ℝ) ^ (2:ℝ))⁻¹ := by
      rw [show (-2:ℝ) = -(2:ℝ) by ring, Real.rpow_neg hp_pos.le]
    have step2 : (p:ℝ) ^ (2:ℝ) = (p:ℝ) ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [step1, step2, inv_eq_one_div]
  have hg : Summable (fun p : Nat.Primes => C / (p:ℝ) ^ 2) := by
    have hmul : Summable (fun p : Nat.Primes => C * (p:ℝ) ^ (-2:ℝ)) := hrpow.mul_left C
    have heq : (fun p : Nat.Primes => C * (p:ℝ) ^ (-2:ℝ))
        = (fun p : Nat.Primes => C / (p:ℝ) ^ 2) := by
      funext p
      rw [hconv p, mul_one_div]
    rwa [heq] at hmul
  have hfin : {p : Nat.Primes | ¬ ∀ t ∈ T, t < (p:ℕ)}.Finite := by
    have hinj : Function.Injective (fun p : Nat.Primes => (p:ℕ)) := by
      intro p q h
      exact Subtype.ext h
    have hpre : ((fun p : Nat.Primes => (p:ℕ)) ⁻¹' (Set.Iic (T.sup id))).Finite :=
      (Set.finite_Iic (T.sup id)).preimage hinj.injOn
    refine hpre.subset ?_
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    have hp' := hp
    push Not at hp'
    obtain ⟨t, htT, hnlt⟩ := hp'
    have ht_le : t ≤ T.sup id := by simpa using Finset.le_sup (f := id) htT
    simp only [Set.mem_preimage, Set.mem_Iic]
    omega
  apply Summable.of_norm_bounded_eventually hg
  rw [Filter.eventually_cofinite]
  apply hfin.subset
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  intro hp_gt
  apply hp
  rw [norm_norm]
  exact hC (p:ℕ) p.2 hp_gt

/-- The infinite product defining the singular series actually converges
(to a nonzero limit) — not just its `1 + δ(p)` summands being small, but
the product itself being well-defined. -/
private theorem multipliable_aux (T : Finset Nat) (hk : 1 ≤ T.card) :
    Multipliable (fun p : Nat.Primes => singular_series_factor T p) := by
  have hM : Multipliable (fun p : Nat.Primes => 1 + singular_series_delta T p) :=
    multipliable_one_add_of_summable (delta_summable T hk)
  have heq : (fun p : Nat.Primes => singular_series_factor T p)
      = (fun p : Nat.Primes => 1 + singular_series_delta T p) := by
    funext p
    exact factor_eq_one_add T p
  rw [heq]
  exact hM

/-- Self-contained Weierstrass-type product bound: if every finite subset of `s`
keeps `∑ |δ(p)|` under control, the product `∏ (1 + δ(p))` over `s` is bounded
below by `1 - ∑ |δ(p)|`. Proved by induction. -/
private lemma prod_one_add_ge_sub (δ : Nat.Primes → ℝ) (hpos : ∀ p, 0 < 1 + δ p)
    (s : Finset Nat.Primes) (hbound : ∑ p ∈ s, |δ p| ≤ 1) :
    1 - ∑ p ∈ s, |δ p| ≤ ∏ p ∈ s, (1 + δ p) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.sum_insert hp] at hbound ⊢
    rw [Finset.prod_insert hp]
    have hab : (0:ℝ) ≤ |δ p| := abs_nonneg _
    have hs_le : ∑ q ∈ s, |δ q| ≤ 1 := by linarith
    have hsum_nonneg : (0:ℝ) ≤ ∑ q ∈ s, |δ q| :=
      Finset.sum_nonneg (fun q _ => abs_nonneg (δ q))
    have ihP := ih hs_le
    have h1 : (0:ℝ) ≤ 1 + δ p := le_of_lt (hpos p)
    have hfac_nonneg : (0:ℝ) ≤ 1 - ∑ q ∈ s, |δ q| := by linarith
    have hle : -|δ p| ≤ δ p := neg_abs_le (δ p)
    have hmul1 : -|δ p| * (1 - ∑ q ∈ s, |δ q|) ≤ δ p * (1 - ∑ q ∈ s, |δ q|) :=
      mul_le_mul_of_nonneg_right hle hfac_nonneg
    have hmul2 : (1 + δ p) * (1 - ∑ q ∈ s, |δ q|) ≤ (1 + δ p) * ∏ q ∈ s, (1 + δ q) :=
      mul_le_mul_of_nonneg_left ihP h1
    nlinarith [hmul1, hmul2, mul_nonneg hab hsum_nonneg]

/-- `hardy_littlewood_constant T` is strictly positive for admissible `T`. -/
private theorem constant_pos_aux (T : Finset Nat) (hT : is_admissible T)
    (hk : 1 ≤ T.card) : 0 < hardy_littlewood_constant T := by
  set δ : Nat.Primes → ℝ := fun p => singular_series_delta T p with hδdef
  have hpos : ∀ p : Nat.Primes, 0 < 1 + δ p := by
    intro p
    have := singular_series_factor_pos T hT (p:ℕ) p.2
    rwa [factor_eq_one_add T (p:ℕ)] at this
  have hsummable : Summable (fun p : Nat.Primes => ‖δ p‖) := delta_summable T hk
  obtain ⟨S₀, hS₀⟩ := summable_iff_vanishing_norm.mp hsummable (1/2 : ℝ) (by norm_num)
  have hS₀tail : ∀ t : Finset Nat.Primes, Disjoint t S₀ → ∑ p ∈ t, |δ p| < 1/2 := by
    intro t htdisj
    have h := hS₀ t htdisj
    have heq : ∑ p ∈ t, ‖δ p‖ = ∑ p ∈ t, |δ p| := by simp [Real.norm_eq_abs]
    rw [heq] at h
    rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun p _ => abs_nonneg (δ p)))] at h
  set B := ∏ p ∈ S₀, (1 + δ p) with hBdef
  have hB_pos : 0 < B := Finset.prod_pos (fun p _ => hpos p)
  set m : ℝ := B / 2 with hmdef
  have hm_pos : 0 < m := by positivity
  have hHP : HasProd (fun p : Nat.Primes => singular_series_factor T p) (hardy_littlewood_constant T) :=
    (multipliable_aux T hk).hasProd
  have hHPδ : HasProd (fun p : Nat.Primes => 1 + δ p) (hardy_littlewood_constant T) := by
    have heqf : (fun p : Nat.Primes => singular_series_factor T p)
        = (fun p : Nat.Primes => 1 + δ p) := by
      funext p; exact factor_eq_one_add T p
    rwa [heqf] at hHP
  have hTendsto : Filter.Tendsto (fun s : Finset Nat.Primes => ∏ p ∈ s, (1 + δ p))
      Filter.atTop (nhds (hardy_littlewood_constant T)) := by
    unfold HasProd SummationFilter.unconditional at hHPδ
    exact hHPδ
  have hev : ∀ᶠ s : Finset Nat.Primes in Filter.atTop, m ≤ ∏ p ∈ s, (1 + δ p) := by
    rw [Filter.eventually_atTop]
    refine ⟨S₀, fun s hs => ?_⟩
    have hsplit : s = S₀ ∪ (s \ S₀) := (Finset.union_sdiff_of_subset hs).symm
    have hdisjoint : Disjoint S₀ (s \ S₀) := Finset.disjoint_sdiff
    rw [hsplit, Finset.prod_union hdisjoint]
    have htail_disj : Disjoint (s \ S₀) S₀ := hdisjoint.symm
    have htail_lt := hS₀tail (s \ S₀) htail_disj
    have htail_le : ∑ p ∈ s \ S₀, |δ p| ≤ 1 := by linarith
    have htail_bound := prod_one_add_ge_sub δ hpos (s \ S₀) htail_le
    have htail_pos : 0 < ∏ p ∈ s \ S₀, (1 + δ p) := Finset.prod_pos (fun p _ => hpos p)
    have hhalf : (1:ℝ)/2 ≤ ∏ p ∈ s \ S₀, (1 + δ p) := by linarith
    calc B / 2 = B * (1/2) := by ring
      _ ≤ B * (∏ p ∈ s \ S₀, (1 + δ p)) := by
          apply mul_le_mul_of_nonneg_left hhalf (le_of_lt hB_pos)
      _ = (∏ p ∈ S₀, (1 + δ p)) * ∏ p ∈ s \ S₀, (1 + δ p) := by rw [hBdef]
  have hge : m ≤ hardy_littlewood_constant T := ge_of_tendsto hTendsto hev
  linarith [hm_pos, hge]


/-! ## The conclusions that rest on no other node -/

theorem delta_bound_holds : delta_bound := by
  unfold delta_bound
  intro T hk
  obtain ⟨C, hC_nonneg, hC⟩ := delta_bound_aux T hk
  refine ⟨C, hC_nonneg, fun p hp hp_gt => ?_⟩
  have h := hC p hp hp_gt
  unfold singular_series_delta at h
  exact h

theorem factor_multipliable_holds : factor_multipliable := by
  unfold factor_multipliable
  exact multipliable_aux

theorem hardy_littlewood_constant_pos_holds : hardy_littlewood_constant_pos := by
  unfold hardy_littlewood_constant_pos
  exact constant_pos_aux

/-! ## Local density, as a step from `SurvivorCount` -/

private theorem mem_active_primes_is_prime (limit : Nat) (q : Nat)
    (hq : q ∈ active_primes limit) : q.Prime := by
  unfold active_primes at hq
  exact (Finset.mem_filter.mp hq).2

private theorem local_density_factor_eq (T : Finset Nat) (hk : 1 ≤ T.card) (q : Nat)
    (hq : q.Prime) :
    ((q : Real) - w T q) / (q : Real)
      = singular_series_factor T q * (1 - 1 / (q : Real)) ^ T.card := by
  unfold singular_series_factor
  set k := T.card with hkdef
  have hqR2 : (2 : Real) ≤ (q : Real) := by exact_mod_cast hq.two_le
  have hq1 : (q : Real) - 1 ≠ 0 := by linarith
  have hqne : (q : Real) ≠ 0 := by linarith
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hexp : m + 1 - 1 = m := by omega
  have h1 : (1 - 1 / (q : Real)) = ((q : Real) - 1) / (q : Real) := by field_simp
  rw [h1, div_pow, hm, hexp]
  field_simp
  ring

/-- **Step:** the whole-cycle survivor count implies the local-density
factorization. -/
theorem local_density_factorization_step
    (h_gen : RNS.SurvivorCount.general_survivor_count) : local_density_factorization := by
  unfold local_density_factorization
  intro T limit hT hk
  rw [h_gen T limit]
  have hcast_num : ((∏ q ∈ active_primes limit, (q - w T q) : ℕ) : Real)
      = ∏ q ∈ active_primes limit, ((q : Real) - w T q) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro q hq
    have hwlt : w T q < q := hT q (mem_active_primes_is_prime limit q hq)
    exact Nat.cast_sub hwlt.le
  have hcast_den : (primorial_modulus limit : Real) = ∏ q ∈ active_primes limit, (q : Real) := by
    unfold primorial_modulus
    rw [Nat.cast_prod]
    simp
  rw [hcast_num, hcast_den, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  exact local_density_factor_eq T hk q (mem_active_primes_is_prime limit q hq)

end RNS.SingularSeries

#print axioms RNS.SingularSeries.delta_bound_holds
#print axioms RNS.SingularSeries.factor_multipliable_holds
#print axioms RNS.SingularSeries.hardy_littlewood_constant_pos_holds
#print axioms RNS.SingularSeries.local_density_factorization_step
