/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PatternUpperBound.Conclusions
import RNSNetwork.Nodes.SelbergBound.Conclusions
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Data.Nat.Count                          -- `Nat.count_add`, `Nat.count_monotone`
import Mathlib.Data.Nat.Find                           -- `Nat.findGreatest`
import Mathlib.Data.Nat.Factorial.Basic                -- `Nat.dvd_factorial`
import Mathlib.Data.ZMod.Basic                         -- `ZMod.chineseRemainder`, `ZMod.val_natCast`
import Mathlib.Algebra.Field.ZMod                      -- `ZMod p` is a field for prime `p`
import Mathlib.SetTheory.Cardinal.Finite               -- `Nat.card_congr`, `Nat.card_prod`
import Mathlib.Data.Nat.GCD.BigOperators               -- `Nat.Coprime.prod_right`
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset -- `Finset.prod_pos`
import Mathlib.Algebra.Group.Units.Equiv               -- `Equiv.addRight`
import Mathlib.Data.Nat.Squarefree                     -- `Nat.prod_primeFactors_of_squarefree`
import Mathlib.Algebra.Squarefree.Basic                -- `Finset.squarefree_prod_of_pairwise_isCoprime`
import Mathlib.Algebra.BigOperators.Associated         -- `Prime.dvd_finsetProd_iff`
import Mathlib.Algebra.BigOperators.Ring.Finset        -- `Finset.sum_boole`
import Mathlib.NumberTheory.Divisors                   -- `Nat.mem_divisors`
import Mathlib.NumberTheory.Harmonic.Bounds            -- `log_add_one_le_harmonic`
import Mathlib.Analysis.SpecialFunctions.Pow.Real      -- `Real.sqrt`, `Real.log`, `Nat.floor`
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Proofs for PatternUpperBound

Imports claims only. `pattern_multiples_count` is proved outright (Mathlib only).
`pattern_sieve_bound` is a step from `SelbergBound.selberg_bound`,
`pattern_multiples_count` and `BadWheels.blocked_le_card`;
`pattern_selberg_sum_lower` a step from `BadWheels.blocked_le_card` and
`BadWheels.blocked_eq_card_iff`; `pattern_count_le` a step from the two before.

The multiples count. The condition "the product of the wheels divides the
product of the forms" repeats with that product, so the count up to `N` is
`N` over the product times the count in one cycle, off by at most one cycle's
count. One cycle is the residues where the product of the forms is zero; by
the Chinese Remainder Theorem that number multiplies over the wheels, and for
one wheel it is the number of positions the wheel blocks.

The lower bound (after Ford, Theorem 4.4, as in `SelbergTwinRails`, with the
number of forms `k` in place of 2). Write Selberg's pattern sum as a sum over
sets of wheels, each set weighing the product of its wheels' Selberg terms
(blocked count over wheel minus blocked count). Raise every wheel's term to
`k` over (wheel − `k`): replacing one wheel's term by a larger one multiplies
the sum by at most (1 + the larger term) over (1 + the smaller one), which is
(wheel − blocked count) over (wheel − `k`); over all wheels that product is at
most the bad factor. With the larger terms the sum is at least the smooth sum
of `k` to the number of prime factors of `n` over `n`, over the `n` built from
the wheels; that is at least the `k`-th power of the sum of 1/a over the `a`
up to the `k`-th root, leaving remainder 1 on division by `k!` (the number of
ways to write a number as a product of `k` factors is at most `k` to its
number of prime factors), and that sum is at least log of the root over `k!`.

The count. Take `t` the `m`-th root of `N` rounded down, with `m = k + 6`; the
level t² and the cut-off t² + 1. A position from the cut-off up where every
form is prime survives the sieve; the survivors are at most `N` over the
pattern sum plus the error, the error is at most t⁶ (each wheel is above `k`,
and 3k is at most (k + 1)²), and t⁶ log^k N is at most a constant times N.
-/

namespace RNS.PatternUpperBound

open RNS.BadWheels BoundingSieve

/-! ## Counting one cycle at a time -/

theorem ioc_count_eq (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ((Finset.Ioc 0 N).filter P).card = Nat.count (fun k => P (k + 1)) N := by
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_nbij' (fun m => m - 1) (fun k => k + 1)
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨h1, h2⟩, h3⟩ := hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    have h : m - 1 + 1 = m := by omega
    show m - 1 < N ∧ P (m - 1 + 1)
    refine ⟨by omega, ?_⟩
    rw [h]
    exact h3
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨h1, h2⟩ := hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    show (0 < k + 1 ∧ k + 1 ≤ N) ∧ P (k + 1)
    exact ⟨⟨by omega, by omega⟩, h2⟩
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨h1, _⟩, _⟩ := hm
    show m - 1 + 1 = m
    omega
  · intro k _
    show k + 1 - 1 = k
    omega

theorem count_period_add (Q : ℕ → Prop) [DecidablePred Q] (d : ℕ)
    (hQ : ∀ k, Q (d + k) ↔ Q k) (N : ℕ) :
    Nat.count Q (d + N) = Nat.count Q d + Nat.count Q N := by
  rw [Nat.count_add]
  congr 1
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    Finset.filter_congr (fun k _ => hQ k)]

theorem count_period_mul (Q : ℕ → Prop) [DecidablePred Q] (d : ℕ)
    (hQ : ∀ k, Q (d + k) ↔ Q k) (q r : ℕ) :
    Nat.count Q (q * d + r) = q * Nat.count Q d + Nat.count Q r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * d + r = d + (q * d + r) by ring, count_period_add Q d hQ, ih]
    ring

theorem count_bound_real (Q : ℕ → Prop) [DecidablePred Q] (d : ℕ) (hd : 0 < d)
    (hQ : ∀ k, Q (d + k) ↔ Q k) (N : ℕ) :
    |(Nat.count Q N : ℝ) - (N : ℝ) * (Nat.count Q d : ℝ) / (d : ℝ)|
      ≤ (Nat.count Q d : ℝ) := by
  have hNd : N / d * d + N % d = N := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod N d
  have hsplit : Nat.count Q N = N / d * Nat.count Q d + Nat.count Q (N % d) := by
    have h := count_period_mul Q d hQ (N / d) (N % d)
    rw [hNd] at h
    exact h
  have hc : Nat.count Q (N % d) ≤ Nat.count Q d :=
    Nat.count_monotone Q (Nat.mod_lt N hd).le
  have hc' : (Nat.count Q (N % d) : ℝ) ≤ (Nat.count Q d : ℝ) := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ (Nat.count Q (N % d) : ℝ) := Nat.cast_nonneg _
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hb : ((N % d : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.mod_lt N hd).le
  have hR0 : (0 : ℝ) ≤ (Nat.count Q d : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ ((N % d : ℕ) : ℝ) * (Nat.count Q d : ℝ) / (d : ℝ) := by positivity
  have ht1 : ((N % d : ℕ) : ℝ) * (Nat.count Q d : ℝ) / (d : ℝ) ≤ (Nat.count Q d : ℝ) := by
    rw [div_le_iff₀ hdR]
    nlinarith [mul_le_mul_of_nonneg_left hb hR0]
  have hN : (N : ℝ) = ((N / d : ℕ) : ℝ) * (d : ℝ) + ((N % d : ℕ) : ℝ) := by
    exact_mod_cast hNd.symm
  have heq : (N : ℝ) * (Nat.count Q d : ℝ) / (d : ℝ)
      = ((N / d : ℕ) : ℝ) * (Nat.count Q d : ℝ)
        + ((N % d : ℕ) : ℝ) * (Nat.count Q d : ℝ) / (d : ℝ) := by
    rw [hN]
    field_simp <;> ring
  rw [hsplit]
  push_cast
  rw [abs_le]
  constructor <;> linarith

/-! ## One cycle is the residues where the product of the forms is zero -/

/-- The product of the forms in any commutative semiring. -/
def patR {R : Type*} [CommSemiring R] (L : Finset (ℕ × ℕ)) (x : R) : R :=
  ∏ ℓ ∈ L, ((ℓ.1 : R) * x + (ℓ.2 : R))

theorem patR_map {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (L : Finset (ℕ × ℕ)) (x : R) : f (patR L x) = patR L (f x) := by
  unfold patR
  rw [map_prod]
  refine Finset.prod_congr rfl (fun ℓ _ => ?_)
  rw [map_add, map_mul, map_natCast, map_natCast]

theorem patR_cast {R : Type*} [CommSemiring R] (L : Finset (ℕ × ℕ)) (m : ℕ) :
    ((pattern_value L m : ℕ) : R) = patR L (m : R) := by
  unfold pattern_value patR
  rw [Nat.cast_prod]
  refine Finset.prod_congr rfl (fun ℓ _ => ?_)
  rw [Nat.cast_add, Nat.cast_mul]

theorem patR_fst {R S : Type*} [CommSemiring R] [CommSemiring S] (L : Finset (ℕ × ℕ))
    (y : R × S) : (patR L y).1 = patR L y.1 :=
  patR_map (RingHom.fst R S) L y

theorem patR_snd {R S : Type*} [CommSemiring R] [CommSemiring S] (L : Finset (ℕ × ℕ))
    (y : R × S) : (patR L y).2 = patR L y.2 :=
  patR_map (RingHom.snd R S) L y

theorem pattern_periodic (L : Finset (ℕ × ℕ)) (d k : ℕ) :
    d ∣ pattern_value L (d + k + 1) ↔ d ∣ pattern_value L (k + 1) := by
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff, patR_cast, patR_cast]
  have h : ((d + k + 1 : ℕ) : ZMod d) = ((k + 1 : ℕ) : ZMod d) := by
    push_cast
    rw [ZMod.natCast_self, zero_add]
  rw [h]

theorem pattern_period_count (L : Finset (ℕ × ℕ)) (d : ℕ) (hd : 0 < d) :
    Nat.count (fun k => d ∣ pattern_value L (k + 1)) d =
      Nat.card {x : ZMod d // patR L x = 0} := by
  have : NeZero d := ⟨hd.ne'⟩
  have e1 : Nat.card {x : ZMod d // patR L x = 0} =
      Nat.card {x : ZMod d // patR L (x + 1) = 0} :=
    (Nat.card_congr (Equiv.subtypeEquiv (Equiv.addRight (1 : ZMod d)) (fun x => Iff.rfl))).symm
  rw [e1, Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.count_eq_card_filter_range]
  apply Finset.card_nbij' (fun k : ℕ => (k : ZMod d)) (fun x : ZMod d => x.val)
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter] at hk
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := (ZMod.natCast_eq_zero_iff (pattern_value L (k + 1)) d).mpr hk.2
    rw [patR_cast] at h
    push_cast at h
    exact h
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    show d ∣ pattern_value L (x.val + 1)
    rw [← ZMod.natCast_eq_zero_iff, patR_cast]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hx.2
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
    show ((k : ZMod d)).val = k
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk.1]
  · intro x _
    show ((x.val : ℕ) : ZMod d) = x
    exact ZMod.natCast_zmod_val x

theorem pattern_roots_mul (L : Finset (ℕ × ℕ)) (m n : ℕ) (h : m.Coprime n) :
    Nat.card {x : ZMod (m * n) // patR L x = 0} =
      Nat.card {x : ZMod m // patR L x = 0} * Nat.card {x : ZMod n // patR L x = 0} := by
  let e := ZMod.chineseRemainder h
  rw [← Nat.card_prod]
  apply Nat.card_congr
  refine (Equiv.subtypeEquiv e.toEquiv
    (q := fun y : ZMod m × ZMod n => patR L y.1 = 0 ∧ patR L y.2 = 0) ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun a : ZMod m => patR L a = 0)
      (q := fun b : ZMod n => patR L b = 0))
  intro x
  have hx : e (patR L x) = patR L (e x) := patR_map e.toRingHom L x
  show patR L x = 0 ↔ patR L (e x).1 = 0 ∧ patR L (e x).2 = 0
  rw [← e.injective.eq_iff, map_zero, hx, Prod.ext_iff, patR_fst, patR_snd]
  simp only [Prod.fst_zero, Prod.snd_zero]

theorem pattern_roots_one (L : Finset (ℕ × ℕ)) :
    Nat.card {x : ZMod 1 // patR L x = 0} = 1 := by
  haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)), Nat.card_zmod]

theorem pattern_roots_prime (L : Finset (ℕ × ℕ)) (p : ℕ) (hp : p.Prime) :
    Nat.card {x : ZMod p // patR L x = 0} = blocked_count L p := by
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold blocked_count blocked
  apply Finset.card_nbij' (fun x : ZMod p => x.val) (fun r : ℕ => (r : ZMod p))
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    have h0 : patR L x = 0 := hx.2
    unfold patR at h0
    obtain ⟨ℓ, hℓ, hz⟩ := Finset.prod_eq_zero_iff.mp h0
    refine ⟨ℓ, hℓ, ?_⟩
    rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact hz
  · intro r hr
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨ℓ, hℓ, hz⟩ := hr.2
    show patR L (r : ZMod p) = 0
    unfold patR
    apply Finset.prod_eq_zero_iff.mpr
    refine ⟨ℓ, hℓ, ?_⟩
    have h := (ZMod.natCast_eq_zero_iff (ℓ.1 * r + ℓ.2) p).mpr (Nat.dvd_of_mod_eq_zero hz)
    push_cast at h
    exact h
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro r hr
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
    show ((r : ZMod p)).val = r
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr.1]

theorem pattern_roots_prod (L : Finset (ℕ × ℕ)) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) :
    Nat.card {x : ZMod (D.prod id) // patR L x = 0} = pattern_rho L D := by
  induction D using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, pattern_roots_one]
    simp [pattern_rho]
  | insert a s ha ih =>
    have haP : a.Prime := hD a (Finset.mem_insert_self a s)
    have hsP : ∀ q ∈ s, q.Prime := fun q hq => hD q (Finset.mem_insert_of_mem hq)
    have hprod : (insert a s).prod id = a * s.prod id := Finset.prod_insert ha
    have hcop : a.Coprime (s.prod id) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hqa : a ≠ q := fun h => ha (by rw [h]; exact hq)
      exact (Nat.coprime_primes haP (hsP q hq)).mpr hqa
    rw [hprod, pattern_roots_mul L a (s.prod id) hcop, pattern_roots_prime L a haP, ih hsP]
    simp only [pattern_rho, Finset.prod_insert ha]

theorem pattern_multiples_count_holds : pattern_multiples_count := by
  intro L D N hD
  have hd : 0 < D.prod id := Finset.prod_pos (fun p hp => (hD p hp).pos)
  have hcount : ((Finset.Ioc 0 N).filter (fun m => D.prod id ∣ pattern_value L m)).card
      = Nat.count (fun k => D.prod id ∣ pattern_value L (k + 1)) N :=
    ioc_count_eq (fun m => D.prod id ∣ pattern_value L m) N
  have hper := pattern_period_count L (D.prod id) hd
  rw [pattern_roots_prod L D hD] at hper
  have hb := count_bound_real (fun k => D.prod id ∣ pattern_value L (k + 1)) (D.prod id) hd
    (fun k => pattern_periodic L (D.prod id) k) N
  rw [hper] at hb
  rw [hcount]
  exact hb

/-! ## The forms: primitive forms give a nonzero bad product -/

theorem cross_ne_zero {ℓ ℓ' : ℕ × ℕ} (h1 : 1 ≤ ℓ.1 ∧ Nat.Coprime ℓ.1 ℓ.2)
    (h2 : 1 ≤ ℓ'.1 ∧ Nat.Coprime ℓ'.1 ℓ'.2) (hne : ℓ ≠ ℓ') : cross ℓ ℓ' ≠ 0 := by
  intro h
  unfold cross at h
  have h' : ℓ.1 * ℓ'.2 = ℓ'.1 * ℓ.2 := by
    have : (ℓ.1 : ℤ) * ℓ'.2 = (ℓ'.1 : ℤ) * ℓ.2 := by linarith
    exact_mod_cast this
  have ha : ℓ.1 ∣ ℓ'.1 := by
    apply h1.2.dvd_of_dvd_mul_right
    rw [← h']
    exact Dvd.intro _ rfl
  have ha' : ℓ'.1 ∣ ℓ.1 := by
    apply h2.2.dvd_of_dvd_mul_right
    rw [h']
    exact Dvd.intro _ rfl
  have heq : ℓ.1 = ℓ'.1 := Nat.dvd_antisymm ha ha'
  have hb : ℓ'.2 = ℓ.2 := by
    rw [← heq] at h'
    exact Nat.eq_of_mul_eq_mul_left (by omega) h'
  exact hne (Prod.ext heq hb.symm)

theorem bad_product_ne_zero {L : Finset (ℕ × ℕ)} (hL : primitive_forms L) :
    bad_product L ≠ 0 := by
  unfold bad_product
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.mpr (fun ℓ hℓ => ?_)
    have := (hL ℓ hℓ).1
    exact_mod_cast (show ℓ.1 ≠ 0 by omega)
  · refine Finset.prod_ne_zero_iff.mpr (fun e he => ?_)
    obtain ⟨he1, he2, hne⟩ := Finset.mem_offDiag.mp he
    exact cross_ne_zero (hL e.1 he1) (hL e.2 he2) hne

/-! ## The sieve wheels -/

theorem mem_pattern_wheels {L : Finset (ℕ × ℕ)} {z p : ℕ} :
    p ∈ pattern_wheels L z ↔ p.Prime ∧ p < z ∧ L.card < p ∧ 0 < blocked_count L p := by
  unfold pattern_wheels active_primes
  simp only [Finset.mem_filter, Finset.mem_range]
  tauto

theorem pattern_wheels_prime {L : Finset (ℕ × ℕ)} {z p : ℕ} (hp : p ∈ pattern_wheels L z) :
    p.Prime :=
  (mem_pattern_wheels.mp hp).1

theorem pattern_product_squarefree (L : Finset (ℕ × ℕ)) (z : ℕ) :
    Squarefree (pattern_wheel_product L z) := by
  unfold pattern_wheel_product
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a ha b hb hab => ?_)
    (fun p hp => (pattern_wheels_prime hp).prime.squarefree)
  exact Nat.coprime_iff_isRelPrime.mp
    ((Nat.coprime_primes (pattern_wheels_prime (Finset.mem_coe.mp ha))
      (pattern_wheels_prime (Finset.mem_coe.mp hb))).mpr hab)

theorem pattern_mem_of_prime_dvd {L : Finset (ℕ × ℕ)} {z p : ℕ} (hp : p.Prime)
    (h : p ∣ pattern_wheel_product L z) : p ∈ pattern_wheels L z := by
  unfold pattern_wheel_product at h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).mp h
  rwa [(Nat.prime_dvd_prime_iff_eq hp (pattern_wheels_prime hq)).mp hpq]

/-! ## Sums over sets of wheels -/

/-- The sum, over the sets of wheels from `S` with product at most `M`, of the
product of the weights. -/
noncomputable def setSumW (w : ℕ → ℝ) (S : Finset ℕ) (M : ℕ) : ℝ :=
  ∑ T ∈ S.powerset, if (∏ p ∈ T, p) ≤ M then ∏ p ∈ T, w p else 0

theorem setSumW_nonneg {w : ℕ → ℝ} {S : Finset ℕ} (hS : ∀ p ∈ S, 0 ≤ w p) (M : ℕ) :
    0 ≤ setSumW w S M := by
  unfold setSumW
  refine Finset.sum_nonneg (fun T hT => ?_)
  split_ifs
  · exact Finset.prod_nonneg (fun p hp => hS p (Finset.mem_powerset.mp hT hp))
  · exact le_rfl

theorem setSumW_mono {w : ℕ → ℝ} {S : Finset ℕ} (hS : ∀ p ∈ S, 0 ≤ w p) {M M' : ℕ}
    (h : M ≤ M') : setSumW w S M ≤ setSumW w S M' := by
  unfold setSumW
  refine Finset.sum_le_sum (fun T hT => ?_)
  by_cases h1 : (∏ p ∈ T, p) ≤ M
  · rw [ite_eq_left h1, ite_eq_left (h1.trans h)]
  · rw [ite_eq_right h1]
    split_ifs
    · exact Finset.prod_nonneg (fun p hp => hS p (Finset.mem_powerset.mp hT hp))
    · exact le_rfl

theorem setSumW_insert {w : ℕ → ℝ} {S : Finset ℕ} {q : ℕ} (hq : q ∉ S) (hq0 : 0 < q)
    (M : ℕ) : setSumW w (insert q S) M = setSumW w S M + w q * setSumW w S (M / q) := by
  unfold setSumW
  rw [Finset.sum_powerset_insert hq]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  have hqT : q ∉ T := fun h => hq (Finset.mem_powerset.mp hT h)
  have hiff : q * (∏ p ∈ T, p) ≤ M ↔ (∏ p ∈ T, p) ≤ M / q := by
    rw [Nat.le_div_iff_mul_le hq0, Nat.mul_comm (∏ p ∈ T, p) q]
  have hP : ∏ p ∈ insert q T, p = q * ∏ p ∈ T, p := Finset.prod_insert hqT
  have hW : ∏ p ∈ insert q T, w p = w q * ∏ p ∈ T, w p := Finset.prod_insert hqT
  rw [hP, hW]
  by_cases h : (∏ p ∈ T, p) ≤ M / q
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h, mul_zero]

theorem setSumW_subset {w : ℕ → ℝ} {S S' : Finset ℕ} (hsub : S' ⊆ S)
    (hz : ∀ p ∈ S, p ∉ S' → w p = 0) (M : ℕ) : setSumW w S' M = setSumW w S M := by
  unfold setSumW
  apply Finset.sum_subset (Finset.powerset_mono.mpr hsub)
  intro T hT hT'
  rw [Finset.mem_powerset] at hT hT'
  obtain ⟨p, hpT, hpS'⟩ := Finset.not_subset.mp hT'
  have h0 : ∏ q ∈ T, w q = 0 := Finset.prod_eq_zero hpT (hz p (hT hpT) hpS')
  rw [h0]
  split_ifs <;> rfl

/-- **Raising the weights.** With weights `g ≤ h` on `S`, the product over `S`
of (1 + g) times the sum with `h` is at most the product of (1 + h) times the
sum with `g`. -/
theorem setSumW_replace (g h : ℕ → ℝ) (S : Finset ℕ) :
    (∀ p ∈ S, 0 < p ∧ 0 ≤ g p ∧ g p ≤ h p) → ∀ M : ℕ,
      (∏ p ∈ S, (1 + g p)) * setSumW h S M ≤ (∏ p ∈ S, (1 + h p)) * setSumW g S M := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ M
    simp [setSumW]
  | insert q S hq ih =>
    intro hS M
    have hS' : ∀ p ∈ S, 0 < p ∧ 0 ≤ g p ∧ g p ≤ h p :=
      fun p hp => hS p (Finset.mem_insert_of_mem hp)
    obtain ⟨hq0, hg0, hgh⟩ := hS q (Finset.mem_insert_self q S)
    have hgS : ∀ p ∈ S, 0 ≤ g p := fun p hp => (hS' p hp).2.1
    have hhS : ∀ p ∈ S, 0 ≤ h p := fun p hp => (hS' p hp).2.1.trans (hS' p hp).2.2
    rw [setSumW_insert hq hq0, setSumW_insert hq hq0, Finset.prod_insert hq,
      Finset.prod_insert hq]
    have i1 := ih hS' M
    have i2 := ih hS' (M / q)
    have hPh : 0 ≤ ∏ p ∈ S, (1 + h p) :=
      Finset.prod_nonneg (fun p hp => by linarith [hhS p hp])
    have hBA : setSumW g S (M / q) ≤ setSumW g S M := setSumW_mono hgS (Nat.div_le_self M q)
    have hhq : 0 ≤ h q := hg0.trans hgh
    have i2' := mul_le_mul_of_nonneg_left i2 hhq
    have step1 : (∏ p ∈ S, (1 + g p)) * (setSumW h S M + h q * setSumW h S (M / q)) ≤
        (∏ p ∈ S, (1 + h p)) * (setSumW g S M + h q * setSumW g S (M / q)) := by
      nlinarith
    have step2 : (1 + g q) * (setSumW g S M + h q * setSumW g S (M / q)) ≤
        (1 + h q) * (setSumW g S M + g q * setSumW g S (M / q)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hgh) (sub_nonneg.mpr hBA)]
    calc (1 + g q) * (∏ p ∈ S, (1 + g p)) * (setSumW h S M + h q * setSumW h S (M / q))
        = (1 + g q) * ((∏ p ∈ S, (1 + g p)) *
            (setSumW h S M + h q * setSumW h S (M / q))) := by ring
      _ ≤ (1 + g q) * ((∏ p ∈ S, (1 + h p)) *
            (setSumW g S M + h q * setSumW g S (M / q))) :=
          mul_le_mul_of_nonneg_left step1 (by linarith)
      _ = (∏ p ∈ S, (1 + h p)) *
            ((1 + g q) * (setSumW g S M + h q * setSumW g S (M / q))) := by ring
      _ ≤ (∏ p ∈ S, (1 + h p)) *
            ((1 + h q) * (setSumW g S M + g q * setSumW g S (M / q))) :=
          mul_le_mul_of_nonneg_left step2 hPh
      _ = (1 + h q) * (∏ p ∈ S, (1 + h p)) * (setSumW g S M + g q * setSumW g S (M / q)) := by
          ring

/-! ## The smooth sum -/

/-- The raised weight `k` over (the wheel − `k`). -/
noncomputable def kw (k : ℕ) (p : ℕ) : ℝ := (k : ℝ) / ((p : ℝ) - k)

/-- The smooth term: `k` to the number of prime factors of `n` over `n`, when
every prime factor of `n` lies in `S`. -/
noncomputable def smoothTermK (k : ℕ) (S : Finset ℕ) (n : ℕ) : ℝ :=
  if n.primeFactors ⊆ S then (k : ℝ) ^ ArithmeticFunction.cardFactors n / n else 0

/-- The smooth sum over the numbers from 1 to `M`. -/
noncomputable def smoothSumK (k : ℕ) (S : Finset ℕ) (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, smoothTermK k S n

theorem smoothTermK_nonneg (k : ℕ) (S : Finset ℕ) (n : ℕ) : 0 ≤ smoothTermK k S n := by
  unfold smoothTermK
  split_ifs
  · positivity
  · exact le_rfl

theorem smoothTermK_mul {k : ℕ} {S : Finset ℕ} {q m : ℕ} (hq : q.Prime) (hqS : q ∈ S)
    (hm0 : m ≠ 0) : smoothTermK k S (q * m) = (k : ℝ) / (q : ℝ) * smoothTermK k S m := by
  have hcond : (q * m).primeFactors ⊆ S ↔ m.primeFactors ⊆ S := by
    rw [Nat.primeFactors_mul hq.ne_zero hm0, hq.primeFactors, Finset.union_subset_iff,
      Finset.singleton_subset_iff]
    exact ⟨fun h => h.2, fun h => ⟨hqS, h⟩⟩
  have hΩ : ArithmeticFunction.cardFactors (q * m) = ArithmeticFunction.cardFactors m + 1 := by
    rw [ArithmeticFunction.cardFactors_mul hq.ne_zero hm0,
      ArithmeticFunction.cardFactors_apply_prime hq, Nat.add_comm]
  unfold smoothTermK
  by_cases h : m.primeFactors ⊆ S
  · rw [ite_eq_left (hcond.mpr h), ite_eq_left h, hΩ, pow_succ]
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    push_cast
    first | (field_simp; ring) | field_simp
  · rw [ite_eq_right (fun h' => h (hcond.mp h')), ite_eq_right h, mul_zero]

theorem smoothSumK_insert_le {k : ℕ} {S : Finset ℕ} {q : ℕ} (hq : q ∉ S) (hqP : q.Prime)
    (M : ℕ) : smoothSumK k (insert q S) M ≤
      smoothSumK k S M + (k : ℝ) / (q : ℝ) * smoothSumK k (insert q S) (M / q) := by
  have hq0 : 0 < q := hqP.pos
  unfold smoothSumK
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun n => q ∣ n), add_comm]
  refine add_le_add ?_ ?_
  · calc ∑ n ∈ (Finset.Icc 1 M).filter (fun n => ¬ q ∣ n), smoothTermK k (insert q S) n
        = ∑ n ∈ (Finset.Icc 1 M).filter (fun n => ¬ q ∣ n), smoothTermK k S n := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          have hqn : ¬ q ∣ n := (Finset.mem_filter.mp hn).2
          have hnq : q ∉ n.primeFactors := fun h => hqn (Nat.dvd_of_mem_primeFactors h)
          have hiff : n.primeFactors ⊆ insert q S ↔ n.primeFactors ⊆ S := by
            constructor
            · intro h p hp
              rcases Finset.mem_insert.mp (h hp) with rfl | h'
              · exact absurd hp hnq
              · exact h'
            · intro h
              exact h.trans (Finset.subset_insert _ _)
          unfold smoothTermK
          by_cases h : n.primeFactors ⊆ S
          · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
          · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]
      _ ≤ ∑ n ∈ Finset.Icc 1 M, smoothTermK k S n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun n _ _ => smoothTermK_nonneg k S n)
  · have hsub : (Finset.Icc 1 M).filter (fun n => q ∣ n) ⊆
        (Finset.Icc 1 (M / q)).image (fun m => q * m) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩ := hn
      rw [Finset.mem_image]
      refine ⟨m, ?_, rfl⟩
      rw [Finset.mem_Icc]
      constructor
      · rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, Nat.mul_zero] at h1
          omega
        · exact h
      · rw [Nat.le_div_iff_mul_le hq0, Nat.mul_comm]
        exact h2
    rw [Finset.mul_sum]
    calc ∑ n ∈ (Finset.Icc 1 M).filter (fun n => q ∣ n), smoothTermK k (insert q S) n
        ≤ ∑ n ∈ (Finset.Icc 1 (M / q)).image (fun m => q * m), smoothTermK k (insert q S) n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => smoothTermK_nonneg _ _ n)
      _ = ∑ m ∈ Finset.Icc 1 (M / q), smoothTermK k (insert q S) (q * m) := by
          rw [Finset.sum_image]
          intro a _ b _ h
          exact Nat.eq_of_mul_eq_mul_left hq0 h
      _ = ∑ m ∈ Finset.Icc 1 (M / q), (k : ℝ) / (q : ℝ) * smoothTermK k (insert q S) m := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          have hm0 : m ≠ 0 := by
            have := (Finset.mem_Icc.mp hm).1
            omega
          exact smoothTermK_mul hqP (Finset.mem_insert_self q S) hm0

/-- **The sum with raised weights is at least the smooth sum.** -/
theorem smoothSumK_le_setSumW (k : ℕ) (S : Finset ℕ) :
    (∀ p ∈ S, p.Prime ∧ k < p) → ∀ M, smoothSumK k S M ≤ setSumW (kw k) S M := by
  refine Finset.induction_on S ?_ ?_
  · intro _ M
    have h1 : smoothSumK k ∅ M ≤ ∑ n ∈ Finset.Icc 1 M, (if n = 1 then (1 : ℝ) else 0) := by
      unfold smoothSumK
      refine Finset.sum_le_sum (fun n hn => ?_)
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      unfold smoothTermK
      split_ifs with h h'
      · rw [h', ArithmeticFunction.cardFactors_one]
        norm_num
      · exfalso
        have := Finset.subset_empty.mp h
        rw [Nat.primeFactors_eq_empty] at this
        omega
      · positivity
      · exact le_rfl
    refine h1.trans (le_of_eq ?_)
    rw [Finset.sum_ite_eq']
    unfold setSumW
    by_cases hM : 1 ≤ M
    · simp [hM]
    · simp [hM]
  · intro q S hq ih hS' M
    have hSS : ∀ p ∈ S, p.Prime ∧ k < p := fun p hp => hS' p (Finset.mem_insert_of_mem hp)
    have hqP := hS' q (Finset.mem_insert_self q S)
    have hkw : ∀ p ∈ S, 0 ≤ kw k p := by
      intro p hp
      have : (k : ℝ) < p := by exact_mod_cast (hSS p hp).2
      unfold kw
      exact div_nonneg (Nat.cast_nonneg k) (by linarith)
    have hkw' : ∀ p ∈ insert q S, 0 ≤ kw k p := by
      intro p hp
      have : (k : ℝ) < p := by exact_mod_cast (hS' p hp).2
      unfold kw
      exact div_nonneg (Nat.cast_nonneg k) (by linarith)
    have ihS := ih hSS
    have hq0 : 0 < q := hqP.1.pos
    have hqk : (k : ℝ) < q := by exact_mod_cast hqP.2
    have hg0 : 0 ≤ kw k q := by
      unfold kw
      exact div_nonneg (Nat.cast_nonneg k) (by linarith)
    have hkq0 : 0 ≤ (k : ℝ) / (q : ℝ) := div_nonneg (Nat.cast_nonneg k) (by linarith)
    induction M using Nat.strong_induction_on with
    | _ M ihM =>
      rcases Nat.eq_zero_or_pos M with hM | hM
      · subst hM
        have : smoothSumK k (insert q S) 0 = 0 := by simp [smoothSumK]
        rw [this]
        exact setSumW_nonneg hkw' 0
      · have hlt : M / q < M := Nat.div_lt_self hM hqP.1.one_lt
        calc smoothSumK k (insert q S) M
            ≤ smoothSumK k S M + (k : ℝ) / (q : ℝ) * smoothSumK k (insert q S) (M / q) :=
              smoothSumK_insert_le hq hqP.1 M
          _ ≤ setSumW (kw k) S M + (k : ℝ) / (q : ℝ) * setSumW (kw k) (insert q S) (M / q) :=
              add_le_add (ihS M) (mul_le_mul_of_nonneg_left (ihM _ hlt) hkq0)
          _ = setSumW (kw k) S M + (k : ℝ) / (q : ℝ) *
                (setSumW (kw k) S (M / q) + kw k q * setSumW (kw k) S (M / q / q)) := by
              rw [setSumW_insert hq hq0]
          _ ≤ setSumW (kw k) S M + (k : ℝ) / (q : ℝ) *
                (setSumW (kw k) S (M / q) + kw k q * setSumW (kw k) S (M / q)) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left
                (add_le_add le_rfl (mul_le_mul_of_nonneg_left
                  (setSumW_mono hkw (Nat.div_le_self _ _)) hg0)) hkq0)
          _ = setSumW (kw k) S M + kw k q * setSumW (kw k) S (M / q) := by
              unfold kw
              have h1 : (q : ℝ) ≠ 0 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
              have h2 : (q : ℝ) - k ≠ 0 := by linarith
              field_simp
              ring
          _ = setSumW (kw k) (insert q S) M := (setSumW_insert hq hq0 M).symm

/-! ## Products of `k` factors -/

/-- The step of the divisor bound at one more prime factor. -/
theorem sum_divisors_step (j : ℝ) (hj : 0 ≤ j) {p m : ℕ} (hp : p.Prime) (hm0 : m ≠ 0)
    (ih : ∑ a ∈ m.divisors, j ^ ArithmeticFunction.cardFactors (m / a) ≤
      (j + 1) ^ ArithmeticFunction.cardFactors m) :
    ∑ a ∈ (p * m).divisors, j ^ ArithmeticFunction.cardFactors (p * m / a) ≤
      (j + 1) ^ ArithmeticFunction.cardFactors (p * m) := by
  have hp0 : 0 < p := hp.pos
  have hsub : (p * m).divisors ⊆ m.divisors ∪ m.divisors.image (fun e => p * e) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    rw [Finset.mem_union, Finset.mem_image]
    by_cases hpd : p ∣ d
    · right
      obtain ⟨e, rfl⟩ := hpd
      exact ⟨e, Nat.mem_divisors.mpr ⟨(mul_dvd_mul_iff_left hp.ne_zero).mp hd.1, hm0⟩, rfl⟩
    · left
      have hc : Nat.Coprime d p := ((hp.coprime_iff_not_dvd).mpr hpd).symm
      exact Nat.mem_divisors.mpr ⟨hc.dvd_of_dvd_mul_left hd.1, hm0⟩
  have hF0 : ∀ a : ℕ, 0 ≤ j ^ ArithmeticFunction.cardFactors (p * m / a) :=
    fun a => pow_nonneg hj _
  have h1 : ∑ a ∈ (p * m).divisors, j ^ ArithmeticFunction.cardFactors (p * m / a) ≤
      ∑ a ∈ m.divisors ∪ m.divisors.image (fun e => p * e),
        j ^ ArithmeticFunction.cardFactors (p * m / a) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hF0 a)
  have h2 : ∑ a ∈ m.divisors ∪ m.divisors.image (fun e => p * e),
        j ^ ArithmeticFunction.cardFactors (p * m / a) ≤
      ∑ a ∈ m.divisors, j ^ ArithmeticFunction.cardFactors (p * m / a) +
        ∑ a ∈ m.divisors.image (fun e => p * e),
          j ^ ArithmeticFunction.cardFactors (p * m / a) := by
    rw [← Finset.sum_union_inter]
    have : 0 ≤ ∑ a ∈ m.divisors ∩ m.divisors.image (fun e => p * e),
        j ^ ArithmeticFunction.cardFactors (p * m / a) :=
      Finset.sum_nonneg (fun a _ => hF0 a)
    linarith
  have h3 : ∑ a ∈ m.divisors, j ^ ArithmeticFunction.cardFactors (p * m / a) =
      j * ∑ a ∈ m.divisors, j ^ ArithmeticFunction.cardFactors (m / a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    have ha' := Nat.mem_divisors.mp ha
    have hm0' : 0 < m := Nat.pos_of_ne_zero hm0
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha'.1 hm0'
    have hma0 : m / a ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hm0' ha'.1) ha0).ne'
    rw [Nat.mul_div_assoc p ha'.1, ArithmeticFunction.cardFactors_mul hp.ne_zero hma0,
      ArithmeticFunction.cardFactors_apply_prime hp, pow_add, pow_one]
  have h4 : ∑ a ∈ m.divisors.image (fun e => p * e),
        j ^ ArithmeticFunction.cardFactors (p * m / a) =
      ∑ e ∈ m.divisors, j ^ ArithmeticFunction.cardFactors (m / e) := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [Nat.mul_div_mul_left m e hp0]
    · intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_left hp0 h
  have hΩ : ArithmeticFunction.cardFactors (p * m) = ArithmeticFunction.cardFactors m + 1 := by
    rw [ArithmeticFunction.cardFactors_mul hp.ne_zero hm0,
      ArithmeticFunction.cardFactors_apply_prime hp, Nat.add_comm]
  rw [hΩ, pow_succ]
  have hS0 : 0 ≤ ∑ a ∈ m.divisors, j ^ ArithmeticFunction.cardFactors (m / a) :=
    Finset.sum_nonneg (fun _ _ => pow_nonneg hj _)
  calc ∑ a ∈ (p * m).divisors, j ^ ArithmeticFunction.cardFactors (p * m / a)
      ≤ ∑ a ∈ m.divisors, j ^ ArithmeticFunction.cardFactors (p * m / a) +
        ∑ a ∈ m.divisors.image (fun e => p * e),
          j ^ ArithmeticFunction.cardFactors (p * m / a) := h1.trans h2
    _ = j * ∑ a ∈ m.divisors, j ^ ArithmeticFunction.cardFactors (m / a) +
        ∑ e ∈ m.divisors, j ^ ArithmeticFunction.cardFactors (m / e) := by rw [h3, h4]
    _ = (j + 1) * ∑ a ∈ m.divisors, j ^ ArithmeticFunction.cardFactors (m / a) := by ring
    _ ≤ (j + 1) * (j + 1) ^ ArithmeticFunction.cardFactors m :=
        mul_le_mul_of_nonneg_left ih (by linarith)
    _ = (j + 1) ^ ArithmeticFunction.cardFactors m * (j + 1) := by ring

/-- Over the divisors `a` of `n`, `j` to the number of prime factors of `n / a`
adds up to at most `j + 1` to the number of prime factors of `n`. -/
theorem sum_divisors_pow_le (j : ℝ) (hj : 0 ≤ j) (n : ℕ) (hn : n ≠ 0) :
    ∑ a ∈ n.divisors, j ^ ArithmeticFunction.cardFactors (n / a) ≤
      (j + 1) ^ ArithmeticFunction.cardFactors n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      simp
    · have hp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [Nat.mul_zero] at hm
        exact hn hm
      have hmlt : m < n := by
        have h2 := hp.two_le
        rw [hm]
        nlinarith [Nat.pos_of_ne_zero hm0]
      have ihm := ih m hmlt hm0
      rw [hm]
      exact sum_divisors_step j hj hp hm0 ihm

/-- The numbers from 1 to `K` leaving the same remainder as 1 on division by `Q`. -/
def oneMod (Q K : ℕ) : Finset ℕ := (Finset.Icc 1 K).filter (fun a => a % Q = 1 % Q)

theorem oneMod_one (Q : ℕ) : oneMod Q 1 = {1} := by
  ext n
  unfold oneMod
  rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩
    omega
  · rintro rfl
    exact ⟨⟨le_rfl, le_rfl⟩, rfl⟩

theorem fiber_le (Q K j m : ℕ) (hm : 1 ≤ m) :
    ∑ x ∈ (oneMod Q K ×ˢ oneMod Q (K ^ j)).filter (fun x => x.1 * x.2 = m),
      (1 : ℝ) / x.1 * ((j : ℝ) ^ ArithmeticFunction.cardFactors x.2 / x.2) ≤
      ((j : ℝ) + 1) ^ ArithmeticFunction.cardFactors m / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpos : ∀ x ∈ (oneMod Q K ×ˢ oneMod Q (K ^ j)).filter (fun x => x.1 * x.2 = m),
      1 ≤ x.1 ∧ 1 ≤ x.2 := by
    intro x hx
    have hx' := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
    unfold oneMod at hx'
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hx'.1).1).1,
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hx'.2).1).1⟩
  have hval : ∀ x ∈ (oneMod Q K ×ˢ oneMod Q (K ^ j)).filter (fun x => x.1 * x.2 = m),
      (1 : ℝ) / x.1 * ((j : ℝ) ^ ArithmeticFunction.cardFactors x.2 / x.2) =
        (j : ℝ) ^ ArithmeticFunction.cardFactors (m / x.1) * (1 / m) := by
    intro x hx
    have hxm : x.1 * x.2 = m := (Finset.mem_filter.mp hx).2
    obtain ⟨h1, h2⟩ := hpos x hx
    have hd : m / x.1 = x.2 := by
      rw [← hxm]
      exact Nat.mul_div_cancel_left x.2 (by omega)
    rw [hd, ← hxm]
    have h1' : (x.1 : ℝ) ≠ 0 := by exact_mod_cast (show x.1 ≠ 0 by omega)
    have h2' : (x.2 : ℝ) ≠ 0 := by exact_mod_cast (show x.2 ≠ 0 by omega)
    push_cast
    first | (field_simp; ring) | field_simp
  rw [Finset.sum_congr rfl hval, ← Finset.sum_mul]
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1)
      ((oneMod Q K ×ˢ oneMod Q (K ^ j)).filter (fun x => x.1 * x.2 = m) : Set (ℕ × ℕ)) := by
    intro x hx x' hx' h
    have hx1 := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    have hx2 := Finset.mem_filter.mp (Finset.mem_coe.mp hx')
    have h1 : x.1 = x'.1 := h
    have hp := (hpos x (Finset.mem_coe.mp hx)).1
    have h2 : x.2 = x'.2 := by
      have : x.1 * x.2 = x.1 * x'.2 := by rw [hx1.2, h1, hx2.2]
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    exact Prod.ext h1 h2
  have hsum : ∑ x ∈ (oneMod Q K ×ˢ oneMod Q (K ^ j)).filter (fun x => x.1 * x.2 = m),
      (j : ℝ) ^ ArithmeticFunction.cardFactors (m / x.1) =
      ∑ a ∈ ((oneMod Q K ×ˢ oneMod Q (K ^ j)).filter (fun x => x.1 * x.2 = m)).image
        (fun x => x.1), (j : ℝ) ^ ArithmeticFunction.cardFactors (m / a) :=
    (Finset.sum_image (f := fun a => (j : ℝ) ^ ArithmeticFunction.cardFactors (m / a)) hinj).symm
  have hsub : ((oneMod Q K ×ˢ oneMod Q (K ^ j)).filter (fun x => x.1 * x.2 = m)).image
      (fun x => x.1) ⊆ m.divisors := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    rw [Nat.mem_divisors]
    exact ⟨⟨x.2, (Finset.mem_filter.mp hx).2.symm⟩, by omega⟩
  have hle : ∑ a ∈ ((oneMod Q K ×ˢ oneMod Q (K ^ j)).filter (fun x => x.1 * x.2 = m)).image
        (fun x => x.1), (j : ℝ) ^ ArithmeticFunction.cardFactors (m / a) ≤
      ∑ a ∈ m.divisors, (j : ℝ) ^ ArithmeticFunction.cardFactors (m / a) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)
  have hdiv := sum_divisors_pow_le (j : ℝ) (Nat.cast_nonneg j) m (by omega)
  rw [hsum, div_eq_mul_one_div (((j : ℝ) + 1) ^ _) (m : ℝ)]
  exact mul_le_mul_of_nonneg_right (hle.trans hdiv) (by positivity)

/-- **The `j`-th power of the sum of 1/a**, over the `a` up to `K` with
remainder 1, is at most the sum of `j` to the number of prime factors of `n`
over `n`, over the `n` up to `K^j` with remainder 1. -/
theorem pow_sum_le (Q K : ℕ) : ∀ j : ℕ,
    (∑ a ∈ oneMod Q K, (1 : ℝ) / a) ^ j ≤
      ∑ n ∈ oneMod Q (K ^ j), (j : ℝ) ^ ArithmeticFunction.cardFactors n / n := by
  intro j
  induction j with
  | zero =>
    rw [pow_zero, pow_zero, oneMod_one, Finset.sum_singleton]
    simp
  | succ j ih =>
    have hA0 : 0 ≤ ∑ a ∈ oneMod Q K, (1 : ℝ) / a := Finset.sum_nonneg (fun _ _ => by positivity)
    have hmaps : ∀ x ∈ oneMod Q K ×ˢ oneMod Q (K ^ j), x.1 * x.2 ∈ oneMod Q (K ^ (j + 1)) := by
      intro x hx
      rw [Finset.mem_product] at hx
      obtain ⟨ha, hb⟩ := hx
      unfold oneMod at ha hb ⊢
      rw [Finset.mem_filter, Finset.mem_Icc] at ha hb ⊢
      obtain ⟨⟨ha1, ha2⟩, ha3⟩ := ha
      obtain ⟨⟨hb1, hb2⟩, hb3⟩ := hb
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩, ?_⟩
      · rw [pow_succ, Nat.mul_comm (K ^ j) K]
        exact Nat.mul_le_mul ha2 hb2
      · rw [Nat.mul_mod, ha3, hb3, ← Nat.mul_mod, Nat.one_mul]
    calc (∑ a ∈ oneMod Q K, (1 : ℝ) / a) ^ (j + 1)
        = (∑ a ∈ oneMod Q K, (1 : ℝ) / a) * (∑ a ∈ oneMod Q K, (1 : ℝ) / a) ^ j := pow_succ' _ _
      _ ≤ (∑ a ∈ oneMod Q K, (1 : ℝ) / a) *
            ∑ n ∈ oneMod Q (K ^ j), (j : ℝ) ^ ArithmeticFunction.cardFactors n / n :=
          mul_le_mul_of_nonneg_left ih hA0
      _ = ∑ x ∈ oneMod Q K ×ˢ oneMod Q (K ^ j),
            (1 : ℝ) / x.1 * ((j : ℝ) ^ ArithmeticFunction.cardFactors x.2 / x.2) := by
          rw [Finset.sum_mul_sum, ← Finset.sum_product']
      _ = ∑ m ∈ oneMod Q (K ^ (j + 1)),
            ∑ x ∈ (oneMod Q K ×ˢ oneMod Q (K ^ j)).filter (fun x => x.1 * x.2 = m),
              (1 : ℝ) / x.1 * ((j : ℝ) ^ ArithmeticFunction.cardFactors x.2 / x.2) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ ≤ ∑ m ∈ oneMod Q (K ^ (j + 1)), ((j : ℝ) + 1) ^ ArithmeticFunction.cardFactors m / m := by
          refine Finset.sum_le_sum (fun m hm => ?_)
          have hm1 : 1 ≤ m := by
            unfold oneMod at hm
            exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
          exact fiber_le Q K j m hm1
      _ = ∑ n ∈ oneMod Q (K ^ (j + 1)),
            ((j + 1 : ℕ) : ℝ) ^ ArithmeticFunction.cardFactors n / n := by
          push_cast
          rfl

/-- **The numbers with remainder 1 alone**: the sum of 1/a over the `a` up to `K`
with remainder 1 on division by `Q` is at least log((K + Q)/Q) / Q. -/
theorem log_le_sum_oneMod (Q K : ℕ) (hQ : 0 < Q) :
    Real.log (((K : ℝ) + Q) / Q) / Q ≤ ∑ a ∈ oneMod Q K, (1 : ℝ) / a := by
  obtain ⟨J, hJ⟩ : ∃ J, J = (K + Q - 1) / Q := ⟨_, rfl⟩
  have hdm := Nat.div_add_mod (K + Q - 1) Q
  have hml := Nat.mod_lt (K + Q - 1) hQ
  rw [← hJ] at hdm
  generalize (K + Q - 1) % Q = r at hdm hml
  have hKJ : K ≤ Q * J := by omega
  have hsub : (Finset.range J).image (fun i => 1 + i * Q) ⊆ oneMod Q K := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    rw [Finset.mem_range] at hi
    unfold oneMod
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · have h1 : (i + 1) * Q ≤ K + Q - 1 := by
        rw [hJ] at hi
        exact (Nat.le_div_iff_mul_le hQ).mp hi
      have h2 : (i + 1) * Q = i * Q + Q := by ring
      omega
    · exact Nat.add_mul_mod_self_right 1 i Q
  have h1 : ∑ i ∈ Finset.range J, (1 : ℝ) / ((1 + i * Q : ℕ) : ℝ) ≤
      ∑ a ∈ oneMod Q K, (1 : ℝ) / a := by
    rw [← Finset.sum_image (f := fun a : ℕ => (1 : ℝ) / a) (g := fun i => 1 + i * Q)]
    · exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)
    · intro a _ b _ h
      have h' : 1 + a * Q = 1 + b * Q := h
      exact Nat.eq_of_mul_eq_mul_right hQ (by omega)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h2 : ∑ i ∈ Finset.range J, (1 : ℝ) / ((i : ℝ) + 1) / Q ≤
      ∑ i ∈ Finset.range J, (1 : ℝ) / ((1 + i * Q : ℕ) : ℝ) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    push_cast
    rw [div_div]
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    apply one_div_le_one_div_of_le (by positivity)
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith
  have h3 : Real.log ((J : ℝ) + 1) ≤ ∑ i ∈ Finset.range J, (1 : ℝ) / ((i : ℝ) + 1) := by
    have := log_add_one_le_harmonic J
    unfold harmonic at this
    push_cast at this
    simpa [one_div] using this
  have h4 : Real.log (((K : ℝ) + Q) / Q) ≤ Real.log ((J : ℝ) + 1) := by
    apply Real.log_le_log (div_pos (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]) hQR)
    rw [div_le_iff₀ hQR]
    have : (K : ℝ) ≤ Q * J := by exact_mod_cast hKJ
    linarith
  rw [← Finset.sum_div] at h2
  have h5 : Real.log (((K : ℝ) + Q) / Q) / Q ≤ Real.log ((J : ℝ) + 1) / Q :=
    div_le_div_of_nonneg_right h4 hQR.le
  have h6 : Real.log ((J : ℝ) + 1) / Q ≤ (∑ i ∈ Finset.range J, (1 : ℝ) / ((i : ℝ) + 1)) / Q :=
    div_le_div_of_nonneg_right h3 hQR.le
  linarith

/-- A root rounded down: for `m ≥ 1` there is `t` with `t^m ≤ M < (t + 1)^m`. -/
theorem exists_root (m M : ℕ) (hm : 1 ≤ m) : ∃ t : ℕ, t ^ m ≤ M ∧ M < (t + 1) ^ m := by
  refine ⟨Nat.findGreatest (fun t => t ^ m ≤ M) M, ?_, ?_⟩
  · exact Nat.findGreatest_spec (P := fun t => t ^ m ≤ M) (Nat.zero_le M)
      (by show 0 ^ m ≤ M; rw [zero_pow (by omega)]; exact Nat.zero_le M)
  · by_contra h
    push Not at h
    by_cases hb : Nat.findGreatest (fun t => t ^ m ≤ M) M + 1 ≤ M
    · exact Nat.findGreatest_is_greatest (P := fun t => t ^ m ≤ M) (Nat.lt_succ_self _) hb h
    · have h1 : M < Nat.findGreatest (fun t => t ^ m ≤ M) M + 1 := by omega
      have h2 : Nat.findGreatest (fun t => t ^ m ≤ M) M + 1 ≤
          (Nat.findGreatest (fun t => t ^ m ≤ M) M + 1) ^ m :=
        le_self_pow (by omega) (by omega)
      omega

/-! ## Selberg's pattern sum from below -/

/-- Selberg's term for one wheel: the blocked count over (wheel − blocked count). -/
noncomputable def gw (L : Finset (ℕ × ℕ)) (p : ℕ) : ℝ :=
  (blocked_count L p : ℝ) / ((p : ℝ) - blocked_count L p)

theorem pattern_selberg_sum_eq (L : Finset (ℕ × ℕ)) (z : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    pattern_selberg_sum L z y = setSumW (gw L) (pattern_wheels L z) ⌊Real.sqrt y⌋₊ := by
  have hpf : ∀ T ⊆ pattern_wheels L z, (∏ p ∈ T, p).primeFactors = T := by
    intro T hT
    have hTP : ∀ p ∈ T, p.Prime := fun p hp => pattern_wheels_prime (hT hp)
    have h0 : ∏ p ∈ T, p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hTP p hp).ne_zero)
    ext p
    rw [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hdvd, _⟩
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).mp hdvd
      rwa [(Nat.prime_dvd_prime_iff_eq hp (hTP q hq)).mp hpq]
    · intro hp
      exact ⟨hTP p hp, Finset.dvd_prod_of_mem _ hp, h0⟩
  have hP0 : pattern_wheel_product L z ≠ 0 := by
    unfold pattern_wheel_product
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => (pattern_wheels_prime hp).ne_zero)
  unfold pattern_selberg_sum setSumW
  refine Finset.sum_nbij' (fun l => l.primeFactors) (fun T => ∏ p ∈ T, p) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    rw [Nat.mem_divisors] at hl
    rw [Finset.mem_powerset]
    intro p hp
    exact pattern_mem_of_prime_dvd (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hl.1)
  · intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Nat.mem_divisors]
    refine ⟨?_, hP0⟩
    unfold pattern_wheel_product
    exact Finset.prod_dvd_prod_of_subset T (pattern_wheels L z) (fun p => p) hT
  · intro l hl
    rw [Nat.mem_divisors] at hl
    exact Nat.prod_primeFactors_of_squarefree
      (Squarefree.squarefree_of_dvd hl.1 (pattern_product_squarefree L z))
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact hpf T hT
  · intro l hl
    rw [Nat.mem_divisors] at hl
    have hsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1 (pattern_product_squarefree L z)
    rw [Nat.prod_primeFactors_of_squarefree hsq]
    have hiff : (l : ℝ) ^ 2 ≤ y ↔ l ≤ ⌊Real.sqrt y⌋₊ := by
      rw [Nat.le_floor_iff (Real.sqrt_nonneg y)]
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      have hs := Real.sq_sqrt hy
      have hs0 := Real.sqrt_nonneg y
      constructor
      · intro h
        by_contra h'
        push Not at h'
        nlinarith
      · intro h
        nlinarith
    by_cases h : (l : ℝ) ^ 2 ≤ y
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
      rfl
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h'))]

set_option maxHeartbeats 1000000 in
theorem pattern_selberg_sum_lower_step (h_le : blocked_le_card) (h_eq : blocked_eq_card_iff) :
    pattern_selberg_sum_lower := by
  intro k hk
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = k.factorial := ⟨_, rfl⟩
  have hQ : 0 < Q := by rw [hQdef]; exact Nat.factorial_pos k
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkQ : (0 : ℝ) < 4 * k * Q := by nlinarith
  refine ⟨1 / (4 * k * Q : ℝ) ^ k, (Q : ℝ) ^ (4 * k), div_pos one_pos (pow_pos hkQ k),
    one_le_pow₀ hQR, ?_⟩
  intro L hL hLk z y hy hyz
  have hy1 : (1 : ℝ) ≤ y := le_trans (one_le_pow₀ hQR) hy
  have hy0 : (0 : ℝ) < y := by linarith
  -- the sizes
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊Real.sqrt y⌋₊ := ⟨_, rfl⟩
  obtain ⟨K, hK1, hK2⟩ := exists_root k M hk
  have hz0 : (0 : ℝ) < z := by
    by_contra h
    push Not at h
    have : (z : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg z)
    rw [this] at hyz
    linarith
  have hMz : M < z := by
    have h1 : (M : ℝ) ≤ Real.sqrt y := by rw [hM]; exact Nat.floor_le (Real.sqrt_nonneg y)
    have h2 : Real.sqrt y < z := (Real.sqrt_lt' hz0).mpr hyz
    exact_mod_cast h1.trans_lt h2
  -- the wheels larger than `k` below the cut-off
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ, S = (active_primes z).filter (fun p => k < p) := ⟨_, rfl⟩
  have hmemS : ∀ {p : ℕ}, p ∈ S ↔ p.Prime ∧ p < z ∧ k < p := by
    intro p
    rw [hSdef]
    unfold active_primes
    simp only [Finset.mem_filter, Finset.mem_range]
    tauto
  have hcop : ∀ ℓ ∈ L, Nat.Coprime ℓ.1 ℓ.2 := fun ℓ hℓ => (hL ℓ hℓ).2
  have hρk : ∀ p ∈ S, blocked_count L p ≤ k := by
    intro p hp
    have := h_le L p (hmemS.mp hp).1 hcop
    unfold blocked_count
    omega
  -- the actual sum equals the sum over `S`
  have hsub : pattern_wheels L z ⊆ S := by
    intro p hp
    obtain ⟨h1, h2, h3, _⟩ := mem_pattern_wheels.mp hp
    exact hmemS.mpr ⟨h1, h2, by omega⟩
  have hzero : ∀ p ∈ S, p ∉ pattern_wheels L z → gw L p = 0 := by
    intro p hp hpn
    obtain ⟨h1, h2, h3⟩ := hmemS.mp hp
    have h0 : blocked_count L p = 0 := by
      by_contra h
      exact hpn (mem_pattern_wheels.mpr ⟨h1, h2, by omega, Nat.pos_of_ne_zero h⟩)
    unfold gw
    rw [h0]
    simp
  have hG : pattern_selberg_sum L z y = setSumW (gw L) S M := by
    rw [pattern_selberg_sum_eq L z y hy0.le, ← hM]
    exact setSumW_subset hsub hzero M
  -- the weights on `S`
  have hw : ∀ p ∈ S, 0 < p ∧ 0 ≤ gw L p ∧ gw L p ≤ kw k p := by
    intro p hp
    obtain ⟨h1, _, h3⟩ := hmemS.mp hp
    have hr := hρk p hp
    have hpR : (k : ℝ) < p := by exact_mod_cast h3
    have hrR : (blocked_count L p : ℝ) ≤ k := by exact_mod_cast hr
    have hr0 : (0 : ℝ) ≤ blocked_count L p := Nat.cast_nonneg _
    refine ⟨h1.pos, ?_, ?_⟩
    · unfold gw
      exact div_nonneg hr0 (by linarith)
    · unfold gw kw
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
  have hrep := setSumW_replace (gw L) (kw k) S hw M
  have hsmooth := smoothSumK_le_setSumW k S (fun p hp => ⟨(hmemS.mp hp).1, (hmemS.mp hp).2.2⟩) M
  have hpow := pow_sum_le Q K k
  have hlog := log_le_sum_oneMod Q K hQ
  -- the numbers with remainder 1 up to `K^k` are built from `S`
  have hsm : ∑ n ∈ oneMod Q (K ^ k), (k : ℝ) ^ ArithmeticFunction.cardFactors n / n ≤
      smoothSumK k S M := by
    unfold smoothSumK
    have hsub' : oneMod Q (K ^ k) ⊆ Finset.Icc 1 M := by
      intro n hn
      unfold oneMod at hn
      have := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      exact Finset.mem_Icc.mpr ⟨this.1, this.2.trans hK1⟩
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub'
      (fun n _ _ => smoothTermK_nonneg k S n))
    refine Finset.sum_le_sum (fun n hn => le_of_eq ?_)
    unfold oneMod at hn
    obtain ⟨hnI, hnmod⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hnI
    have hpf : n.primeFactors ⊆ S := by
      intro p hp
      have hpP := Nat.prime_of_mem_primeFactors hp
      have hpn := Nat.dvd_of_mem_primeFactors hp
      have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
      have hKz : K ^ k < z := lt_of_le_of_lt hK1 hMz
      refine hmemS.mpr ⟨hpP, by omega, ?_⟩
      by_contra hpk
      push Not at hpk
      have h2 := hpP.two_le
      have hpQ : p ∣ Q := by
        rw [hQdef]
        exact Nat.dvd_factorial hpP.pos hpk
      have hk2 : 2 ≤ k := by omega
      have hQ2 : 2 ≤ Q := by
        rw [hQdef]
        exact le_trans hk2 (Nat.self_le_factorial k)
      have hdm := Nat.div_add_mod n Q
      have hmod : p ∣ n % Q := by
        have h' : p ∣ Q * (n / Q) + n % Q := by rw [hdm]; exact hpn
        exact (Nat.dvd_add_right (Dvd.dvd.mul_right hpQ _)).mp h'
      rw [hnmod, Nat.mod_eq_of_lt (by omega)] at hmod
      exact hpP.one_lt.ne' (Nat.dvd_one.mp hmod)
    unfold smoothTermK
    rw [ite_eq_left hpf]
  -- logarithms: `y < (K + 1)^(2k)`
  have hyK : Real.log y < 2 * k * Real.log ((K : ℝ) + 1) := by
    have hM1 : Real.sqrt y < (M : ℝ) + 1 := by rw [hM]; exact Nat.lt_floor_add_one _
    have hK2R : (M : ℝ) + 1 ≤ ((K : ℝ) + 1) ^ k := by
      have : M + 1 ≤ (K + 1) ^ k := hK2
      exact_mod_cast this
    have hs := Real.sq_sqrt hy0.le
    have hs0 := Real.sqrt_nonneg y
    have h3 : y < ((M : ℝ) + 1) ^ 2 := by nlinarith
    have h4 : ((M : ℝ) + 1) ^ 2 ≤ (((K : ℝ) + 1) ^ k) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hK2R 2
    have h5 : y < ((K : ℝ) + 1) ^ (2 * k) := by
      rw [pow_mul']
      linarith
    have := Real.log_lt_log hy0 h5
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hlogQ : 4 * k * Real.log Q ≤ Real.log y := by
    have := Real.log_le_log (pow_pos (by linarith) _) hy
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hKlog : Real.log ((K : ℝ) + 1) - Real.log Q ≤ Real.log (((K : ℝ) + Q) / Q) := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    rw [Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))]
    have : Real.log ((K : ℝ) + 1) ≤ Real.log ((K : ℝ) + Q) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hkpos : (0 : ℝ) < k := by linarith
  have hk2 : (0 : ℝ) < 2 * k := by linarith
  have hk4 : (0 : ℝ) < 4 * k := by linarith
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hL1 : Real.log y / (4 * k * Q) ≤ ∑ a ∈ oneMod Q K, (1 : ℝ) / a := by
    have hlq : Real.log y / (4 * k) ≤ Real.log ((K : ℝ) + 1) - Real.log Q := by
      have h1 : Real.log y / (2 * k) < Real.log ((K : ℝ) + 1) := by
        rw [div_lt_iff₀ hk2]
        linarith
      have h2 : Real.log Q ≤ Real.log y / (4 * k) := by
        rw [le_div_iff₀ hk4]
        linarith
      have h3 : Real.log y / (2 * k) = 2 * (Real.log y / (4 * k)) := by
        first | (field_simp; ring) | field_simp
      linarith
    calc Real.log y / (4 * k * Q) = (Real.log y / (4 * k)) / Q := by
          rw [div_div]
      _ ≤ Real.log (((K : ℝ) + Q) / Q) / Q :=
          div_le_div_of_nonneg_right (hlq.trans hKlog) (by positivity)
      _ ≤ _ := hlog
  have hL0 : 0 ≤ Real.log y / (4 * k * Q) := div_nonneg hlogy0 hkQ.le
  have hLpow : (Real.log y / (4 * k * Q)) ^ k ≤ (∑ a ∈ oneMod Q K, (1 : ℝ) / a) ^ k :=
    pow_le_pow_left₀ hL0 hL1 k
  -- the bad factor
  have hratio : ∀ p ∈ S, 1 + kw k p = (1 + gw L p) * (((p : ℝ) - blocked_count L p) /
      ((p : ℝ) - k)) := by
    intro p hp
    have hpR : (k : ℝ) < p := by exact_mod_cast (hmemS.mp hp).2.2
    have hrR : (blocked_count L p : ℝ) ≤ k := by exact_mod_cast hρk p hp
    unfold gw kw
    have h1 : (p : ℝ) - k ≠ 0 := by linarith
    have h2 : (p : ℝ) - blocked_count L p ≠ 0 := by linarith
    first | (field_simp; ring) | field_simp
  have hprodeq : ∏ p ∈ S, (1 + kw k p) =
      (∏ p ∈ S, (1 + gw L p)) * ∏ p ∈ S, (((p : ℝ) - blocked_count L p) / ((p : ℝ) - k)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hratio
  have hfac_one : ∀ p, p.Prime → k < p →
      1 ≤ ((p : ℝ) - blocked_count L p) / ((p : ℝ) - k) := by
    intro p hp hpk
    have hpR : (k : ℝ) < p := by exact_mod_cast hpk
    have hrR : (blocked_count L p : ℝ) ≤ k := by
      have := h_le L p hp hcop
      unfold blocked_count
      rw [← hLk]
      exact_mod_cast this
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hbad : ∏ p ∈ S, (((p : ℝ) - blocked_count L p) / ((p : ℝ) - k)) ≤ bad_factor L := by
    have hfilt : ∏ p ∈ S.filter (fun p => blocked_count L p ≠ k),
        (((p : ℝ) - blocked_count L p) / ((p : ℝ) - k)) =
        ∏ p ∈ S, (((p : ℝ) - blocked_count L p) / ((p : ℝ) - k)) := by
      apply Finset.prod_filter_of_ne
      intro p _ hne hk'
      apply hne
      rw [hk']
      have hpR : (k : ℝ) < p := by exact_mod_cast (hmemS.mp ‹p ∈ S›).2.2
      exact div_self (by linarith)
    rw [← hfilt]
    unfold bad_factor
    rw [hLk]
    apply Finset.prod_le_prod_of_subset_of_one_le₀
    · intro p hp
      obtain ⟨hpS, hne⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1, _, h3⟩ := hmemS.mp hpS
      rw [Finset.mem_filter, Nat.mem_primeFactors]
      refine ⟨⟨h1, ?_, Int.natAbs_ne_zero.mpr (bad_product_ne_zero hL)⟩, h3⟩
      have hd : (p : ℤ) ∣ bad_product L := by
        by_contra hnd
        apply hne
        have := (h_eq L p h1 hcop).mpr hnd
        unfold blocked_count
        rw [this, hLk]
      exact Int.natCast_dvd.mp hd
    · intro p hp
      have := hfac_one p (hmemS.mp (Finset.mem_filter.mp hp).1).1
        (hmemS.mp (Finset.mem_filter.mp hp).1).2.2
      linarith
    · intro p hp _
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      exact hfac_one p (Nat.prime_of_mem_primeFactors hp1) hp2
  -- putting it together
  have hPg : 0 < ∏ p ∈ S, (1 + gw L p) :=
    Finset.prod_pos (fun p hp => by linarith [(hw p hp).2.1])
  have hGg0 : 0 ≤ setSumW (gw L) S M := setSumW_nonneg (fun p hp => (hw p hp).2.1) M
  have hkey : setSumW (kw k) S M ≤
      (∏ p ∈ S, (((p : ℝ) - blocked_count L p) / ((p : ℝ) - k))) * setSumW (gw L) S M := by
    rw [hprodeq] at hrep
    have h' : (∏ p ∈ S, (1 + gw L p)) * setSumW (kw k) S M ≤
        (∏ p ∈ S, (1 + gw L p)) * ((∏ p ∈ S, (((p : ℝ) - blocked_count L p) /
          ((p : ℝ) - k))) * setSumW (gw L) S M) := by
      calc (∏ p ∈ S, (1 + gw L p)) * setSumW (kw k) S M ≤ _ := hrep
        _ = _ := by ring
    exact le_of_mul_le_mul_left h' hPg
  have hbadG : (∏ p ∈ S, (((p : ℝ) - blocked_count L p) / ((p : ℝ) - k))) *
      setSumW (gw L) S M ≤ bad_factor L * setSumW (gw L) S M :=
    mul_le_mul_of_nonneg_right hbad hGg0
  rw [hG]
  calc 1 / (4 * k * Q : ℝ) ^ k * Real.log y ^ k = (Real.log y / (4 * k * Q)) ^ k := by
        rw [div_pow]
        ring
    _ ≤ (∑ a ∈ oneMod Q K, (1 : ℝ) / a) ^ k := hLpow
    _ ≤ ∑ n ∈ oneMod Q (K ^ k), (k : ℝ) ^ ArithmeticFunction.cardFactors n / n := hpow
    _ ≤ smoothSumK k S M := hsm
    _ ≤ setSumW (kw k) S M := hsmooth
    _ ≤ _ := hkey
    _ ≤ _ := hbadG

/-! ## The pattern as a Selberg sieve problem -/

/-- The share of a divisor: the product over its prime factors of the blocked
count over the prime. -/
noncomputable def pattern_nu (L : Finset (ℕ × ℕ)) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (blocked_count L p : ℝ) / p)

theorem pattern_nu_apply (L : Finset (ℕ × ℕ)) {d : ℕ} (hd : d ≠ 0) :
    pattern_nu L d = ∏ p ∈ d.primeFactors, (blocked_count L p : ℝ) / p :=
  ArithmeticFunction.prodPrimeFactors_apply hd

theorem pattern_nu_prime (L : Finset (ℕ × ℕ)) {p : ℕ} (hp : p.Prime) :
    pattern_nu L p = (blocked_count L p : ℝ) / p := by
  rw [pattern_nu_apply L hp.ne_zero, hp.primeFactors, Finset.prod_singleton]

/-- The pattern as a Selberg sieve problem. -/
noncomputable def pattern_sieve (L : Finset (ℕ × ℕ)) (N z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (hlt : ∀ p ∈ pattern_wheels L z, blocked_count L p < p) : SelbergSieve where
  support := (Finset.Ioc 0 N).image (pattern_value L)
  prodPrimes := pattern_wheel_product L z
  prodPrimes_squarefree := pattern_product_squarefree L z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := pattern_nu L
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime := fun p hp hpd => by
    rw [pattern_nu_prime L hp]
    have hm := mem_pattern_wheels.mp (pattern_mem_of_prime_dvd hp hpd)
    have h1 : (0 : ℝ) < blocked_count L p := by exact_mod_cast hm.2.2.2
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact div_pos h1 this
  nu_lt_one_of_prime := fun p hp hpd => by
    rw [pattern_nu_prime L hp]
    have h1 : (blocked_count L p : ℝ) < p := by
      exact_mod_cast hlt p (pattern_mem_of_prime_dvd hp hpd)
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [div_lt_one this]
    exact h1
  level := y
  one_le_level := hy

theorem pattern_value_lt {L : Finset (ℕ × ℕ)} (hne : L.Nonempty) (hL : primitive_forms L)
    {m m' : ℕ} (hm : 1 ≤ m) (h : m < m') : pattern_value L m < pattern_value L m' := by
  unfold pattern_value
  apply Finset.prod_lt_prod_of_nonempty₀ _ _ hne
  · intro ℓ hℓ
    have := (hL ℓ hℓ).1
    have : 1 ≤ ℓ.1 * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  · intro ℓ hℓ
    have h1 := (hL ℓ hℓ).1
    have : ℓ.1 * m < ℓ.1 * m' := Nat.mul_lt_mul_of_pos_left h (by omega)
    omega

theorem pattern_value_injOn {L : Finset (ℕ × ℕ)} (hne : L.Nonempty) (hL : primitive_forms L)
    (N : ℕ) : Set.InjOn (pattern_value L) (Finset.Ioc 0 N : Set ℕ) := by
  intro a ha b hb h
  have ha1 := (Finset.mem_Ioc.mp (Finset.mem_coe.mp ha)).1
  have hb1 := (Finset.mem_Ioc.mp (Finset.mem_coe.mp hb)).1
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (pattern_value_lt hne hL (by omega) hab).ne
  · exact hab
  · exact absurd h (pattern_value_lt hne hL (by omega) hab).ne'

theorem pattern_card_image_filter {L : Finset (ℕ × ℕ)} (hne : L.Nonempty)
    (hL : primitive_forms L) (N : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    (((Finset.Ioc 0 N).image (pattern_value L)).filter q).card =
      ((Finset.Ioc 0 N).filter (fun m => q (pattern_value L m))).card := by
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  exact (pattern_value_injOn hne hL N).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))

theorem pattern_sifted_eq {L : Finset (ℕ × ℕ)} (hne : L.Nonempty) (hL : primitive_forms L)
    (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) (hlt : ∀ p ∈ pattern_wheels L z, blocked_count L p < p) :
    BoundingSieve.siftedSum (s := (pattern_sieve L N z y hy hlt).toBoundingSieve) =
      (pattern_sifted L N z : ℝ) := by
  unfold BoundingSieve.siftedSum pattern_sifted
  show (∑ d ∈ (Finset.Ioc 0 N).image (pattern_value L),
      if Nat.Coprime (pattern_wheel_product L z) d then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole, pattern_card_image_filter hne hL]

theorem pattern_multSum_eq {L : Finset (ℕ × ℕ)} (hne : L.Nonempty) (hL : primitive_forms L)
    (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) (hlt : ∀ p ∈ pattern_wheels L z, blocked_count L p < p)
    (d : ℕ) :
    BoundingSieve.multSum (s := (pattern_sieve L N z y hy hlt).toBoundingSieve) d =
      (((Finset.Ioc 0 N).filter (fun m => d ∣ pattern_value L m)).card : ℝ) := by
  unfold BoundingSieve.multSum
  show (∑ n ∈ (Finset.Ioc 0 N).image (pattern_value L),
      if d ∣ n then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole, pattern_card_image_filter hne hL]

theorem pattern_rem_le {L : Finset (ℕ × ℕ)} (hne : L.Nonempty) (hL : primitive_forms L)
    (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) (hlt : ∀ p ∈ pattern_wheels L z, blocked_count L p < p)
    (h_mc : pattern_multiples_count) (h_le : blocked_le_card)
    {d : ℕ} (hd : d ∣ pattern_wheel_product L z) :
    |BoundingSieve.rem (s := (pattern_sieve L N z y hy hlt).toBoundingSieve) d| ≤
      (L.card : ℝ) ^ ArithmeticFunction.cardDistinctFactors d := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd (pattern_product_squarefree L z)
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hDP : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsq
  have hprod' : d.primeFactors.prod id = d := hprod
  have hnu : pattern_nu L d = (pattern_rho L d.primeFactors : ℝ) / d := by
    rw [pattern_nu_apply L hd0, Finset.prod_div_distrib]
    unfold pattern_rho
    rw [Nat.cast_prod]
    congr 1
    rw [← Nat.cast_prod, hprod]
  have hcop : ∀ ℓ ∈ L, Nat.Coprime ℓ.1 ℓ.2 := fun ℓ hℓ => (hL ℓ hℓ).2
  have hrho : (pattern_rho L d.primeFactors : ℝ) ≤
      (L.card : ℝ) ^ ArithmeticFunction.cardDistinctFactors d := by
    rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors]
    have : pattern_rho L d.primeFactors ≤ L.card ^ d.primeFactors.card := by
      unfold pattern_rho
      exact Finset.prod_le_pow_card _ _ _ (fun p hp => h_le L p (hDP p hp) hcop)
    exact_mod_cast this
  have key := h_mc L d.primeFactors N hDP
  rw [hprod'] at key
  unfold BoundingSieve.rem
  rw [pattern_multSum_eq hne hL]
  show |(_ : ℝ) - pattern_nu L d * N| ≤ _
  rw [hnu]
  refine le_trans (le_of_eq ?_) (key.trans hrho)
  congr 1
  ring

theorem pattern_bounding_eq {L : Finset (ℕ × ℕ)} (N z : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (hlt : ∀ p ∈ pattern_wheels L z, blocked_count L p < p) :
    RNS.SelbergBound.bounding_sum (pattern_sieve L N z y hy hlt) = pattern_selberg_sum L z y := by
  unfold RNS.SelbergBound.bounding_sum pattern_selberg_sum
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hld : l ∣ pattern_wheel_product L z := Nat.dvd_of_mem_divisors hl
  have hl0 : l ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hl)
  have hg : (pattern_sieve L N z y hy hlt).toBoundingSieve.selbergTerms l =
      ∏ p ∈ l.primeFactors, (blocked_count L p : ℝ) / ((p : ℝ) - blocked_count L p) := by
    rw [BoundingSieve.selbergTerms_apply]
    show pattern_nu L l * ∏ p ∈ l.primeFactors, (1 - pattern_nu L p)⁻¹ = _
    rw [pattern_nu_apply L hl0, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpP := Nat.prime_of_mem_primeFactors hp
    have hlt' : (blocked_count L p : ℝ) < p := by
      exact_mod_cast hlt p (pattern_mem_of_prime_dvd hpP
        ((Nat.dvd_of_mem_primeFactors hp).trans hld))
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    rw [pattern_nu_prime L hpP]
    have h1 : (p : ℝ) ≠ 0 := by linarith
    have h2 : (p : ℝ) - blocked_count L p ≠ 0 := by linarith
    have h3 : (1 : ℝ) - blocked_count L p / p ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      rw [eq_div_iff h1] at h
      linarith
    field_simp
  rw [hg]
  rfl

theorem pattern_sieve_bound_step (h_sb : RNS.SelbergBound.selberg_bound)
    (h_mc : pattern_multiples_count) (h_le : blocked_le_card) : pattern_sieve_bound := by
  intro L hne hL N z y hy
  have hcop : ∀ ℓ ∈ L, Nat.Coprime ℓ.1 ℓ.2 := fun ℓ hℓ => (hL ℓ hℓ).2
  have hlt : ∀ p ∈ pattern_wheels L z, blocked_count L p < p := by
    intro p hp
    obtain ⟨h1, _, h3, _⟩ := mem_pattern_wheels.mp hp
    have := h_le L p h1 hcop
    unfold blocked_count
    omega
  have h := h_sb (pattern_sieve L N z y hy hlt)
  rw [pattern_sifted_eq hne hL, pattern_bounding_eq] at h
  refine h.trans (add_le_add le_rfl (Finset.sum_le_sum (fun d hd => ?_)))
  show (if (d : ℝ) ≤ y then (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
      |BoundingSieve.rem (s := (pattern_sieve L N z y hy hlt).toBoundingSieve) d| else 0) ≤
    if (d : ℝ) ≤ y then (3 * (L.card : ℝ)) ^ ArithmeticFunction.cardDistinctFactors d else 0
  split_ifs with hdy
  · have hr := pattern_rem_le hne hL N z y hy hlt h_mc h_le (Nat.dvd_of_mem_divisors hd)
    calc (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
          |BoundingSieve.rem (s := (pattern_sieve L N z y hy hlt).toBoundingSieve) d|
        ≤ (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
          (L.card : ℝ) ^ ArithmeticFunction.cardDistinctFactors d :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (3 * (L.card : ℝ)) ^ ArithmeticFunction.cardDistinctFactors d := by
          rw [← mul_pow]
  · exact le_rfl

/-! ## The count -/

theorem pattern_count_le_sifted {L : Finset (ℕ × ℕ)} (hL : primitive_forms L) (N z : ℕ) :
    pattern_count L N ≤ z + pattern_sifted L N z := by
  unfold pattern_count pattern_sifted
  have hsub : (Finset.Ioc 0 N).filter (fun n => ∀ ℓ ∈ L, (ℓ.1 * n + ℓ.2).Prime) ⊆
      Finset.range z ∪ (Finset.Ioc 0 N).filter
        (fun m => Nat.Coprime (pattern_wheel_product L z) (pattern_value L m)) := by
    intro n hn
    obtain ⟨hnN, hp⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_filter]
    by_cases hnz : n < z
    · exact Or.inl hnz
    · right
      refine ⟨hnN, ?_⟩
      unfold pattern_value
      apply Nat.Coprime.prod_right
      intro ℓ hℓ
      have hpr := hp ℓ hℓ
      refine ((hpr.coprime_iff_not_dvd).mpr (fun h => hnz ?_)).symm
      obtain ⟨_, hlz, _, _⟩ := mem_pattern_wheels.mp (pattern_mem_of_prime_dvd hpr h)
      have h1 := (hL ℓ hℓ).1
      have : n ≤ ℓ.1 * n := Nat.le_mul_of_pos_left n (by omega)
      omega
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_range]

/-- `3k` to the number of prime factors of a divisor of the wheel product is at
most its square. -/
theorem err_pow_le_sq {L : Finset (ℕ × ℕ)} {z d : ℕ} (hd : d ∣ pattern_wheel_product L z) :
    (3 * (L.card : ℝ)) ^ ArithmeticFunction.cardDistinctFactors d ≤ (d : ℝ) ^ 2 := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd (pattern_product_squarefree L z)
  have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsq
  conv_rhs => rw [← hprod]
  push_cast
  rw [ArithmeticFunction.cardDistinctFactors_eq_card_primeFactors, ← Finset.prod_const,
    ← Finset.prod_pow]
  apply Finset.prod_le_prod₀
  · intro p _
    positivity
  · intro p hp
    have hm := mem_pattern_wheels.mp (pattern_mem_of_prime_dvd (Nat.prime_of_mem_primeFactors hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hd))
    have hk : (L.card : ℝ) + 1 ≤ p := by exact_mod_cast hm.2.2.1
    have hk0 : (0 : ℝ) ≤ L.card := Nat.cast_nonneg _
    nlinarith [mul_le_mul hk hk (by linarith) (by linarith), sq_nonneg ((L.card : ℝ) - 1)]

/-- The error at level t² is at most t⁶. -/
theorem pattern_error_le (L : Finset (ℕ × ℕ)) (z t : ℕ) :
    (∑ d ∈ Nat.divisors (pattern_wheel_product L z),
      if (d : ℝ) ≤ (t : ℝ) ^ 2 then
        (3 * (L.card : ℝ)) ^ ArithmeticFunction.cardDistinctFactors d else 0)
      ≤ (t : ℝ) ^ 6 := by
  calc _ ≤ ∑ d ∈ Nat.divisors (pattern_wheel_product L z),
        if d ∈ Finset.Icc 1 (t ^ 2) then (t : ℝ) ^ 4 else 0 := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        have hd' := Nat.mem_divisors.mp hd
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
        by_cases h : (d : ℝ) ≤ (t : ℝ) ^ 2
        · have hdt : d ≤ t ^ 2 := by exact_mod_cast h
          rw [ite_eq_left h, ite_eq_left (Finset.mem_Icc.mpr ⟨hd1, hdt⟩)]
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          calc (3 * (L.card : ℝ)) ^ ArithmeticFunction.cardDistinctFactors d ≤ (d : ℝ) ^ 2 :=
                err_pow_le_sq hd'.1
            _ ≤ ((t : ℝ) ^ 2) ^ 2 := by nlinarith
            _ = (t : ℝ) ^ 4 := by ring
        · rw [ite_eq_right h]
          split_ifs
          · positivity
          · exact le_rfl
    _ = ∑ d ∈ Nat.divisors (pattern_wheel_product L z) ∩ Finset.Icc 1 (t ^ 2), (t : ℝ) ^ 4 :=
        Finset.sum_ite_mem _ _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (t ^ 2), (t : ℝ) ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun _ _ _ => by positivity)
    _ = (t : ℝ) ^ 6 := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        push_cast
        ring

theorem bad_factor_one_le {L : Finset (ℕ × ℕ)} (hL : primitive_forms L)
    (h_le : blocked_le_card) : 1 ≤ bad_factor L := by
  unfold bad_factor
  apply Finset.one_le_prod₀
  intro q hq
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
  have hqP := Nat.prime_of_mem_primeFactors hq1
  have hpR : (L.card : ℝ) < q := by exact_mod_cast hq2
  have hrR : (blocked_count L q : ℝ) ≤ L.card := by
    have := h_le L q hqP (fun ℓ hℓ => (hL ℓ hℓ).2)
    unfold blocked_count
    exact_mod_cast this
  rw [le_div_iff₀ (by linarith)]
  linarith

set_option maxHeartbeats 1000000 in
theorem pattern_count_le_step (h_sieve : pattern_sieve_bound) (h_low : pattern_selberg_sum_lower)
    (h_le : blocked_le_card) : pattern_count_le := by
  intro k hk
  obtain ⟨c, y₀, hc, hy₀1, hlow⟩ := h_low k hk
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = k + 6 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = ⌈y₀⌉₊ := ⟨_, rfl⟩
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hmR : (m : ℝ) = k + 6 := by rw [hmdef]; push_cast; ring
  have hm0 : (0 : ℝ) < m := by linarith
  refine ⟨3 * (m : ℝ) ^ k + (m : ℝ) ^ k / c,
    max (((T + 1 : ℕ) : ℝ) ^ m) ((4 : ℝ) ^ m), ?_⟩
  intro L hL hLk N hN
  have hne : L.Nonempty := by
    rw [← Finset.card_pos, hLk]
    omega
  have hbad := bad_factor_one_le hL h_le
  have hN1 : ((T + 1 : ℕ) : ℝ) ^ m ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hN4 : (4 : ℝ) ^ m ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have hm1 : 1 ≤ m := by omega
  obtain ⟨t, hlo, hhi⟩ := exists_root m N hm1
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN4
  have htT : T + 1 ≤ t + 1 := by
    by_contra h
    push Not at h
    have h' : t + 1 ≤ T + 1 := by omega
    have h1 : (t + 1) ^ m ≤ (T + 1) ^ m := Nat.pow_le_pow_left h' m
    have h2 : (N : ℝ) < ((t + 1 : ℕ) : ℝ) ^ m := by exact_mod_cast hhi
    have h3 : ((t + 1 : ℕ) : ℝ) ^ m ≤ ((T + 1 : ℕ) : ℝ) ^ m := by exact_mod_cast h1
    linarith
  have hty : y₀ ≤ (t : ℝ) := by
    have h1 : y₀ ≤ (T : ℝ) := by rw [hT]; exact Nat.le_ceil y₀
    have h2 : (T : ℝ) ≤ t := by exact_mod_cast (show T ≤ t by omega)
    linarith
  have ht1 : (1 : ℝ) ≤ t := le_trans hy₀1 hty
  have ht0 : (0 : ℝ) < t := by linarith
  have hloR : (t : ℝ) ^ m ≤ N := by exact_mod_cast hlo
  have hhiR : (N : ℝ) < ((t : ℝ) + 1) ^ m := by exact_mod_cast hhi
  -- logarithms
  have hLt : Real.log N < m * Real.log ((t : ℝ) + 1) := by
    have := Real.log_lt_log hNpos hhiR
    rw [Real.log_pow] at this
    exact this
  have hL4 : m * Real.log 4 ≤ Real.log N := by
    have := Real.log_le_log (by positivity) hN4
    rw [Real.log_pow] at this
    exact this
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL4' : 0 < (m : ℝ) * Real.log 4 := mul_pos hm0 (by rw [hlog4]; linarith)
  have hLpos : 0 < Real.log N := by linarith
  have hlogt1 : Real.log ((t : ℝ) + 1) ≤ Real.log 2 + Real.log t := by
    rw [← Real.log_mul (by norm_num) ht0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hlogt1' : Real.log ((t : ℝ) + 1) ≤ t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (t : ℝ) + 1 by positivity)
    linarith
  -- the level t² and the cut-off t² + 1
  have hy1 : (1 : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
  have hyt : y₀ ≤ (t : ℝ) ^ 2 := by nlinarith
  have hyz : (t : ℝ) ^ 2 < ((t ^ 2 + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have hG := hlow L hL hLk (t ^ 2 + 1) ((t : ℝ) ^ 2) hyt hyz
  have hsieve := h_sieve L hne hL N (t ^ 2 + 1) ((t : ℝ) ^ 2) hy1
  have hE := pattern_error_le L (t ^ 2 + 1) t
  have hcount : (pattern_count L N : ℝ) ≤
      (t : ℝ) ^ 2 + 1 + (pattern_sifted L N (t ^ 2 + 1) : ℝ) := by
    have := pattern_count_le_sifted hL N (t ^ 2 + 1)
    exact_mod_cast this
  -- log of the level is at least log N / m
  have hlt2 : Real.log ((t : ℝ) ^ 2) = 2 * Real.log t := by
    rw [Real.log_pow]
    push_cast
    ring
  have hlevel : Real.log N / m ≤ Real.log ((t : ℝ) ^ 2) := by
    rw [hlt2, div_le_iff₀ hm0]
    have hmt := mul_le_mul_of_nonneg_left hlogt1 hm0.le
    rw [hlog4] at hL4
    linarith
  have hlevel0 : 0 ≤ Real.log N / m := div_nonneg hLpos.le hm0.le
  have hlevk : (Real.log N / m) ^ k ≤ Real.log ((t : ℝ) ^ 2) ^ k :=
    pow_le_pow_left₀ hlevel0 hlevel k
  set P := Real.log N ^ k with hP
  have hPpos : 0 < P := pow_pos hLpos k
  set G := pattern_selberg_sum L (t ^ 2 + 1) ((t : ℝ) ^ 2) with hGdef
  have hcP : c * P / (m : ℝ) ^ k ≤ bad_factor L * G := by
    have h1 : c * ((Real.log N / m) ^ k) ≤ c * Real.log ((t : ℝ) ^ 2) ^ k :=
      mul_le_mul_of_nonneg_left hlevk hc.le
    have h2 : c * ((Real.log N / m) ^ k) = c * P / (m : ℝ) ^ k := by
      rw [hP, div_pow]
      ring
    linarith
  have hcP0 : 0 < c * P / (m : ℝ) ^ k := div_pos (mul_pos hc hPpos) (pow_pos hm0 k)
  have hbG : 0 < bad_factor L * G := lt_of_lt_of_le hcP0 hcP
  have hGpos : 0 < G := by
    by_contra h
    push Not at h
    have : bad_factor L * G ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
    linarith
  have hmain : (N : ℝ) / G ≤ (m : ℝ) ^ k / c * bad_factor L * N / P := by
    have hmk : (0 : ℝ) < (m : ℝ) ^ k := pow_pos hm0 k
    rw [div_le_div_iff₀ hGpos hPpos]
    have h1 : (N : ℝ) * (c * P / (m : ℝ) ^ k) ≤ N * (bad_factor L * G) :=
      mul_le_mul_of_nonneg_left hcP hNpos.le
    have hcne : c ≠ 0 := ne_of_gt hc
    have hmkne : (m : ℝ) ^ k ≠ 0 := ne_of_gt hmk
    have h2 : (N : ℝ) * (c * P / (m : ℝ) ^ k) * ((m : ℝ) ^ k / c) = N * P := by
      first | (field_simp; ring) | field_simp
    have h3 : (N : ℝ) * (bad_factor L * G) * ((m : ℝ) ^ k / c) =
        (m : ℝ) ^ k / c * bad_factor L * N * G := by ring
    have h4 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ (m : ℝ) ^ k / c from
      div_nonneg hmk.le hc.le)
    linarith
  -- the error and the cut-off are at most a constant times N / log^k N
  have hLle : Real.log N ≤ m * t := by
    have := mul_le_mul_of_nonneg_left hlogt1' hm0.le
    linarith
  have hPle : P ≤ (m : ℝ) ^ k * (t : ℝ) ^ k := by
    rw [hP, ← mul_pow]
    exact pow_le_pow_left₀ hLpos.le hLle k
  have ht6 : (t : ℝ) ^ 6 ≤ (m : ℝ) ^ k * N / P := by
    rw [le_div_iff₀ hPpos]
    have h1 : (t : ℝ) ^ 6 * P ≤ (t : ℝ) ^ 6 * ((m : ℝ) ^ k * (t : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left hPle (by positivity)
    have h2 : (t : ℝ) ^ (6 + k) ≤ (t : ℝ) ^ m := by
      apply pow_le_pow_right₀ ht1
      omega
    have h3 : (t : ℝ) ^ 6 * ((m : ℝ) ^ k * (t : ℝ) ^ k) = (m : ℝ) ^ k * (t : ℝ) ^ (6 + k) := by
      rw [pow_add]
      ring
    have h4 : (m : ℝ) ^ k * (t : ℝ) ^ (6 + k) ≤ (m : ℝ) ^ k * N :=
      mul_le_mul_of_nonneg_left (h2.trans hloR) (by positivity)
    linarith
  have hz : (t : ℝ) ^ 2 + 1 ≤ 2 * (t : ℝ) ^ 6 := by
    have h4 : (1 : ℝ) ≤ (t : ℝ) ^ 4 := one_le_pow₀ ht1
    have h26 : (t : ℝ) ^ 2 ≤ (t : ℝ) ^ 6 := pow_le_pow_right₀ ht1 (by norm_num)
    have h16 : (1 : ℝ) ≤ (t : ℝ) ^ 6 := one_le_pow₀ ht1
    linarith
  have hfin : (pattern_count L N : ℝ) ≤ 3 * ((m : ℝ) ^ k * N / P) +
      (m : ℝ) ^ k / c * bad_factor L * N / P := by
    linarith
  have hQ0 : 0 ≤ (m : ℝ) ^ k * N / P := div_nonneg (by positivity) hPpos.le
  have hbadN : (m : ℝ) ^ k * N / P ≤ bad_factor L * ((m : ℝ) ^ k * N / P) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbad) hQ0]
  calc (pattern_count L N : ℝ)
      ≤ 3 * ((m : ℝ) ^ k * N / P) + (m : ℝ) ^ k / c * bad_factor L * N / P := hfin
    _ ≤ 3 * (bad_factor L * ((m : ℝ) ^ k * N / P)) + (m : ℝ) ^ k / c * bad_factor L * N / P := by
        linarith
    _ = (3 * (m : ℝ) ^ k + (m : ℝ) ^ k / c) * bad_factor L * N / P := by ring

end RNS.PatternUpperBound

#print axioms RNS.PatternUpperBound.pattern_multiples_count_holds
#print axioms RNS.PatternUpperBound.pattern_selberg_sum_lower_step
#print axioms RNS.PatternUpperBound.pattern_sieve_bound_step
#print axioms RNS.PatternUpperBound.pattern_count_le_step
