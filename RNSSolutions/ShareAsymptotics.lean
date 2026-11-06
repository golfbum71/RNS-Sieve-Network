/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.ShareAsymptotics.Conclusions
import RNSNetwork.Nodes.SurvivorCount.Conclusions
import RNSNetwork.Nodes.TwinShare.Conclusions
import RNSNetwork.Nodes.SingularSeries.Conclusions
import Mathlib.Topology.Algebra.InfiniteSum.Basic       -- `Function.Injective.tprod_eq`
import Mathlib.Analysis.SpecialFunctions.Log.Summable  -- `Real.multipliable_one_add_of_summable`
import Mathlib.Analysis.PSeries                        -- `summable_one_div_nat_pow`
import Mathlib.Topology.Algebra.InfiniteSum.NatInt     -- `HasProd.tendsto_prod_nat`
import Mathlib.Order.Filter.AtTopBot.Archimedean       -- `tendsto_natCast_atTop_atTop`
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Proofs for ShareAsymptotics

Built clean by `lake build RNSSolutions` on 2026-11-06; `#print axioms` shows only
the standard three. (`pattern_share_asymptotic_step` added afterwards; see its
metadata for its build status.)

Imports claims only. Both claims are steps: from `SurvivorCount`'s
`general_survivor_count`, `TwinShare`'s two twin-share claims, and
`MertensThird.mertens_third`, taken as named hypotheses.

Idea. The survivor share of the cycle is the product over the wheels of one
minus one over the wheel (`SurvivorCount`), which is Mertens' share at `n`,
so the first claim is Mertens' third theorem along the whole numbers. For the
twin share: twin share = (twins over plain survivors) times (plain share);
`TwinShare` writes the first factor as the partial odd twin product times the
odd wheels' share, and the odd wheels' share is twice the plain share. So the
twin share is twice the partial odd twin product times the plain share
squared; the partial products converge (the factors differ from 1 by at most
four over the prime squared), and Mertens gives the rest.
-/

namespace RNS.ShareAsymptotics

open Filter Topology RNS.SurvivorCount RNS.TwinShare RNS.MertensThird RNS.SingularSeries

private theorem mem_active {limit q : Nat} (hq : q ∈ active_primes limit) :
    q.Prime ∧ q < limit := by
  have h := Finset.mem_filter.mp hq
  exact ⟨h.2, Finset.mem_range.mp h.1⟩

/-- The plain share is the product over the wheels of the wheel size minus 1
over the wheel size (as in `ShareBounds`). -/
private theorem share_eq_prod (hgen : general_survivor_count) (limit : Nat) :
    ((wheel_survivors_gen {0} limit).card : Real) / (primorial_modulus limit : Real)
      = ∏ q ∈ active_primes limit, (((q : Real) - 1) / q) := by
  have hw : ∀ q, w ({0} : Finset Nat) q = 1 := by intro q; simp [w]
  rw [hgen {0} limit, primorial_modulus]
  simp only [hw]
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  rw [Nat.cast_sub (mem_active hq).1.one_le]
  simp

/-- That product, for the wheels up to `n`, is Mertens' survivor share at `n`. -/
private theorem prod_eq_survivor_share (n : ℕ) :
    ∏ q ∈ active_primes (n + 1), (((q : Real) - 1) / q) = survivor_share (n : ℝ) := by
  unfold survivor_share
  rw [Nat.floor_natCast]
  refine Finset.prod_congr rfl fun q hq => ?_
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (mem_active hq).1.ne_zero
  rw [sub_div, div_self hq0]

theorem survivor_share_asymptotic_step (hgen : general_survivor_count)
    (hm : mertens_third) : survivor_share_asymptotic := by
  unfold survivor_share_asymptotic
  unfold mertens_third at hm
  have h := hm.comp tendsto_natCast_atTop_atTop
  refine Filter.Tendsto.congr (fun n => ?_) h
  show survivor_share (n : ℝ) * Real.log (n : ℝ) =
    ((wheel_survivors_gen {0} (n + 1)).card : ℝ) / (primorial_modulus (n + 1) : ℝ) *
      Real.log (n : ℝ)
  rw [share_eq_prod hgen (n + 1), prod_eq_survivor_share n]

/-- The odd twin factors multiply to a finite product. -/
private theorem twin_multipliable : Multipliable odd_twin_factor := by
  have hf : Summable (fun n : ℕ => if n.Prime ∧ n ≠ 2 then -(1 / ((n : ℝ) - 1) ^ 2) else 0) := by
    refine Summable.of_norm_bounded
      ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left 4) (fun n => ?_)
    split_ifs with h
    · have h3 : (3 : ℝ) ≤ n := by
        have h2 := h.1.two_le
        have hne := h.2
        exact_mod_cast (show 3 ≤ n by omega)
      have hpos : (0 : ℝ) < ((n : ℝ) - 1) ^ 2 := by nlinarith
      rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity), mul_one_div,
        div_le_div_iff₀ hpos (by positivity)]
      nlinarith
    · simp only [norm_zero]
      positivity
  have hm := Real.multipliable_one_add_of_summable hf
  convert hm using 1
  funext n
  unfold odd_twin_factor
  split_ifs <;> ring

/-- The partial odd twin product up to `n`, as a product over the odd wheels. -/
private theorem partial_eq (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), odd_twin_factor i =
      ∏ q ∈ (active_primes (n + 1)).erase 2, (1 - 1 / ((q : Real) - 1) ^ 2) := by
  unfold odd_twin_factor
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ (fun _ _ => rfl)
  ext q
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, active_primes]
  tauto

theorem twin_share_asymptotic_step (hgen : general_survivor_count)
    (heq : twin_share_eq_prod) (hsplit : twin_share_split) (hm : mertens_third) :
    twin_share_asymptotic := by
  unfold twin_share_asymptotic
  unfold mertens_third at hm
  have ht := (twin_multipliable.hasProd.tendsto_prod_nat).comp (tendsto_add_atTop_nat 1)
  have hs := hm.comp tendsto_natCast_atTop_atTop
  have hc := (ht.const_mul 2).mul (hs.pow 2)
  refine hc.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  show 2 * (∏ i ∈ Finset.range (n + 1), odd_twin_factor i) *
      (survivor_share (n : ℝ) * Real.log (n : ℝ)) ^ 2 =
    ((wheel_survivors (n + 1)).card : ℝ) / (primorial_modulus (n + 1) : ℝ) *
      Real.log (n : ℝ) ^ 2
  have hw : ∀ q, w ({0} : Finset Nat) q = 1 := by intro q; simp [w]
  have hplain : ((wheel_survivors_gen {0} (n + 1)).card : ℝ) ≠ 0 := by
    rw [hgen {0} (n + 1)]
    simp only [hw]
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun q hq => by
      have := (mem_active hq).1.two_le
      omega)
  have hcycle : (primorial_modulus (n + 1) : ℝ) ≠ 0 := by
    unfold primorial_modulus
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun q hq => (mem_active hq).1.ne_zero)
  have hT : ((wheel_survivors (n + 1)).card : ℝ) / (primorial_modulus (n + 1) : ℝ) =
      ((wheel_survivors (n + 1)).card : ℝ) / ((wheel_survivors_gen {0} (n + 1)).card : ℝ) *
        (((wheel_survivors_gen {0} (n + 1)).card : ℝ) / (primorial_modulus (n + 1) : ℝ)) := by
    field_simp
  have h2mem : 2 ∈ active_primes (n + 1) := by
    unfold active_primes
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have hO : ∏ q ∈ (active_primes (n + 1)).erase 2, (((q : Real) - 1) / (q : Real)) =
      2 * survivor_share (n : ℝ) := by
    rw [← prod_eq_survivor_share n,
      ← Finset.mul_prod_erase (active_primes (n + 1)) (fun q : ℕ => ((q : Real) - 1) / q) h2mem]
    first | (norm_num; ring) | norm_num
  rw [hT, heq (n + 1), hsplit (n + 1), hO, share_eq_prod hgen (n + 1),
    prod_eq_survivor_share n, partial_eq n]
  ring

/-- **Twice the odd twin product is the classical twin-prime constant.** The
odd primes are exactly where the factor differs from 1, so the product over
the whole numbers equals the product over the odd primes. -/
theorem odd_twin_product_eq_classical_holds : odd_twin_product_eq_classical := by
  unfold odd_twin_product_eq_classical odd_twin_product RNS.TwinConstant.twin_prime_classical_constant
  congr 1
  let g : {q : Nat.Primes // (q : ℕ) ≠ 2} → ℕ := fun p => ((p : Nat.Primes) : ℕ)
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hsupp : Function.mulSupport odd_twin_factor ⊆ Set.range g := by
    intro n hn
    rw [Function.mem_mulSupport] at hn
    unfold odd_twin_factor at hn
    split_ifs at hn with h
    · exact ⟨⟨⟨n, h.1⟩, h.2⟩, rfl⟩
    · exact absurd rfl hn
  rw [← hg.tprod_eq hsupp]
  refine tprod_congr fun p => ?_
  show odd_twin_factor ((p : Nat.Primes) : ℕ) = _
  unfold odd_twin_factor
  rw [if_pos ⟨(p : Nat.Primes).prop, p.prop⟩]

theorem twin_share_asymptotic_classical_step (hgen : general_survivor_count)
    (heq : twin_share_eq_prod) (hsplit : twin_share_split) (hm : mertens_third) :
    twin_share_asymptotic_classical := by
  have h := twin_share_asymptotic_step hgen heq hsplit hm
  unfold twin_share_asymptotic at h
  unfold twin_share_asymptotic_classical
  rw [← odd_twin_product_eq_classical_holds]
  exact h

/-- A pattern's correction factor at the primes, extended by 1 to all whole
numbers. -/
private noncomputable def ext_factor (T : Finset ℕ) (m : ℕ) : ℝ :=
  if m.Prime then singular_series_factor T m else 1

/-- The plain wheel product up to `n` is Mertens' survivor share at `n`. -/
private theorem prod_one_sub_eq (n : ℕ) :
    ∏ q ∈ active_primes (n + 1), (1 - 1 / (q : ℝ)) = survivor_share (n : ℝ) := by
  unfold survivor_share
  rw [Nat.floor_natCast]

theorem pattern_share_asymptotic_step (hld : local_density_factorization)
    (hmul : factor_multipliable) (hm : mertens_third) : pattern_share_asymptotic := by
  intro T hT hk
  unfold mertens_third at hm
  have hg : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  have hf1 : ∀ x ∉ Set.range (fun p : Nat.Primes => (p : ℕ)), ext_factor T x = 1 := by
    intro x hx
    unfold ext_factor
    rw [if_neg]
    intro hp
    exact hx ⟨⟨x, hp⟩, rfl⟩
  have hcomp : (ext_factor T ∘ fun p : Nat.Primes => (p : ℕ)) =
      fun p : Nat.Primes => singular_series_factor T p := by
    funext p
    show (if (p : ℕ).Prime then singular_series_factor T p else 1) = _
    rw [if_pos p.prop]
  have hmulT : Multipliable (ext_factor T) := by
    refine (hg.multipliable_iff hf1).mp ?_
    rw [hcomp]
    exact hmul T hk
  have hval : ∏' m, ext_factor T m = hardy_littlewood_constant T := by
    unfold hardy_littlewood_constant
    rw [← hg.tprod_eq (f := ext_factor T)
      (fun x hx => by_contra fun hn => hx (hf1 x hn))]
    refine tprod_congr fun p => ?_
    show (if (p : ℕ).Prime then singular_series_factor T p else 1) = _
    rw [if_pos p.prop]
  have hpart : ∀ n : ℕ, ∏ i ∈ Finset.range (n + 1), ext_factor T i =
      ∏ q ∈ active_primes (n + 1), singular_series_factor T q := by
    intro n
    unfold ext_factor
    rw [← Finset.prod_filter]
    first | rfl | simp [active_primes]
  have ht := (hmulT.hasProd.tendsto_prod_nat).comp (tendsto_add_atTop_nat 1)
  rw [hval] at ht
  have hs := (hm.comp tendsto_natCast_atTop_atTop).pow T.card
  have hc := ht.mul hs
  refine Filter.Tendsto.congr (fun n => ?_) hc
  show (∏ i ∈ Finset.range (n + 1), ext_factor T i) *
      (survivor_share (n : ℝ) * Real.log (n : ℝ)) ^ T.card =
    ((wheel_survivors_gen T (n + 1)).card : ℝ) / (primorial_modulus (n + 1) : ℝ) *
      Real.log (n : ℝ) ^ T.card
  rw [hld T (n + 1) hT hk, Finset.prod_pow, prod_one_sub_eq n, hpart n]
  ring

end RNS.ShareAsymptotics

#print axioms RNS.ShareAsymptotics.survivor_share_asymptotic_step
#print axioms RNS.ShareAsymptotics.twin_share_asymptotic_step
#print axioms RNS.ShareAsymptotics.odd_twin_product_eq_classical_holds
#print axioms RNS.ShareAsymptotics.twin_share_asymptotic_classical_step
#print axioms RNS.ShareAsymptotics.pattern_share_asymptotic_step
