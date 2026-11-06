/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.MenonIdentity.Conclusions
import Mathlib.Tactic.Positivity                        -- `Finset.prod_pos`
import Mathlib.Data.Nat.Totient                         -- `Nat.sum_totient`, `Nat.totient_mul`
import Mathlib.NumberTheory.ArithmeticFunction.Misc     -- `Nat.Coprime.card_divisors_mul`
import Mathlib.Algebra.BigOperators.Associated          -- `Prime.exists_mem_finset_dvd`
import Mathlib.Data.Nat.GCD.BigOperators                -- `Nat.coprime_prod_right_iff`
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma  -- `Finset.sum_comm`

/-!
# Proofs for MenonIdentity

Imports claims only, never other nodes' proofs. Rests on no other node.

Built clean by `lake build RNSSolutions` on 2026-11-05; `#print axioms` shows only
the standard three.

Idea. Write the cycle length as `N`. The gcd of (survivor minus one) with `N`
is the sum of the totients of its divisors, which are the divisors `d` of `N`
dividing (survivor minus one). Swapping the two sums, each divisor `d` of `N`
contributes its totient times the number of survivors leaving remainder 1 on
division by `d`. Write `N = d * e`; the wheels make `N` squarefree, so `d` and
`e` share no factor. The numbers from 1 to `N` leaving remainder 1 on division
by `d` are `1 + d * t` for `t` below `e`, and as `t` runs below `e` the
remainders of `1 + d * t` on division by `e` run through every remainder
once, since `d` is invertible modulo `e`. So exactly `φ e` of them survive,
and each divisor contributes `φ d * φ e = φ N`. With `d = 1` this also says
the survivors number `φ N`, and `N` has two to the number of wheels divisors.
-/

namespace RNS.MenonIdentity

/-! ## Counting the numbers that leave remainder 1 -/

/-- The numbers `1 + d * t` with `t` below `e` are exactly the numbers from 1 to
`d * e` leaving remainder 1 on division by `d`; among them, the survivors of
`d * e` are those whose `t` makes `1 + d * t` share no factor with `e`. -/
private theorem filter_eq_image (d e : Nat) (hd : 0 < d) :
    (Finset.Icc 1 (d * e)).filter (fun k => Nat.Coprime k (d * e) ∧ d ∣ k - 1) =
      ((Finset.range e).filter (fun t => Nat.Coprime (1 + d * t) e)).image
        (fun t => 1 + d * t) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hk1, hkN⟩, hcop, hdk⟩
    obtain ⟨t, ht⟩ := hdk
    have hk : k = 1 + d * t := by omega
    refine ⟨t, ⟨?_, ?_⟩, hk.symm⟩
    · by_contra hte
      have hle := Nat.mul_le_mul_left d (not_lt.mp hte)
      omega
    · rw [← hk]
      exact Nat.Coprime.coprime_dvd_right (dvd_mul_left e d) hcop
  · rintro ⟨t, ⟨hte, hcop⟩, rfl⟩
    refine ⟨⟨by omega, ?_⟩, ?_, ⟨t, by omega⟩⟩
    · have h := Nat.mul_le_mul_left d (show t + 1 ≤ e by omega)
      rw [Nat.mul_add, Nat.mul_one] at h
      omega
    · apply Nat.Coprime.mul_right
      · exact (Nat.coprime_add_mul_left_left 1 d t).mpr (Nat.coprime_one_left d)
      · exact hcop

/-- As `t` runs below `e`, the remainders of `1 + d * t` on division by `e`
sharing no factor with `e` number `φ e`. -/
private theorem card_shift_coprime (d e : Nat) (he : 0 < e) (hde : Nat.Coprime d e) :
    ((Finset.range e).filter (fun t => Nat.Coprime (1 + d * t) e)).card = Nat.totient e := by
  have hinj : Set.InjOn (fun t => (1 + d * t) % e) (Finset.range e : Set Nat) := by
    intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h' : (1 + d * a) % e = (1 + d * b) % e := h
    have h1 : 1 + a * d ≡ 1 + b * d [MOD e] := by
      unfold Nat.ModEq
      rw [Nat.mul_comm a d, Nat.mul_comm b d]
      exact h'
    have h2 := Nat.ModEq.cancel_right_of_coprime (Nat.coprime_iff_gcd_eq_one.mp hde.symm)
      (Nat.ModEq.add_left_cancel' 1 h1)
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  have himg : (Finset.range e).image (fun t => (1 + d * t) % e) = Finset.range e := by
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      simp only [Finset.mem_image, Finset.mem_range] at hs ⊢
      obtain ⟨t, _, rfl⟩ := hs
      exact Nat.mod_lt _ he
    · exact (Finset.card_image_of_injOn hinj).ge
  have hT : ((Finset.range e).filter (fun t => Nat.Coprime (1 + d * t) e)).image
      (fun t => (1 + d * t) % e) = (Finset.range e).filter (fun s => e.Coprime s) := by
    ext s
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨t, ⟨_, hc⟩, rfl⟩
      refine ⟨Nat.mod_lt _ he, ?_⟩
      show Nat.gcd e ((1 + d * t) % e) = 1
      rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
      exact hc
    · rintro ⟨hs, hc⟩
      have hs' : s ∈ (Finset.range e).image (fun t => (1 + d * t) % e) := by
        rw [himg]
        exact Finset.mem_range.mpr hs
      simp only [Finset.mem_image, Finset.mem_range] at hs'
      obtain ⟨t, ht, hts⟩ := hs'
      refine ⟨t, ⟨ht, ?_⟩, hts⟩
      show Nat.gcd (1 + d * t) e = 1
      rw [Nat.gcd_comm, Nat.gcd_rec, hts, Nat.gcd_comm]
      exact hc
  have hsub : (((Finset.range e).filter (fun t => Nat.Coprime (1 + d * t) e) : Finset Nat) :
      Set Nat) ⊆ (Finset.range e : Set Nat) :=
    Finset.coe_subset.mpr (fun x hx => (Finset.mem_filter.mp hx).1)
  calc ((Finset.range e).filter (fun t => Nat.Coprime (1 + d * t) e)).card
      = (((Finset.range e).filter (fun t => Nat.Coprime (1 + d * t) e)).image
          (fun t => (1 + d * t) % e)).card :=
        (Finset.card_image_of_injOn (Set.InjOn.mono hsub hinj)).symm
    _ = ((Finset.range e).filter (fun s => e.Coprime s)).card := by rw [hT]
    _ = Nat.totient e := (Nat.totient_eq_card_coprime e).symm

/-- For `d` and `e` sharing no factor, the numbers from 1 to `d * e` sharing no
factor with `d * e` and leaving remainder 1 on division by `d` number `φ e`. -/
private theorem count_one_mod (d e : Nat) (hd : 0 < d) (he : 0 < e) (hde : Nat.Coprime d e) :
    ((Finset.Icc 1 (d * e)).filter (fun k => Nat.Coprime k (d * e) ∧ d ∣ k - 1)).card
      = Nat.totient e := by
  have hinj : Function.Injective (fun t : Nat => 1 + d * t) := by
    intro a b h
    have h' : 1 + d * a = 1 + d * b := h
    exact Nat.mul_left_cancel hd (by omega)
  rw [filter_eq_image d e hd, Finset.card_image_of_injective _ hinj,
    card_shift_coprime d e he hde]

/-! ## The wheels make the cycle squarefree -/

/-- The survivors of the wheels in one cycle are the numbers from 1 to the
cycle length sharing no factor with it. -/
private theorem survivors_eq (W : Finset Nat) (hW : ∀ q ∈ W, q.Prime) :
    survivors_upto W (W.prod id) =
      (Finset.Icc 1 (W.prod id)).filter (fun k => Nat.Coprime k (W.prod id)) := by
  unfold survivors_upto
  apply Finset.filter_congr
  intro k _
  rw [Nat.coprime_prod_right_iff]
  apply forall₂_congr
  intro q hq
  rw [Nat.coprime_comm]
  exact ((hW q hq).coprime_iff_not_dvd).symm

/-- No prime's square divides the cycle length. -/
private theorem sq_not_dvd (W : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (q : Nat) (hq : q.Prime) :
    ¬ q * q ∣ W.prod id := by
  intro h
  have hqN : q ∣ W.prod id := (dvd_mul_right q q).trans h
  obtain ⟨p, hp, hqp⟩ := hq.prime.exists_mem_finset_dvd hqN
  have hpq : q = p := (Nat.prime_dvd_prime_iff_eq hq (hW p hp)).mp hqp
  subst hpq
  rw [← Finset.mul_prod_erase W id hp] at h
  change q * q ∣ q * (W.erase q).prod id at h
  have h2 : q ∣ (W.erase q).prod id := Nat.dvd_of_mul_dvd_mul_left hq.pos h
  obtain ⟨r, hr, hqr⟩ := hq.prime.exists_mem_finset_dvd h2
  have hqr' : q = r := (Nat.prime_dvd_prime_iff_eq hq (hW r (Finset.mem_of_mem_erase hr))).mp hqr
  subst hqr'
  exact Finset.notMem_erase q W hr

/-- A divisor of the cycle length shares no factor with its cofactor. -/
private theorem coprime_div (W : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (d : Nat)
    (hd : d ∣ W.prod id) : Nat.Coprime d (W.prod id / d) := by
  apply Nat.coprime_of_dvd
  intro q hq hqd hqe
  apply sq_not_dvd W hW q hq
  have h := mul_dvd_mul hqd hqe
  rwa [Nat.mul_div_cancel' hd] at h

/-- The cycle length has two to the number of wheels divisors. -/
private theorem card_divisors_prod (W : Finset Nat) (hW : ∀ q ∈ W, q.Prime) :
    (W.prod id).divisors.card = 2 ^ W.card := by
  induction W using Finset.induction_on with
  | empty => simp
  | insert p W hpW ih =>
    have hp : p.Prime := hW p (Finset.mem_insert_self p W)
    have hW' : ∀ q ∈ W, q.Prime := fun q hq => hW q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (W.prod id) := by
      rw [Nat.coprime_prod_right_iff]
      intro q hq
      exact (Nat.coprime_primes hp (hW' q hq)).mpr (fun h => hpW (by rw [h]; exact hq))
    rw [Finset.prod_insert hpW, Finset.card_insert_of_notMem hpW, pow_succ]
    change (p * W.prod id).divisors.card = 2 ^ W.card * 2
    rw [Nat.Coprime.card_divisors_mul hcop, Nat.Prime.divisors hp, ih hW',
      Finset.card_pair_eq_two_iff.mpr (Nat.ne_of_lt hp.one_lt), Nat.mul_comm]

/-- The divisors of `gcd a N` are the divisors of `N` that divide `a`. -/
private theorem divisors_gcd (a N : Nat) (hN : N ≠ 0) :
    (Nat.gcd a N).divisors = N.divisors.filter (fun d => d ∣ a) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩
    exact ⟨⟨h2, hN⟩, h1⟩
  · rintro ⟨⟨h2, _⟩, h1⟩
    exact ⟨⟨h1, h2⟩, fun h0 => hN (Nat.eq_zero_of_gcd_eq_zero_right h0)⟩

/-! ## Menon's identity -/

theorem menon_wheel_sum_holds : menon_wheel_sum := by
  intro W hW
  have hNpos : 0 < W.prod id := Finset.prod_pos fun q hq => (hW q hq).pos
  have hN0 : W.prod id ≠ 0 := hNpos.ne'
  rw [survivors_eq W hW]
  -- each divisor `d` of the cycle contributes `φ d` times the survivors leaving remainder 1
  have step2 : ∀ d ∈ (W.prod id).divisors,
      (∑ k ∈ (Finset.Icc 1 (W.prod id)).filter (fun k => Nat.Coprime k (W.prod id)),
        if d ∣ k - 1 then Nat.totient d else 0) = Nat.totient (W.prod id) := by
    intro d hd
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Finset.filter_filter]
    have hdN : d ∣ W.prod id := Nat.dvd_of_mem_divisors hd
    have hcop := coprime_div W hW d hdN
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hepos : 0 < W.prod id / d := Nat.div_pos (Nat.le_of_dvd hNpos hdN) hdpos
    have hNe : W.prod id = d * (W.prod id / d) := (Nat.mul_div_cancel' hdN).symm
    generalize W.prod id / d = e at hcop hepos hNe
    rw [hNe, count_one_mod d e hdpos hepos hcop, Nat.totient_mul hcop, Nat.mul_comm]
  -- with `d = 1`: the survivors number `φ` of the cycle
  have hS : ((Finset.Icc 1 (W.prod id)).filter (fun k => Nat.Coprime k (W.prod id))).card
      = Nat.totient (W.prod id) := by
    have h1 := step2 1 (Nat.one_mem_divisors.mpr hN0)
    simp only [Nat.one_dvd, ↓reduceIte, Nat.totient_one, Finset.sum_const, smul_eq_mul,
      Nat.mul_one] at h1
    exact h1
  calc (∑ k ∈ (Finset.Icc 1 (W.prod id)).filter (fun k => Nat.Coprime k (W.prod id)),
        Nat.gcd (k - 1) (W.prod id))
      = ∑ k ∈ (Finset.Icc 1 (W.prod id)).filter (fun k => Nat.Coprime k (W.prod id)),
          ∑ d ∈ (W.prod id).divisors, if d ∣ k - 1 then Nat.totient d else 0 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_filter, ← divisors_gcd (k - 1) (W.prod id) hN0, Nat.sum_totient]
    _ = ∑ d ∈ (W.prod id).divisors,
          ∑ k ∈ (Finset.Icc 1 (W.prod id)).filter (fun k => Nat.Coprime k (W.prod id)),
            if d ∣ k - 1 then Nat.totient d else 0 := Finset.sum_comm
    _ = ∑ d ∈ (W.prod id).divisors, Nat.totient (W.prod id) := Finset.sum_congr rfl step2
    _ = (W.prod id).divisors.card * Nat.totient (W.prod id) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = ((Finset.Icc 1 (W.prod id)).filter (fun k => Nat.Coprime k (W.prod id))).card
          * 2 ^ W.card := by
        rw [card_divisors_prod W hW, hS, Nat.mul_comm]

end RNS.MenonIdentity

#print axioms RNS.MenonIdentity.menon_wheel_sum_holds
