/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Data.Nat.Choose.Sum -- `Finset.sum_powerset_neg_one_pow_card_of_nonempty`
import Mathlib.Algebra.Ring.Parity -- `Nat.even_iff`, `Nat.odd_iff`, `Odd.neg_one_pow`
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify
import RNSNetwork.Nodes.Sawtooth.Conclusions
import RNSNetwork.Nodes.LehmerExcess.Conclusions

/-!
# Proofs for LehmerExcess

Imports claims only, never other nodes' proofs. `lehmer_excess_closed_form`
is proved as a step from `Sawtooth`'s `sawtooth_identity`, taken as a named
hypothesis; `RNSSolutions/Assemble.lean` plugs in the finished proof.

The route: each wheel is one short of `k`, so a product of wheels leaves
remainder 1 on division by `k` when there is an even number of them and
`k - 1` when odd. So each remainder in the sawtooth identity is `a` or
`k - a`; twice it is `k` plus or minus `2 a - k`. The `k` parts cancel over
all choices of wheels, and the signs on `2 a - k` all agree, leaving two to
the number of wheels copies.
-/

namespace RNS.LehmerExcess

open RNS.Sawtooth

/-- `a` times `k - 1` leaves remainder `k - a` on division by `k`. -/
private theorem mul_pred_mod (a k : Nat) (ha : 0 < a) (hak : a < k) :
    a * (k - 1) % k = k - a := by
  have e : a * (k - 1) = (k - a) + k * (a - 1) := by
    zify [show 1 ≤ k by omega, show a ≤ k by omega, show 1 ≤ a by omega]
    ring
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- A product of wheels each one short of `k` leaves remainder 1 on division
by `k` for an even number of wheels, and `k - 1` for an odd number. -/
private theorem prod_mod (k : Nat) (hk : 2 ≤ k) (T : Finset Nat)
    (hT : ∀ q ∈ T, q % k = k - 1) :
    T.prod id % k = if T.card % 2 = 0 then 1 else k - 1 := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.card_empty, if_pos rfl]
    exact Nat.mod_eq_of_lt (by omega)
  | insert q T hq ih =>
    rw [Finset.prod_insert hq, Finset.card_insert_of_notMem hq]
    have hq' := hT q (Finset.mem_insert_self q T)
    have ih' := ih (fun x hx => hT x (Finset.mem_insert_of_mem hx))
    have e1 : id q * T.prod id = q * T.prod id := rfl
    rw [e1, Nat.mul_mod, hq', ih']
    rcases Nat.mod_two_eq_zero_or_one T.card with h | h
    · rw [if_pos h, if_neg (by omega), Nat.mul_one, Nat.mod_eq_of_lt (by omega)]
    · have e2 : (k - 1) * (k - 1) = 1 + k * (k - 2) := by
        zify [show 1 ≤ k by omega, show 2 ≤ k by omega]
        ring
      rw [if_neg (by omega), if_pos (by omega), e2, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]

/-- **The closed form for wheels one short**, as a step from the sawtooth
identity. -/
theorem lehmer_excess_closed_form_step (hS : sawtooth_identity) :
    lehmer_excess_closed_form := by
  intro W k a hW hWk hne ha hak
  have hk : 2 ≤ k := by omega
  have h := hS W k a hW
  have hterm : ∀ S ∈ W.powerset, ((a * (W \ S).prod id % k : Nat) : Int) * 2
      = k + (-1 : Int) ^ (W.card - S.card) * (2 * a - k) := by
    intro S hS'
    have hsub := Finset.mem_powerset.mp hS'
    have hcard : (W \ S).card = W.card - S.card := Finset.card_sdiff_of_subset hsub
    have hm := prod_mod k hk (W \ S) (fun q hq => hWk q (Finset.sdiff_subset hq))
    rw [Nat.mul_mod, hm, ← hcard]
    rcases Nat.mod_two_eq_zero_or_one (W \ S).card with hc | hc
    · rw [if_pos hc, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hak,
        Even.neg_one_pow (Nat.even_iff.mpr hc)]
      ring
    · rw [if_neg (by omega), Nat.mod_eq_of_lt hak, mul_pred_mod a k ha hak,
        Odd.neg_one_pow (Nat.odd_iff.mpr hc), Nat.cast_sub (by omega : a ≤ k)]
      ring
  have hsum : (∑ S ∈ W.powerset, (-1 : Int) ^ S.card * ((a * (W \ S).prod id % k : Nat) : Int)) * 2
      = (-1 : Int) ^ W.card * 2 ^ W.card * (2 * a - k) := by
    rw [Finset.sum_mul]
    have e : ∀ S ∈ W.powerset, (-1 : Int) ^ S.card * ((a * (W \ S).prod id % k : Nat) : Int) * 2
        = k * (-1 : Int) ^ S.card + (-1 : Int) ^ W.card * (2 * a - k) := by
      intro S hS'
      have hle : S.card ≤ W.card := Finset.card_le_card (Finset.mem_powerset.mp hS')
      rw [mul_assoc, hterm S hS']
      have hpow : (-1 : Int) ^ S.card * (-1) ^ (W.card - S.card) = (-1) ^ W.card := by
        rw [← pow_add, Nat.add_sub_cancel' hle]
      linear_combination (2 * (a : Int) - k) * hpow
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_powerset_neg_one_pow_card_of_nonempty hne, Finset.sum_const,
      Finset.card_powerset, nsmul_eq_mul]
    push_cast
    ring
  linear_combination 2 * h - hsum

end RNS.LehmerExcess
