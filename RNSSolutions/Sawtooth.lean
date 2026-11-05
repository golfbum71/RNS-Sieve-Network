/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Algebra.BigOperators.Associated -- `Finset.prod_primes_dvd`
import Mathlib.Algebra.BigOperators.Ring.Finset -- `Finset.prod_add`, `Finset.prod_neg`
import Mathlib.Data.Nat.Factorization.Basic     -- `Nat.Ioc_filter_dvd_card_eq_div`
import Mathlib.Data.Nat.Prime.Basic             -- `Nat.Prime.prime`
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import RNSNetwork.Nodes.Sawtooth.Conclusions

/-!
# Proofs for Sawtooth

Imports claims only, never other nodes' proofs. Proves all three of the
node's claims directly; none rests on another node.

The route: a number survives the wheels exactly when, for every wheel, it is
not a multiple of that wheel. Written as a product over the wheels of
"one minus (is a multiple)", and multiplied out, this becomes a signed sum
over choices of wheels of "is a multiple of every chosen wheel", which for
distinct primes is "is a multiple of their product". Adding up over the
numbers from 1 to the bound and swapping the two sums gives Legendre's count,
because the multiples of a number up to the bound number the bound divided by
it. At a fraction of the cycle, each rounded-down quotient is a whole part,
and whole part = (value minus remainder) / denominator turns the count into
the proportional share minus the signed sum of remainders.
-/

namespace RNS.Sawtooth

/-- For distinct primes, being a multiple of every one of them is the same as
being a multiple of their product. -/
private theorem prod_dvd_iff {S : Finset Nat} (hS : ∀ q ∈ S, q.Prime) (n : Nat) :
    S.prod id ∣ n ↔ ∀ q ∈ S, q ∣ n := by
  constructor
  · intro h q hq
    exact (Finset.dvd_prod_of_mem id hq).trans h
  · intro h
    exact Finset.prod_primes_dvd n (fun a ha => (hS a ha).prime) h

/-- Surviving every wheel, as a number (1 or 0), multiplied out over the
choices of wheels. -/
private theorem survives_expand (W : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (n : Nat) :
    (if ∀ q ∈ W, ¬ q ∣ n then (1 : Int) else 0)
      = ∑ S ∈ W.powerset, (-1 : Int) ^ S.card * (if S.prod id ∣ n then 1 else 0) := by
  rw [← Finset.prod_boole (s := W) (p := fun q => ¬ q ∣ n) (M₀ := Int)]
  have h1 : ∀ q ∈ W, (if ¬ q ∣ n then (1 : Int) else 0) = -(if q ∣ n then 1 else 0) + 1 := by
    intro q _
    split_ifs <;> simp_all
  rw [Finset.prod_congr rfl h1, Finset.prod_add]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have hS' : ∀ q ∈ S, q.Prime := fun q hq => hW q (Finset.mem_powerset.mp hS hq)
  rw [Finset.prod_const_one, mul_one, Finset.prod_neg, Finset.prod_boole]
  congr 1
  simp only [prod_dvd_iff hS' n]

/-- The multiples of a number from 1 to a bound number the bound divided by
it, rounded down. -/
private theorem multiples_card (x d : Nat) :
    ((Finset.Icc 1 x).filter (fun k => d ∣ k)).card = x / d := by
  have h : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [h]
  exact Nat.Ioc_filter_dvd_card_eq_div x d

/-- Dividing the cycle by the product of some of its wheels leaves the product
of the others. -/
private theorem complement_prod (W S : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (hS : S ⊆ W) :
    W.prod id / S.prod id = (W \ S).prod id := by
  have hpos : 0 < S.prod id :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun q hq => (hW q (hS hq)).ne_zero)
  rw [← Finset.prod_sdiff hS]
  exact Nat.mul_div_cancel _ hpos

/-- Rounding down twice: `a` `k`-ths of the cycle, rounded down, then divided
by the product of some wheels and rounded down, is `a` times the product of
the other wheels, divided by `k` and rounded down. -/
private theorem floor_step (W S : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (hS : S ⊆ W)
    (k a : Nat) :
    a * W.prod id / k / S.prod id = a * (W \ S).prod id / k := by
  have hpos : 0 < S.prod id :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun q hq => (hW q (hS hq)).ne_zero)
  rw [Nat.div_div_eq_div_mul, ← Finset.prod_sdiff hS, ← mul_assoc]
  exact Nat.mul_div_mul_right _ _ hpos

/-- **Legendre's count**, proved. -/
theorem legendre_count_holds : legendre_count := by
  intro W x hW
  unfold survivors_upto
  rw [Finset.card_filter]
  push_cast
  simp_rw [survives_expand W hW]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← Finset.mul_sum, ← multiples_card x (S.prod id), Finset.card_filter]
  push_cast
  rfl

/-- **The sawtooth identity**, proved. -/
theorem sawtooth_identity_holds : sawtooth_identity := by
  intro W k a hW
  rw [legendre_count_holds W _ hW, legendre_count_holds W _ hW, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have hSW := Finset.mem_powerset.mp hS
  rw [floor_step W S hW hSW, complement_prod W S hW hSW]
  have h := Nat.div_add_mod (a * (W \ S).prod id) k
  have h2 : (k : Int) * ((a * (W \ S).prod id / k : Nat) : Int)
      + ((a * (W \ S).prod id % k : Nat) : Int) = (a : Int) * ((W \ S).prod id : Nat) := by
    exact_mod_cast h
  linear_combination (-1 : Int) ^ S.card * h2

/-- **An even split, read off the remainders**, proved. -/
theorem even_split_iff_remainders_cancel_holds : even_split_iff_remainders_cancel := by
  intro W k a hW
  have h := sawtooth_identity_holds W k a hW
  constructor
  · intro he
    have he' : (k : Int) * (survivors_upto W (a * W.prod id / k)).card
        = (a : Int) * (survivors_upto W (W.prod id)).card := by
      exact_mod_cast he
    linarith
  · intro hz
    have he' : (k : Int) * (survivors_upto W (a * W.prod id / k)).card
        = (a : Int) * (survivors_upto W (W.prod id)).card := by
      linarith
    exact_mod_cast he'

end RNS.Sawtooth

#print axioms RNS.Sawtooth.legendre_count_holds
#print axioms RNS.Sawtooth.sawtooth_identity_holds
#print axioms RNS.Sawtooth.even_split_iff_remainders_cancel_holds
