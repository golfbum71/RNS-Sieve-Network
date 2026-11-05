/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.GermainCriterion.Conclusions
import RNSNetwork.Nodes.Sawtooth.Conclusions
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset   -- `Finset.sum_powerset_insert`
import Mathlib.Data.Nat.ModEq                  -- `Nat.ModEq.mul_left`
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Proofs for GermainCriterion

Imports claims only, never other nodes' proofs. The sufficient direction rests
on `Sawtooth.even_split_iff_remainders_cancel`, taken as a named hypothesis.

Drafted 2026-11-05; awaiting its first `lake build RNSSolutions`.

Idea. For the wheels `p`, `q`, the signed sum of `Sawtooth` has four terms:
the remainders of `a p q`, `a q`, `a p` and `a` on division by `k`, with signs
`+ - - +`. If `p` leaves remainder 1, the first two agree and so do the last
two. In the other case, `q` is the negative of `p` and `p q` is the negative
of 1, so the first and last remainders add up to `k` or are both 0, and so do
the middle two; and they are 0 together, since `p` shares no factor with `k`.
-/

namespace RNS.GermainCriterion

/-- The four-term form of the signed sum for two wheels. -/
private theorem pair_remainder_sum (p q k a : Nat) (hpq : p ≠ q) :
    ∑ S ∈ ({p, q} : Finset Nat).powerset,
        (-1 : Int) ^ S.card * ((a * (({p, q} : Finset Nat) \ S).prod id % k : Nat) : Int)
      = ((a * (p * q) % k : Nat) : Int) - ((a * q % k : Nat) : Int)
          - ((a * p % k : Nat) : Int) + ((a % k : Nat) : Int) := by
  have hnot : p ∉ ({q} : Finset Nat) := by
    simp only [Finset.mem_singleton]; exact hpq
  have hps : ({q} : Finset Nat).powerset = {∅, {q}} := by
    ext t
    simp only [Finset.mem_powerset, Finset.subset_singleton_iff, Finset.mem_insert,
      Finset.mem_singleton]
  have h0 : (∅ : Finset Nat) ≠ {q} := (Finset.singleton_ne_empty q).symm
  have e1 : ({p, q} : Finset Nat) \ {q} = {p} := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; aesop
  have e2 : ({p, q} : Finset Nat) \ {p} = {q} := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; aesop
  rw [Finset.sum_powerset_insert hnot, hps, Finset.sum_pair h0, Finset.sum_pair h0]
  simp only [Finset.card_empty, Finset.sdiff_empty, Finset.card_singleton, Finset.insert_empty,
    Finset.card_pair hpq, e1, e2, Finset.sdiff_self, Finset.prod_pair hpq,
    Finset.prod_singleton, Finset.prod_empty, id, pow_zero, pow_one, Nat.mul_one]
  ring

/-- Two remainders that add up to a multiple of `k` add up to 0 or to `k`. -/
private theorem pair_mod_cases {X W k : Nat} (hX : X < k) (hW : W < k)
    (h : (X + W) % k = 0) : X + W = 0 ∨ X + W = k := by
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · interval_cases t <;> simp_all
  · exfalso
    nlinarith

theorem two_wheel_split_of_remainders_step
    (h_cancel : RNS.Sawtooth.even_split_iff_remainders_cancel) :
    two_wheel_split_of_remainders := by
  intro p q k a hp hq hpq hk hcase
  have hW : ∀ r ∈ ({p, q} : Finset Nat), r.Prime := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hp
    · exact hq
  rw [h_cancel {p, q} k a hW, pair_remainder_sum p q k a hpq]
  rcases hcase with h1 | h1 | ⟨hsq, hneg⟩
  · -- `p` leaves remainder 1
    have hA : a * p % k = a % k := by
      have := Nat.ModEq.mul_left a h1
      simpa using this
    have hB : a * (p * q) % k = a * q % k := by
      have := Nat.ModEq.mul_left (a * q) h1
      have e : a * (p * q) = a * q * p := by ring
      rw [e]; simpa using this
    rw [hA, hB]; ring
  · -- `q` leaves remainder 1
    have hA : a * q % k = a % k := by
      have := Nat.ModEq.mul_left a h1
      simpa using this
    have hB : a * (p * q) % k = a * p % k := by
      have := Nat.ModEq.mul_left (a * p) h1
      have e : a * (p * q) = a * p * q := by ring
      rw [e]; simpa using this
    rw [hA, hB]; ring
  · -- `p * p` leaves remainder 1 and `p + q` is a multiple of `k`
    -- the four remainders
    set X := a * (p * q) % k with hXdef
    set Y := a * q % k with hYdef
    set Z := a * p % k with hZdef
    set W := a % k with hWdef
    have hX : X < k := Nat.mod_lt _ hk
    have hY : Y < k := Nat.mod_lt _ hk
    have hZ : Z < k := Nat.mod_lt _ hk
    have hWk : W < k := Nat.mod_lt _ hk
    -- `p q + 1` is a multiple of `k`
    have hpq1 : (p * q + 1) % k = 0 := by
      have e1 : (p * (p + q)) % k = 0 := by
        rw [Nat.mul_mod, hneg, Nat.mul_zero, Nat.zero_mod]
      have e2 : (p * p + p * q) % k = 0 := by
        have e : p * (p + q) = p * p + p * q := by ring
        rw [← e]; exact e1
      have e3 : (p * p + p * q) % k = (1 + p * q) % k := by
        rw [Nat.add_mod, hsq, ← Nat.add_mod]
      rw [Nat.add_comm]; rw [← e3]; exact e2
    have hXW : (X + W) % k = 0 := by
      rw [hXdef, hWdef, ← Nat.add_mod]
      have e : a * (p * q) + a = a * (p * q + 1) := by ring
      rw [e, Nat.mul_mod, hpq1, Nat.mul_zero, Nat.zero_mod]
    have hYZ : (Y + Z) % k = 0 := by
      rw [hYdef, hZdef, ← Nat.add_mod]
      have e : a * q + a * p = a * (p + q) := by ring
      rw [e, Nat.mul_mod, hneg, Nat.mul_zero, Nat.zero_mod]
    -- `W = 0` exactly when `Z = 0`, since `p` shares no factor with `k`
    have hWZ : W = 0 ↔ Z = 0 := by
      constructor
      · intro h
        rw [hZdef, Nat.mul_mod, ← hWdef, h, Nat.zero_mul, Nat.zero_mod]
      · intro h
        have h2 : a * p * p % k = 0 := by
          rw [Nat.mul_mod, ← hZdef, h, Nat.zero_mul, Nat.zero_mod]
        have h3 : a * p * p % k = a % k := by
          have := Nat.ModEq.mul_left a hsq
          have e : a * (p * p) = a * p * p := by ring
          rw [← e]; simpa using this
        rw [hWdef, ← h3, h2]
    rcases pair_mod_cases hX hWk hXW with h1 | h1 <;>
      rcases pair_mod_cases hY hZ hYZ with h2 | h2
    · have : X = 0 := by omega
      have : W = 0 := by omega
      have : Y = 0 := by omega
      have : Z = 0 := by omega
      omega
    · exfalso
      have hW0 : W = 0 := by omega
      have hZ0 := hWZ.mp hW0
      omega
    · exfalso
      have hZ0 : Z = 0 := by omega
      have hW0 := hWZ.mpr hZ0
      omega
    · omega

end RNS.GermainCriterion

#print axioms RNS.GermainCriterion.two_wheel_split_of_remainders_step
