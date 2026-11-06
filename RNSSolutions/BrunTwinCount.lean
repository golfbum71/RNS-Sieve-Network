/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunTwinCount.Conclusions
import Mathlib.Data.Nat.Count                          -- `Nat.count_add`, `Nat.count_monotone`
import Mathlib.Data.ZMod.Basic                         -- `ZMod.chineseRemainder`, `ZMod.val_natCast`
import Mathlib.Algebra.Field.ZMod                      -- `ZMod p` is a field for prime `p`
import Mathlib.SetTheory.Cardinal.Finite               -- `Nat.card_congr`, `Nat.card_prod`
import Mathlib.Data.Nat.GCD.BigOperators               -- `Nat.Coprime.prod_right`
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset -- `Finset.prod_pos`
import Mathlib.Algebra.Group.Units.Equiv               -- `Equiv.addRight`
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Proofs for BrunTwinCount

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea, in four pieces.

* Shift. The positions 1 to `N` with a property are the positions 0 to
  `N - 1` with the property moved up by one, so the count is Mathlib's
  `Nat.count` of the moved property.
* One cycle at a time. If the property repeats with the cycle, then a full
  cycle followed by any stretch counts the cycle plus the stretch
  (`Nat.count_add`). So the count up to `N` is the number of full cycles
  times the count in one cycle, plus the count in the leftover piece, which
  is between zero and the count in one cycle.
* One cycle is the residues. Sending a position to its residue matches one
  cycle with the residues of the product; the twin condition becomes a
  residue times the residue two further on being zero.
* Split by wheels. The Chinese Remainder Theorem turns residues of a product
  of two coprime numbers into pairs of residues, so the number of twin
  roots multiplies. For a prime wheel the residues form a field, and the
  roots are zero and minus two: one root for the wheel at 2, two otherwise.
-/

namespace RNS.BrunTwinCount

/-! ### Shift and one cycle at a time -/

/-- The positions 1 to `N` with a property, counted by `Nat.count` of the
property moved up by one. -/
theorem ioc_count_eq (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ((Finset.Ioc 0 N).filter P).card = Nat.count (fun k => P (k + 1)) N := by
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_nbij' (fun m => m - 1) (fun k => k + 1)
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨h1, h2⟩, h3⟩ := hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    have h : m - 1 + 1 = m := by omega
    refine ⟨by omega, ?_⟩
    show P (m - 1 + 1)
    rw [h]
    exact h3
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨h1, h2⟩ := hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, h2⟩
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm
    obtain ⟨⟨h1, _⟩, _⟩ := hm
    show m - 1 + 1 = m
    omega
  · intro k _
    show k + 1 - 1 = k
    omega

/-- A full cycle followed by any stretch counts the cycle plus the stretch. -/
theorem count_period_add (Q : ℕ → Prop) [DecidablePred Q] (d : ℕ)
    (hQ : ∀ k, Q (d + k) ↔ Q k) (N : ℕ) :
    Nat.count Q (d + N) = Nat.count Q d + Nat.count Q N := by
  rw [Nat.count_add]
  congr 1
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    Finset.filter_congr (fun k _ => hQ k)]

/-- A number of full cycles followed by a stretch. -/
theorem count_period_mul (Q : ℕ → Prop) [DecidablePred Q] (d : ℕ)
    (hQ : ∀ k, Q (d + k) ↔ Q k) (q r : ℕ) :
    Nat.count Q (q * d + r) = q * Nat.count Q d + Nat.count Q r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * d + r = d + (q * d + r) by ring, count_period_add Q d hQ, ih]
    ring

/-- **The count of a repeating property.** Up to `N` it is `N` times the
count in one cycle divided by the cycle, off by at most the count in one
cycle. -/
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

/-! ### One cycle is the residues -/

/-- The twin condition repeats with the cycle. -/
theorem twin_periodic (d k : ℕ) :
    d ∣ (d + k + 1) * (d + k + 1 + 2) ↔ d ∣ (k + 1) * (k + 1 + 2) := by
  have h : (d + k + 1) * (d + k + 1 + 2) = d * (d + 2 * k + 4) + (k + 1) * (k + 1 + 2) := by
    ring
  rw [h]
  exact Nat.dvd_add_right (dvd_mul_right d _)

/-- The twin positions in one cycle match the twin roots among the residues. -/
theorem twin_period_count (d : ℕ) (hd : 0 < d) :
    Nat.count (fun k => d ∣ (k + 1) * (k + 1 + 2)) d =
      Nat.card {x : ZMod d // x * (x + 2) = 0} := by
  have : NeZero d := ⟨hd.ne'⟩
  have e1 : Nat.card {x : ZMod d // x * (x + 2) = 0} =
      Nat.card {x : ZMod d // (x + 1) * (x + 1 + 2) = 0} :=
    (Nat.card_congr (Equiv.subtypeEquiv (Equiv.addRight (1 : ZMod d)) (fun x => Iff.rfl))).symm
  rw [e1, Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.count_eq_card_filter_range]
  apply Finset.card_nbij' (fun k : ℕ => (k : ZMod d)) (fun x : ZMod d => x.val)
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter] at hk
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := (ZMod.natCast_eq_zero_iff ((k + 1) * (k + 1 + 2)) d).mpr hk.2
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
    exact h
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt x, ?_⟩
    show d ∣ (x.val + 1) * (x.val + 1 + 2)
    rw [← ZMod.natCast_eq_zero_iff]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    exact hx.2
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
    show ((k : ZMod d)).val = k
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk.1]
  · intro x _
    show ((x.val : ℕ) : ZMod d) = x
    exact ZMod.natCast_zmod_val x

/-! ### Split by wheels -/

/-- The twin roots of a product of two coprime numbers are pairs of twin roots
(Chinese Remainder Theorem). -/
theorem twin_roots_mul (m n : ℕ) (h : m.Coprime n) :
    Nat.card {x : ZMod (m * n) // x * (x + 2) = 0} =
      Nat.card {x : ZMod m // x * (x + 2) = 0} * Nat.card {x : ZMod n // x * (x + 2) = 0} := by
  let e := ZMod.chineseRemainder h
  rw [← Nat.card_prod]
  apply Nat.card_congr
  refine (Equiv.subtypeEquiv e.toEquiv
    (q := fun y : ZMod m × ZMod n => y.1 * (y.1 + 2) = 0 ∧ y.2 * (y.2 + 2) = 0) ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun a : ZMod m => a * (a + 2) = 0)
      (q := fun b : ZMod n => b * (b + 2) = 0))
  intro x
  have hx : e (x * (x + 2)) = e x * (e x + 2) := by
    rw [map_mul, map_add, map_ofNat]
  show x * (x + 2) = 0 ↔ (e x).1 * ((e x).1 + 2) = 0 ∧ (e x).2 * ((e x).2 + 2) = 0
  rw [← e.injective.eq_iff, map_zero, hx, Prod.ext_iff]
  exact Iff.rfl

/-- One cycle of the empty product has one twin root. -/
theorem twin_roots_one : Nat.card {x : ZMod 1 // x * (x + 2) = 0} = 1 := by
  haveI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => Subsingleton.elim _ _)), Nat.card_zmod]

/-- A prime wheel has the twin roots zero and minus two: one root for the
wheel at 2, two for every other wheel. -/
theorem twin_roots_prime (p : ℕ) (hp : p.Prime) :
    Nat.card {x : ZMod p // x * (x + 2) = 0} = if p = 2 then 1 else 2 := by
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : (Finset.univ.filter (fun x : ZMod p => x * (x + 2) = 0)) = {0, -2} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, mul_eq_zero, add_eq_zero_iff_eq_neg]
  rw [hset]
  split_ifs with h2
  · subst h2
    have h2z : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
    have h2z' : (2 : ZMod 2) = 0 := by exact_mod_cast h2z
    have h : (-2 : ZMod 2) = 0 := by rw [h2z', neg_zero]
    rw [h]
    simp
  · have hne : (0 : ZMod p) ≠ -2 := by
      intro h
      rw [eq_comm, neg_eq_zero] at h
      have h2' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h2'
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')
    exact Finset.card_pair_eq_two_iff.mpr hne

/-- The twin roots of one cycle of a product of distinct prime wheels number
`twin_rho`. -/
theorem twin_roots_prod (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) :
    Nat.card {x : ZMod (D.prod id) // x * (x + 2) = 0} = twin_rho D := by
  induction D using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, twin_roots_one]
    simp [twin_rho]
  | insert a s ha ih =>
    have haP : a.Prime := hD a (Finset.mem_insert_self a s)
    have hsP : ∀ q ∈ s, q.Prime := fun q hq => hD q (Finset.mem_insert_of_mem hq)
    have hprod : (insert a s).prod id = a * s.prod id := Finset.prod_insert ha
    have hcop : a.Coprime (s.prod id) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hqa : a ≠ q := fun h => ha (by rw [h]; exact hq)
      exact (Nat.coprime_primes haP (hsP q hq)).mpr hqa
    rw [hprod, twin_roots_mul a (s.prod id) hcop, twin_roots_prime a haP, ih hsP]
    simp only [twin_rho, Finset.prod_insert ha]

/-! ### The twin multiples count -/

theorem twin_multiples_count_holds : twin_multiples_count := by
  intro D N hD
  have hd : 0 < D.prod id := Finset.prod_pos (fun p hp => (hD p hp).pos)
  have hcount : ((Finset.Ioc 0 N).filter (fun m => D.prod id ∣ m * (m + 2))).card
      = Nat.count (fun k => D.prod id ∣ (k + 1) * (k + 1 + 2)) N :=
    ioc_count_eq (fun m => D.prod id ∣ m * (m + 2)) N
  have hper := twin_period_count (D.prod id) hd
  rw [twin_roots_prod D hD] at hper
  have hb := count_bound_real (fun k => D.prod id ∣ (k + 1) * (k + 1 + 2)) (D.prod id) hd
    (fun k => twin_periodic (D.prod id) k) N
  rw [hper] at hb
  rw [hcount]
  exact hb

end RNS.BrunTwinCount

#print axioms RNS.BrunTwinCount.twin_multiples_count_holds
