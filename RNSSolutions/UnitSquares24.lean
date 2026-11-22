/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.UnitSquares24.Conclusions
import Mathlib.Tactic

/-!
# Proofs for UnitSquares24

Built clean by `lake build RNSSolutions` on 2026-11-22; `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`.

Divisors of 24: every unit of the cycle of 24 squares to 1 (a finite check),
and the units of a divisor all come from units of 24
(`ZMod.unitsMap_surjective`).

Conversely: if 5 divides the cycle length, the position 2 on the wheel of 5
lifts to an open position of the cycle, and 2 squared is not 1 on the wheel of
5; otherwise 5 itself is open, and 5 squared being 1 makes the cycle length
divide 25 − 1 = 24.
-/

namespace RNS.UnitSquares24

theorem units_square_one_iff_holds : units_square_one_iff := by
  intro m hm
  haveI : NeZero m := ⟨hm⟩
  constructor
  · intro h
    by_cases h5 : 5 ∣ m
    · exfalso
      obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective h5 (ZMod.unitOfCoprime 2 (by decide))
      have h1 : (ZMod.unitsMap h5 v) ^ 2 = 1 := by rw [← map_pow, h v, map_one]
      rw [hv] at h1
      have h2 := congrArg (fun u : (ZMod 5)ˣ => (u : ZMod 5)) h1
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h2
      exact absurd h2 (by decide)
    · have hc : Nat.Coprime 5 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5
      have h1 := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) (h (ZMod.unitOfCoprime 5 hc))
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h1
      have h2 : ((25 : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
        rw [show (25 : ℕ) = 5 ^ 2 by norm_num, Nat.cast_pow, h1, Nat.cast_one]
      rw [ZMod.natCast_eq_natCast_iff'] at h2
      have h3 : 1 ≡ 25 [MOD m] := h2.symm
      exact (Nat.modEq_iff_dvd' (by norm_num)).mp h3
  · intro hdvd u
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hdvd u
    have key : ∀ x y : ZMod 24, x * y = 1 → x ^ 2 = 1 := by decide +kernel
    have hv : v ^ 2 = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact key _ _ v.mul_inv)
    rw [← map_pow, hv, map_one]

theorem prime_sq_mod_24_step (h : units_square_one_iff) : prime_sq_mod_24 := by
  intro p hp h5
  have hc : Nat.Coprime p 24 := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> first | omega | norm_num at hp
  have h1 := congrArg (fun u : (ZMod 24)ˣ => (u : ZMod 24))
    (((h 24 (by norm_num)).mpr dvd_rfl) (ZMod.unitOfCoprime p hc))
  simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h1
  have h2 : ((p ^ 2 : ℕ) : ZMod 24) = ((1 : ℕ) : ZMod 24) := by
    rw [Nat.cast_pow, h1, Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  simpa using h2

theorem prime_sq_mod_24_holds : prime_sq_mod_24 :=
  prime_sq_mod_24_step units_square_one_iff_holds

end RNS.UnitSquares24

#print axioms RNS.UnitSquares24.units_square_one_iff_holds
#print axioms RNS.UnitSquares24.prime_sq_mod_24_holds
