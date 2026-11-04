/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Data.Nat.Prime.Basic   -- `Nat.minFac` facts
import Mathlib.Tactic.Push                     -- `push Not`
import RNSNetwork.Nodes.SquareRootShield.Conclusions

/-!
# Proof for SquareRootShield

Proves `RNS.SquareRootShield.square_root_shield`. The tactic proof is the one
from `squareRootShield` in the `HardyLittlewood` repository (already compiled
on this Lean version), with the two private helpers written out in place.

Idea: a prime has no prime factor smaller than itself. Conversely, a number
that is not prime has some divisor between 2 and its square root (Mathlib's
`Nat.prime_def_le_sqrt`); that divisor's smallest prime factor is then a prime
factor of the number, smaller than it, and at most the square root of the
ceiling.
-/

namespace RNS.SquareRootShield

private theorem prime_has_no_small_proper_factor (x : Nat) (hx : x.Prime) :
    ¬ ∃ p, p.Prime ∧ p ∣ x ∧ p < x := by
  rintro ⟨p, hp, hpd, hplt⟩
  rcases hx.eq_one_or_self_of_dvd p hpd with h1 | h2
  · exact absurd h1 hp.one_lt.ne'
  · exact absurd h2 hplt.ne

theorem square_root_shield_holds : square_root_shield := by
  unfold square_root_shield
  intro X x hx2 hxX
  constructor
  · intro hx hcontra
    obtain ⟨p, hp, hpd, hplt, _⟩ := hcontra
    exact prime_has_no_small_proper_factor x hx ⟨p, hp, hpd, hplt⟩
  · intro hnot
    by_contra hxp
    have hiff := Nat.prime_def_le_sqrt (p := x)
    have hstep : ¬ ∀ m, 2 ≤ m → m ≤ x.sqrt → ¬ m ∣ x := by
      intro hall
      exact hxp (hiff.mpr ⟨hx2, hall⟩)
    push Not at hstep
    obtain ⟨m, hm2, hmle, hmdvd⟩ := hstep
    set p := m.minFac with hp_def
    have hm1 : m ≠ 1 := by omega
    have hp_prime : p.Prime := Nat.minFac_prime hm1
    have hp_dvd_m : p ∣ m := Nat.minFac_dvd m
    have hp_dvd_x : p ∣ x := hp_dvd_m.trans hmdvd
    have hp_le_m : p ≤ m := Nat.minFac_le (by omega)
    have hp_le_sqrtx : p ≤ Nat.sqrt x := hp_le_m.trans hmle
    have hsqrtx_le_sqrtX : Nat.sqrt x ≤ Nat.sqrt X := Nat.sqrt_le_sqrt hxX
    have hp_le_sqrtX : p ≤ Nat.sqrt X := hp_le_sqrtx.trans hsqrtx_le_sqrtX
    have hsqrtx_lt_x : Nat.sqrt x < x := Nat.sqrt_lt_self (by omega)
    have hp_lt_x : p < x := lt_of_le_of_lt hp_le_sqrtx hsqrtx_lt_x
    exact hnot ⟨p, hp_prime, hp_dvd_x, hp_lt_x, hp_le_sqrtX⟩

end RNS.SquareRootShield

#print axioms RNS.SquareRootShield.square_root_shield_holds
