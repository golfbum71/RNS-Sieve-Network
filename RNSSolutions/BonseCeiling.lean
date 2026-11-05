/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BonseCeiling.Conclusions
import Mathlib.NumberTheory.Bertrand   -- `Nat.exists_prime_lt_and_le_two_mul`; brings in the
                                       -- big-operator lemmas used below
import Mathlib.Tactic.NormNum.Prime    -- `norm_num` proving small numbers prime
import Mathlib.Tactic.Linarith

/-!
# Proofs for BonseCeiling

Imports claims only, never other nodes' proofs. Rests on no other node.

Built clean by `lake build RNSSolutions` on 2026-11-05; `#print axioms` shows only
the standard three.

Idea (the classical proof, by strong induction over the primes). For a prime
`p` from 11 on, Bertrand's postulate gives a prime `q` with `p/2 < q < p`.
The wheels below `p` include `q` and every wheel below `q`, so the cycle for
`p` is at least `q` times the cycle for `q`. If `q` is at least 11, the cycle
for `q` exceeds `q` squared by induction, so the cycle for `p` exceeds `q`
cubed, which is at least four times `q` squared, which exceeds `p` squared
because `p < 2q`. If `q` is below 11, then `p` is at most 19 and the wheels
2, 3, 5, 7 (and 11, 13 when `p` is 17 or 19) already make the cycle large
enough.
-/

namespace RNS.BonseCeiling

/-- A prime below `m` is one of the wheels below `m`. -/
private theorem mem_active {q m : Nat} (hq : q.Prime) (h : q < m) : q ∈ active_primes m :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hq⟩

/-- The product of any set of the wheels below `m` divides their whole cycle. -/
private theorem subset_prod_dvd {s : Finset Nat} {m : Nat} (h : s ⊆ active_primes m) :
    s.prod id ∣ primorial_modulus m := by
  unfold primorial_modulus
  exact Dvd.intro_left _ (Finset.prod_sdiff h)

/-- The combined cycle is positive. -/
private theorem primorial_pos (m : Nat) : 0 < primorial_modulus m := by
  unfold primorial_modulus
  exact Finset.prod_pos fun i hi => (Finset.mem_filter.mp hi).2.pos

/-- For a prime `q` below `p`, the cycle for `p` is at least `q` times the
cycle for `q`. -/
private theorem cycle_step {q p : Nat} (hq : q.Prime) (hqp : q < p) :
    q * primorial_modulus q ≤ primorial_modulus p := by
  have hnot : q ∉ active_primes q := fun h =>
    (lt_irrefl q) (Finset.mem_range.mp (Finset.mem_filter.mp h).1)
  have hsub : insert q (active_primes q) ⊆ active_primes p := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact mem_active hq hqp
    · have hx' := Finset.mem_filter.mp hx
      exact mem_active hx'.2 (lt_trans (Finset.mem_range.mp hx'.1) hqp)
  have hdvd := subset_prod_dvd hsub
  rw [Finset.prod_insert hnot] at hdvd
  exact Nat.le_of_dvd (primorial_pos p) hdvd

/-- A prime from 11 on is odd. -/
private theorem odd_of_ge_eleven {p : Nat} (hp : p.Prime) (h : 11 ≤ p) : p % 2 = 1 := by
  by_contra hne
  have h2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

/-- **The ceiling lies inside one combined cycle**, proved. -/
theorem ceiling_inside_cycle_holds : ceiling_inside_cycle := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp h11
    have hodd := odd_of_ge_eleven hp h11
    obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (p / 2) (by omega)
    have hqp : q < p := by omega
    have hp2q : p < 2 * q := by omega
    have hstep := cycle_step hq hqp
    by_cases hq11 : 11 ≤ q
    · -- `q` is at least 11: use the induction hypothesis at `q`.
      have hih : q ^ 2 < primorial_modulus q := ih q hqp hq hq11
      have hq0 : 0 < q := hq.pos
      have a : p ^ 2 < 4 * q ^ 2 := by nlinarith [hp2q, hq0, Nat.zero_le p]
      have b : 4 * q ^ 2 ≤ q * q ^ 2 := by nlinarith [hq11, Nat.zero_le (q ^ 2)]
      have c : q * q ^ 2 < q * primorial_modulus q := by nlinarith [hih, hq0]
      linarith
    · -- `q` is below 11, so `p` is at most 19: count the small wheels directly.
      have hp19 : p ≤ 19 := by omega
      by_cases hp13 : p ≤ 13
      · have hsub : ({2, 3, 5, 7} : Finset Nat) ⊆ active_primes p := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> exact mem_active (by norm_num) (by omega)
        have h210 : ({2, 3, 5, 7} : Finset Nat).prod id = 210 := by decide
        have hle210 : 210 ≤ primorial_modulus p := by
          rw [← h210]; exact Nat.le_of_dvd (primorial_pos p) (subset_prod_dvd hsub)
        have hsq : p ^ 2 ≤ 13 ^ 2 := Nat.pow_le_pow_left hp13 2
        norm_num at hsq
        linarith
      · have hsub : ({2, 3, 5, 7, 11, 13} : Finset Nat) ⊆ active_primes p := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact mem_active (by norm_num) (by omega)
        have h30030 : ({2, 3, 5, 7, 11, 13} : Finset Nat).prod id = 30030 := by decide
        have hle : 30030 ≤ primorial_modulus p := by
          rw [← h30030]; exact Nat.le_of_dvd (primorial_pos p) (subset_prod_dvd hsub)
        have hsq : p ^ 2 ≤ 19 ^ 2 := Nat.pow_le_pow_left hp19 2
        norm_num at hsq
        linarith

end RNS.BonseCeiling

#print axioms RNS.BonseCeiling.ceiling_inside_cycle_holds
