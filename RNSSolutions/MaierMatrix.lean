/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.MaierMatrix.Conclusions
import Mathlib

/-!
# Proofs for MaierMatrix

Imports claims only, never other nodes' proofs. Rests on no other node.
`maier_irregularity` is cited, not proved.

Idea. The double count: both sides add 1 for each pair (row, column) whose
entry is prime; swap the order of the two sums. The row count: the entry map
`c ↦ r P + c` carries the prime entries of row `r` onto the primes of the
window, with inverse `n ↦ n − r P`. A prime `n` of the window has a surviving
column: a wheel dividing `n − r P` divides `n` (it divides `P`), so equals the
prime `n`; but every wheel is at most `P`, which is at most `r P`, below `n`.
-/

namespace RNS.MaierMatrix

theorem maier_column_identity_holds : maier_column_identity := by
  intro W rows U
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem maier_row_count_holds : maier_row_count := by
  intro W r U hW hr
  have hPpos : 0 < W.prod id := Finset.prod_pos (fun q hq => (hW q hq).pos)
  have hqP : ∀ q ∈ W, q ∣ W.prod id := fun q hq => Finset.dvd_prod_of_mem id hq
  have hrP : W.prod id ≤ r * W.prod id := Nat.le_mul_of_pos_left _ hr
  apply Finset.card_nbij' (fun c => r * W.prod id + c) (fun n => n - r * W.prod id)
  · intro c hc
    simp only [Finset.mem_coe, survivors_upto, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc] at hc ⊢
    obtain ⟨⟨⟨h1, hU⟩, _⟩, hp⟩ := hc
    exact ⟨⟨by omega, by omega⟩, hp⟩
  · intro n hn
    simp only [Finset.mem_coe, survivors_upto, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc] at hn ⊢
    obtain ⟨⟨hlo, hhi⟩, hp⟩ := hn
    have hsum : r * W.prod id + (n - r * W.prod id) = n := by omega
    refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, by rw [hsum]; exact hp⟩
    intro q hq hdvd
    have hqn : q ∣ n := by
      rw [← hsum]
      exact Nat.dvd_add (dvd_mul_of_dvd_right (hqP q hq) r) hdvd
    have hqeq : q = n := (Nat.prime_dvd_prime_iff_eq (hW q hq) hp).mp hqn
    have hqle : q ≤ W.prod id := Nat.le_of_dvd hPpos (hqP q hq)
    omega
  · intro c _
    show r * W.prod id + c - r * W.prod id = c
    omega
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hn
    show r * W.prod id + (n - r * W.prod id) = n
    omega

#print axioms RNS.MaierMatrix.maier_column_identity_holds
#print axioms RNS.MaierMatrix.maier_row_count_holds

end RNS.MaierMatrix
