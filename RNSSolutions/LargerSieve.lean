/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.LargerSieve.Conclusions
import Mathlib

/-!
# Proofs for LargerSieve

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. For one wheel, split the set by position; the pairs sharing a position
number the sum of the squared part sizes, which by Cauchy–Schwarz
(`sq_sum_le_card_mul_sum_sq`) is at least the square of the set's size over
the number of occupied positions. Summed with the weights this is a lower
bound for the weighted pair count. Swapping the sums, the weighted count is a
sum over pairs: a pair of equal members contributes at most the total weight;
a pair of different members contributes at most the weight of the divisors
of their difference, which is the logarithm of the difference
(`ArithmeticFunction.vonMangoldt_sum`), below `log N`.
-/

namespace RNS.LargerSieve

open ArithmeticFunction

/-- The pairs of members of `A` at the same position of the wheel `q`. -/
private def pairs (A : Finset Nat) (q : Nat) : Nat :=
  ((A ×ˢ A).filter (fun x => x.1 % q = x.2 % q)).card

/-- Cauchy–Schwarz for one wheel: the size of `A` squared is at most the
number of occupied positions times the pairs sharing a position. -/
private theorem pairs_lower (A : Finset Nat) (q : Nat) :
    A.card ^ 2 ≤ classes A q * pairs A q := by
  have hmapA : (A : Set Nat).MapsTo (fun a => a % q) (A.image (fun a => a % q) : Set Nat) := by
    intro a ha
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp ha))
  have hsum := Finset.card_eq_sum_card_fiberwise hmapA
  have hmapP : (((A ×ˢ A).filter (fun x => x.1 % q = x.2 % q) : Finset (Nat × Nat)) :
      Set (Nat × Nat)).MapsTo (fun x => x.1 % q) (A.image (fun a => a % q) : Set Nat) := by
    intro x hx
    have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_product.mp hx'.1).1)
  have hpairs := Finset.card_eq_sum_card_fiberwise hmapP
  have hfib : ∀ c, (((A ×ˢ A).filter (fun x => x.1 % q = x.2 % q)).filter
      (fun x => x.1 % q = c)).card = (A.filter (fun a => a % q = c)).card ^ 2 := by
    intro c
    rw [sq, ← Finset.card_product]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨h1, h4⟩, ⟨h2, by rw [← h3]; exact h4⟩⟩
    · rintro ⟨⟨h1, h4⟩, ⟨h2, h5⟩⟩
      exact ⟨⟨⟨h1, h2⟩, h4.trans h5.symm⟩, h4⟩
  unfold pairs classes
  rw [hpairs, Finset.sum_congr rfl (fun c _ => hfib c)]
  conv_lhs => rw [hsum]
  exact sq_sum_le_card_mul_sum_sq

/-- Two different members of the window: the weights of the wheels at which
they share a position add up to at most `log N`. -/
private theorem offdiag_bound (S : Finset Nat) {M N a b : Nat} (ha : M ≤ a ∧ a < M + N)
    (hb : M ≤ b ∧ b < M + N) (hne : a ≠ b) :
    ∑ q ∈ S, vonMangoldt q * (if a % q = b % q then (1 : ℝ) else 0) ≤ Real.log N := by
  have hcond : ∀ q, a % q = b % q → q ∣ (max a b - min a b) := by
    intro q hq
    rcases le_total a b with h | h
    · rw [max_eq_right h, min_eq_left h]
      exact (Nat.modEq_iff_dvd' h).mp hq
    · rw [max_eq_left h, min_eq_right h]
      exact (Nat.modEq_iff_dvd' h).mp hq.symm
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hd0 : max a b - min a b ≠ 0 := by omega
  have hdN : max a b - min a b ≤ N := by omega
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  calc ∑ q ∈ S.filter (fun q => a % q = b % q), vonMangoldt q
      ≤ ∑ q ∈ (max a b - min a b).divisors, vonMangoldt q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          exact Nat.mem_divisors.mpr ⟨hcond q (Finset.mem_filter.mp hq).2, hd0⟩
        · intro q _ _
          exact vonMangoldt_nonneg
    _ = Real.log ((max a b - min a b : Nat) : ℝ) := vonMangoldt_sum
    _ ≤ Real.log N := by
        apply Real.log_le_log
        · have : 0 < max a b - min a b := Nat.pos_of_ne_zero hd0
          exact_mod_cast this
        · exact_mod_cast hdN

/-- A pair of equal members counts each wheel at most once. -/
private theorem diag_bound (S : Finset Nat) (a b : Nat) :
    ∑ q ∈ S, vonMangoldt q * (if a % q = b % q then (1 : ℝ) else 0) ≤
      ∑ q ∈ S, vonMangoldt q := by
  apply Finset.sum_le_sum
  intro q _
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]
    exact vonMangoldt_nonneg

private theorem weight_div_le (A S : Finset Nat) :
    ∑ q ∈ S, vonMangoldt q / (classes A q : ℝ) ≤ ∑ q ∈ S, vonMangoldt q := by
  apply Finset.sum_le_sum
  intro q _
  rcases Nat.eq_zero_or_pos (classes A q) with h | h
  · rw [h, Nat.cast_zero, div_zero]
    exact vonMangoldt_nonneg
  · exact div_le_self vonMangoldt_nonneg (by exact_mod_cast h)

theorem larger_sieve_holds : larger_sieve := by
  intro A S M N hA hden
  have hdiagA : (A ×ˢ A).filter (fun x => x.1 = x.2) = A.diag := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_diag]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3 ▸ h1⟩, h3⟩
  have hoffA : (A ×ˢ A).filter (fun x => ¬ x.1 = x.2) = A.offDiag := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  -- the weighted pair count from below
  have hlow : (A.card : ℝ) ^ 2 * ∑ q ∈ S, vonMangoldt q / (classes A q : ℝ) ≤
      ∑ q ∈ S, vonMangoldt q * (pairs A q : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    have hR : ((A.card : ℝ)) ^ 2 ≤ (classes A q : ℝ) * (pairs A q : ℝ) := by
      exact_mod_cast pairs_lower A q
    rcases Nat.eq_zero_or_pos (classes A q) with hc | hc
    · rw [hc, Nat.cast_zero, div_zero, mul_zero]
      exact mul_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
    · have hcpos : (0 : ℝ) < classes A q := by exact_mod_cast hc
      calc (A.card : ℝ) ^ 2 * (vonMangoldt q / (classes A q : ℝ))
          = vonMangoldt q * ((A.card : ℝ) ^ 2 / (classes A q : ℝ)) := by ring
        _ ≤ vonMangoldt q * (pairs A q : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
          rw [div_le_iff₀ hcpos]
          linarith
  -- the weighted pair count from above
  have hup : ∑ q ∈ S, vonMangoldt q * (pairs A q : ℝ) ≤
      (A.card : ℝ) * ∑ q ∈ S, vonMangoldt q +
        ((A.card * A.card - A.card : Nat) : ℝ) * Real.log N := by
    calc ∑ q ∈ S, vonMangoldt q * (pairs A q : ℝ)
        = ∑ q ∈ S, ∑ x ∈ A ×ˢ A,
            vonMangoldt q * (if x.1 % q = x.2 % q then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun q _ => ?_)
          unfold pairs
          rw [Finset.natCast_card_filter, Finset.mul_sum]
      _ = ∑ x ∈ A ×ˢ A, ∑ q ∈ S,
            vonMangoldt q * (if x.1 % q = x.2 % q then (1 : ℝ) else 0) := Finset.sum_comm
      _ ≤ ∑ x ∈ A ×ˢ A, (if x.1 = x.2 then ∑ q ∈ S, vonMangoldt q else Real.log N) := by
          apply Finset.sum_le_sum
          intro x hx
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
          split_ifs with h
          · exact diag_bound S x.1 x.2
          · exact offdiag_bound S (hA x.1 h1) (hA x.2 h2) h
      _ = (A.card : ℝ) * ∑ q ∈ S, vonMangoldt q +
            ((A.card * A.card - A.card : Nat) : ℝ) * Real.log N := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, hdiagA, hoffA,
            Finset.diag_card, Finset.offDiag_card, nsmul_eq_mul, nsmul_eq_mul]
  have hsub : ((A.card * A.card - A.card : Nat) : ℝ) = (A.card : ℝ) * A.card - A.card := by
    rw [Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
  rw [hsub] at hup
  have hs := weight_div_le A S
  set s1 := ∑ q ∈ S, vonMangoldt q with hs1
  set s2 := ∑ q ∈ S, vonMangoldt q / (classes A q : ℝ) with hs2
  set L := Real.log N with hL
  set a := (A.card : ℝ) with ha
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  rw [le_div_iff₀ (show (0 : ℝ) < s2 - L by linarith)]
  rcases eq_or_lt_of_le ha0 with h0 | hpos
  · rw [← h0]
    linarith
  · by_contra hcon
    push Not at hcon
    have h1 : 0 < a * (a * (s2 - L) - (s1 - L)) := mul_pos hpos (by linarith)
    nlinarith

theorem larger_sieve_few_holds : larger_sieve_few := by
  intro A S M N G hA hG hcl hden
  have hG' : (1 : ℝ) ≤ G := by exact_mod_cast hG
  have hGpos : (0 : ℝ) < G := by linarith
  have hs1 : 0 ≤ ∑ q ∈ S, vonMangoldt q := Finset.sum_nonneg fun q _ => vonMangoldt_nonneg
  have hdivle : (∑ q ∈ S, vonMangoldt q) / G ≤ ∑ q ∈ S, vonMangoldt q := div_le_self hs1 hG'
  rcases A.eq_empty_or_nonempty with hA0 | hAne
  · rw [hA0, Finset.card_empty, Nat.cast_zero]
    apply div_nonneg <;> linarith
  · have hge : (∑ q ∈ S, vonMangoldt q) / G ≤ ∑ q ∈ S, vonMangoldt q / (classes A q : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro q hq
      have hc : 0 < classes A q := by
        unfold classes
        exact Finset.card_pos.mpr (hAne.image _)
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by exact_mod_cast hc)
        (by exact_mod_cast hcl q hq)
    have hmain := larger_sieve_holds A S M N hA (by linarith)
    refine hmain.trans ?_
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)

#print axioms RNS.LargerSieve.larger_sieve_holds
#print axioms RNS.LargerSieve.larger_sieve_few_holds

end RNS.LargerSieve
