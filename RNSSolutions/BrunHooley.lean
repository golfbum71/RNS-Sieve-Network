/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BrunHooley.Conclusions
import RNSNetwork.Nodes.BrunPureSieve.Conclusions
import RNSNetwork.Nodes.BrunTruncation.Conclusions
import Mathlib

/-!
# Proofs for BrunHooley

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. The expansion is distributivity: a product of sums is the sum over one
choice from each factor of the product of the choices (`Finset.prod_sum`).
For the upper-sieve property: each range's sieve sum is at least its
indicator (1 if no wheel of the range divides the number, 0 otherwise), and
these indicators are at least 0, so the product of the sieve sums is at least
the product of the indicators, which is 1 exactly when no wheel of any range
divides the number, and at least 0 otherwise.
-/

namespace RNS.BrunHooley

theorem combined_eq_product_holds : combined_eq_product := by
  intro I P wt n
  unfold combined_sieve_sum sieve_sum
  exact (Finset.prod_sum I (fun i => (P i).powerset)
    (fun i D => if (∀ q ∈ D, q ∣ n) then wt i D else 0)).symm

theorem product_upper_sieve_holds : product_upper_sieve := by
  intro I P wt hup n
  rw [combined_eq_product_holds]
  have hind : ∀ i ∈ I, (0 : ℝ) ≤ if ∀ q ∈ P i, ¬ q ∣ n then (1 : ℝ) else 0 := by
    intro i _
    split_ifs <;> norm_num
  calc (if ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ n then (1 : ℝ) else 0)
      ≤ ∏ i ∈ I, (if ∀ q ∈ P i, ¬ q ∣ n then (1 : ℝ) else 0) := by
        by_cases h : ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ n
        · rw [if_pos h]
          exact le_of_eq (Finset.prod_eq_one (fun i hi => if_pos (h i hi))).symm
        · rw [if_neg h]
          exact Finset.prod_nonneg hind
    _ ≤ ∏ i ∈ I, sieve_sum (P i) (wt i) n :=
        Finset.prod_le_prod₀ hind (fun i hi => hup i hi n)

#print axioms RNS.BrunHooley.combined_eq_product_holds
#print axioms RNS.BrunHooley.product_upper_sieve_holds

/-! ## The Brun–Hooley bound (Ford, Theorem 2.3)

`brun_hooley_bound_step` takes three claims as named hypotheses: Bonferroni's
inequality for an even stopping point (`BrunPureSieve.bonferroni_even_fn`) and
the size of the truncation error (`BrunTruncation.truncation_error`,
`BrunTruncation.esymm_power_bound`); joined in `Assemble`.

Idea. At one number, Bonferroni with a single position says Brun's stopped
sum over one range is at least the indicator that no wheel of the range
divides it. Multiply over the ranges (as in `product_upper_sieve`) and expand
into a sum over choices. Summing over the positions turns each choice into its
sign times its multiple count, which is `X` times its share product plus its
remainder. The share part factors back into the product of the stopped sums
over the ranges, each at most one minus the shares plus the truncation error,
and the remainder part is at most the sum of the absolute remainders.
-/

/-- A one-position count. -/
private theorem card_Ioc_one (p : Prop) [Decidable p] :
    ((Finset.Ioc 0 1).filter (fun _ : ℕ => p)).card = if p then 1 else 0 := by
  split_ifs with h <;> simp [h]

/-- For distinct prime wheels, the product divides a number exactly when
every wheel does. -/
private theorem prod_dvd_iff (D : Finset ℕ) (hD : ∀ q ∈ D, q.Prime) (m : ℕ) :
    D.prod id ∣ m ↔ ∀ q ∈ D, q ∣ m :=
  ⟨fun h q hq => dvd_trans (Finset.dvd_prod_of_mem id hq) h,
   fun h => Finset.prod_primes_dvd m (fun q hq => (hD q hq).prime) h⟩

/-- Brun's sieve stopped at an even number of wheels is an upper sieve on one
range, at every number. -/
private theorem one_range (hbon : RNS.BrunPureSieve.bonferroni_even_fn) (P : Finset ℕ)
    (b m : ℕ) (hP : ∀ q ∈ P, q.Prime) (hb : Even b) :
    (if ∀ q ∈ P, ¬ q ∣ m then (1 : ℝ) else 0) ≤
      ∑ D ∈ small_sets P b, if (∀ q ∈ D, q ∣ m) then (-1 : ℝ) ^ D.card else 0 := by
  have h : (((Finset.Ioc 0 1).filter (fun _ : ℕ => ∀ q ∈ P, ¬ q ∣ m)).card : ℤ) ≤
      ∑ D ∈ P.powerset.filter (fun D => D.card ≤ b),
        (-1 : ℤ) ^ D.card * (((Finset.Ioc 0 1).filter (fun _ : ℕ => D.prod id ∣ m)).card : ℤ) :=
    hbon P (fun _ => m) 1 b hP hb
  rw [card_Ioc_one] at h
  have hsum : ∀ D ∈ P.powerset.filter (fun D => D.card ≤ b),
      (-1 : ℤ) ^ D.card * (((Finset.Ioc 0 1).filter (fun _ : ℕ => D.prod id ∣ m)).card : ℤ) =
        if (∀ q ∈ D, q ∣ m) then (-1 : ℤ) ^ D.card else 0 := by
    intro D hD
    have hDP : D ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
    have hiff := prod_dvd_iff D (fun q hq => hP q (hDP hq)) m
    rw [card_Ioc_one]
    by_cases hd : ∀ q ∈ D, q ∣ m
    · rw [if_pos (hiff.mpr hd), if_pos hd]
      simp
    · rw [if_neg (fun h' => hd (hiff.mp h')), if_neg hd]
      simp
  rw [Finset.sum_congr rfl hsum] at h
  unfold small_sets
  exact_mod_cast h

theorem brun_hooley_bound_step (hbon : RNS.BrunPureSieve.bonferroni_even_fn)
    (htr : RNS.BrunTruncation.truncation_error) (hpow : RNS.BrunTruncation.esymm_power_bound) :
    brun_hooley_bound := by
  intro I P b S val X g hb hP hX hg
  -- the pointwise upper sieve for all the ranges, expanded over choices
  have hpt : ∀ m : ℕ, (if ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ m then (1 : ℝ) else 0) ≤
      ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)),
        ∏ x ∈ I.attach,
          (if ∀ q ∈ c x.1 x.2, q ∣ m then (-1 : ℝ) ^ (c x.1 x.2).card else 0) := by
    intro m
    have hind : ∀ i ∈ I, (0 : ℝ) ≤ if ∀ q ∈ P i, ¬ q ∣ m then (1 : ℝ) else 0 := by
      intro i _
      split_ifs <;> norm_num
    calc (if ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ m then (1 : ℝ) else 0)
        ≤ ∏ i ∈ I, (if ∀ q ∈ P i, ¬ q ∣ m then (1 : ℝ) else 0) := by
          by_cases h : ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ m
          · rw [if_pos h]
            exact le_of_eq (Finset.prod_eq_one (fun i hi => if_pos (h i hi))).symm
          · rw [if_neg h]
            exact Finset.prod_nonneg hind
      _ ≤ ∏ i ∈ I, ∑ D ∈ small_sets (P i) (b i),
            (if (∀ q ∈ D, q ∣ m) then (-1 : ℝ) ^ D.card else 0) :=
          Finset.prod_le_prod₀ hind (fun i hi => one_range hbon (P i) (b i) m (hP i hi) (hb i hi))
      _ = ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)),
            ∏ x ∈ I.attach,
              (if ∀ q ∈ c x.1 x.2, q ∣ m then (-1 : ℝ) ^ (c x.1 x.2).card else 0) :=
          Finset.prod_sum I (fun i => small_sets (P i) (b i))
            (fun i D => if (∀ q ∈ D, q ∣ m) then (-1 : ℝ) ^ D.card else 0)
  -- summing over the positions: sign times multiple count
  have hc : ∀ c : (i : ℕ) → i ∈ I → Finset ℕ,
      ∑ n ∈ S, ∏ x ∈ I.attach,
          (if ∀ q ∈ c x.1 x.2, q ∣ val n then (-1 : ℝ) ^ (c x.1 x.2).card else 0) =
        (∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) * (choice_count I S val c : ℝ) := by
    intro c
    have h1 : ∀ n ∈ S, (∏ x ∈ I.attach,
          (if ∀ q ∈ c x.1 x.2, q ∣ val n then (-1 : ℝ) ^ (c x.1 x.2).card else 0)) =
        if (∀ x ∈ I.attach, ∀ q ∈ c x.1 x.2, q ∣ val n) then
          ∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card else 0 :=
      fun n _ => by
        rw [Finset.prod_ite_zero]
        try (split_ifs <;> rfl)
    unfold choice_count
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- the share part factors into the stopped sums of the ranges
  have hmain : ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)),
        (∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) *
          ∏ x ∈ I.attach, ∏ q ∈ c x.1 x.2, g q =
      ∏ i ∈ I, RNS.BrunTruncation.trunc_prod (P i) g (b i) := by
    have h2 : ∀ c ∈ I.pi (fun i => small_sets (P i) (b i)),
        (∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) * ∏ x ∈ I.attach, ∏ q ∈ c x.1 x.2, g q =
          ∏ x ∈ I.attach, ((-1 : ℝ) ^ (c x.1 x.2).card * ∏ q ∈ c x.1 x.2, g q) :=
      fun c _ => (Finset.prod_mul_distrib).symm
    rw [Finset.sum_congr rfl h2]
    unfold RNS.BrunTruncation.trunc_prod
    exact (Finset.prod_sum I (fun i => small_sets (P i) (b i))
      (fun i D => (-1 : ℝ) ^ D.card * ∏ q ∈ D, g q)).symm
  -- each stopped sum lies between the product and the product plus the error
  have htrunc : ∀ i ∈ I, ∏ q ∈ P i, (1 - g q) ≤ RNS.BrunTruncation.trunc_prod (P i) g (b i) ∧
      RNS.BrunTruncation.trunc_prod (P i) g (b i) ≤ ∏ q ∈ P i, (1 - g q) +
        (∑ q ∈ P i, g q) ^ (b i + 1) / ((b i + 1).factorial : ℝ) := by
    intro i hi
    obtain ⟨h0, h1⟩ := htr (P i) g (b i) (hg i hi)
    have hp := hpow (P i) g (b i + 1) (fun q hq => (hg i hi q hq).1)
    rw [Even.neg_one_pow (hb i hi), one_mul] at h0 h1
    constructor <;> linarith
  have hVnonneg : ∀ i ∈ I, 0 ≤ ∏ q ∈ P i, (1 - g q) :=
    fun i hi => Finset.prod_nonneg (fun q hq => by linarith [(hg i hi q hq).2])
  -- each remainder term is at most its absolute value
  have hrem : ∀ c ∈ I.pi (fun i => small_sets (P i) (b i)),
      (∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) * choice_remainder I S val X g c ≤
        |choice_remainder I S val X g c| := by
    intro c _
    have habs : |∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card| = 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_eq_one (fun x _ => by simp)
    calc (∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) * choice_remainder I S val X g c
        ≤ |(∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) * choice_remainder I S val X g c| :=
          le_abs_self _
      _ = |choice_remainder I S val X g c| := by rw [abs_mul, habs, one_mul]
  have hsplit : ∀ c ∈ I.pi (fun i => small_sets (P i) (b i)),
      (∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) * (choice_count I S val c : ℝ) =
        X * ((∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) *
          ∏ x ∈ I.attach, ∏ q ∈ c x.1 x.2, g q) +
        (∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) * choice_remainder I S val X g c := by
    intro c _
    unfold choice_remainder
    ring
  have hcard : ((sifted_positions I P S val).card : ℝ) =
      ∑ n ∈ S, (if ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ val n then (1 : ℝ) else 0) := by
    unfold sifted_positions
    rw [Finset.natCast_card_filter]
  calc ((sifted_positions I P S val).card : ℝ)
      = ∑ n ∈ S, (if ∀ i ∈ I, ∀ q ∈ P i, ¬ q ∣ val n then (1 : ℝ) else 0) := hcard
    _ ≤ ∑ n ∈ S, ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)),
          ∏ x ∈ I.attach,
            (if ∀ q ∈ c x.1 x.2, q ∣ val n then (-1 : ℝ) ^ (c x.1 x.2).card else 0) :=
        Finset.sum_le_sum (fun n _ => hpt (val n))
    _ = ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)), ∑ n ∈ S,
          ∏ x ∈ I.attach,
            (if ∀ q ∈ c x.1 x.2, q ∣ val n then (-1 : ℝ) ^ (c x.1 x.2).card else 0) :=
        Finset.sum_comm
    _ = ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)),
          (∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) * (choice_count I S val c : ℝ) :=
        Finset.sum_congr rfl (fun c _ => hc c)
    _ = X * ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)),
            (∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) *
              ∏ x ∈ I.attach, ∏ q ∈ c x.1 x.2, g q +
          ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)),
            (∏ x ∈ I.attach, (-1 : ℝ) ^ (c x.1 x.2).card) * choice_remainder I S val X g c := by
        rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ X * ∏ i ∈ I, (∏ q ∈ P i, (1 - g q) +
            (∑ q ∈ P i, g q) ^ (b i + 1) / ((b i + 1).factorial : ℝ)) +
          ∑ c ∈ I.pi (fun i => small_sets (P i) (b i)), |choice_remainder I S val X g c| := by
        rw [hmain]
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ hX
          exact Finset.prod_le_prod₀
            (fun i hi => le_trans (hVnonneg i hi) (htrunc i hi).1) (fun i hi => (htrunc i hi).2)
        · exact Finset.sum_le_sum hrem

#print axioms RNS.BrunHooley.brun_hooley_bound_step

/-! ## The exponential form (Ford, Theorem 2.3) -/

theorem product_exp_bound_holds : product_exp_bound := by
  intro I V E hV hE
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i hi
    have h1 := hV i hi
    have h2 := hE i hi
    positivity
  · intro i hi
    have hv := hV i hi
    have hv0 : V i ≠ 0 := hv.ne'
    have h1 : 1 + E i / V i ≤ Real.exp (E i / V i) := by
      linarith [Real.add_one_le_exp (E i / V i)]
    calc V i + E i = V i * (1 + E i / V i) := by
          first
            | (field_simp; ring)
            | field_simp
      _ ≤ V i * Real.exp (E i / V i) := mul_le_mul_of_nonneg_left h1 hv.le

theorem brun_hooley_bound_exp_step (hbound : brun_hooley_bound) : brun_hooley_bound_exp := by
  intro I P b S val X g hb hP hX hg hg1
  have h := hbound I P b S val X g hb hP hX hg
  have hV : ∀ i ∈ I, 0 < ∏ q ∈ P i, (1 - g q) :=
    fun i hi => Finset.prod_pos (fun q hq => by linarith [hg1 i hi q hq])
  have hE : ∀ i ∈ I, 0 ≤ (∑ q ∈ P i, g q) ^ (b i + 1) / ((b i + 1).factorial : ℝ) := by
    intro i hi
    have hs : 0 ≤ ∑ q ∈ P i, g q := Finset.sum_nonneg (fun q hq => (hg i hi q hq).1)
    positivity
  have hexp : ∏ i ∈ I, (∏ q ∈ P i, (1 - g q) +
        (∑ q ∈ P i, g q) ^ (b i + 1) / ((b i + 1).factorial : ℝ)) ≤
      (∏ i ∈ I, ∏ q ∈ P i, (1 - g q)) *
        Real.exp (∑ i ∈ I, ((∑ q ∈ P i, g q) ^ (b i + 1) / ((b i + 1).factorial : ℝ)) /
          ∏ q ∈ P i, (1 - g q)) :=
    product_exp_bound_holds I (fun i => ∏ q ∈ P i, (1 - g q))
      (fun i => (∑ q ∈ P i, g q) ^ (b i + 1) / ((b i + 1).factorial : ℝ)) hV hE
  have hmul := mul_le_mul_of_nonneg_left hexp hX
  rw [← mul_assoc] at hmul
  linarith

#print axioms RNS.BrunHooley.product_exp_bound_holds
#print axioms RNS.BrunHooley.brun_hooley_bound_exp_step

end RNS.BrunHooley
