/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.RamanujanSums.Conclusions
import Mathlib.Algebra.BigOperators.Associated    -- `Finset.prod_primes_dvd`
import Mathlib.Algebra.Field.GeomSum              -- `geom_sum_eq`
import Mathlib.Algebra.BigOperators.Ring.Finset   -- `Finset.prod_add`, `Finset.sum_mul`
import Mathlib.Algebra.BigOperators.Intervals     -- `Finset.sum_Ico_eq_sum_range`
import Mathlib.Tactic.Ring

/-!
# Proofs for RamanujanSums

Imports claims only, never other nodes' proofs. Rests on no other node; the
first three helper lemmas repeat ones in `RNSSolutions/Sawtooth.lean`, with
complex numbers in place of integers.

Idea. Surviving every wheel, as a number 1 or 0, is a signed count over the
choices of wheels (Legendre). So the sum is a signed sum, over the choices,
of the turned multiples of the chosen wheels' product. The multiples of that
product, turned, go round a smaller circle whose size is the product of the
other wheels; going once round it adds up to its size if it divides the
frequency and to 0 otherwise. Multiplying out the wheel product gives the
same signed sum.
-/

namespace RNS.RamanujanSums

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
    (if ∀ q ∈ W, ¬ q ∣ n then (1 : ℂ) else 0)
      = ∑ S ∈ W.powerset, (-1 : ℂ) ^ S.card * (if S.prod id ∣ n then 1 else 0) := by
  rw [← Finset.prod_boole (s := W) (p := fun q => ¬ q ∣ n) (M₀ := ℂ)]
  have h1 : ∀ q ∈ W, (if ¬ q ∣ n then (1 : ℂ) else 0) = -(if q ∣ n then 1 else 0) + 1 := by
    intro q _
    split_ifs <;> simp_all
  rw [Finset.prod_congr rfl h1, Finset.prod_add]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have hS' : ∀ q ∈ S, q.Prime := fun q hq => hW q (Finset.mem_powerset.mp hS hq)
  rw [Finset.prod_const_one, mul_one, Finset.prod_neg, Finset.prod_boole]
  congr 1
  simp only [prod_dvd_iff hS' n]

/-- Dividing the cycle by the product of some of its wheels leaves the product
of the others. -/
private theorem complement_prod (W S : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (hS : S ⊆ W) :
    W.prod id / S.prod id = (W \ S).prod id := by
  have hpos : 0 < S.prod id :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun q hq => (hW q (hS hq)).ne_zero)
  rw [← Finset.prod_sdiff hS]
  exact Nat.mul_div_cancel _ hpos

/-- Going once round a circle of size `m`: if `r` turned `m` times is back to
the start, the powers `r ^ 1, ..., r ^ m` add up to `m` when `r` is 1 and to 0
otherwise. -/
private theorem period_sum {r : ℂ} {m : Nat} (hr : r ^ m = 1) :
    ∑ j ∈ Finset.Icc 1 m, r ^ j = if r = 1 then (m : ℂ) else 0 := by
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  split_ifs with h1
  · subst h1
    simp
  · have hg := geom_sum_eq h1 m
    rw [hr, sub_self, zero_div] at hg
    calc ∑ k ∈ Finset.range m, r ^ (1 + k) = r * ∑ k ∈ Finset.range m, r ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [pow_add, pow_one]
      _ = 0 := by rw [hg, mul_zero]

/-- The multiples of `d` in one cycle, turned by frequency `n`, add up to the
cycle length over `d` when that divides `n`, and to 0 otherwise. -/
private theorem multiples_root_sum (W : Finset Nat) (hW : ∀ q ∈ W, q.Prime) (d n : Nat)
    (hd : d ∣ W.prod id) :
    ∑ k ∈ Finset.Icc 1 (W.prod id), (if d ∣ k then (1 : ℂ) else 0) * cycle_root W ^ (k * n)
      = if W.prod id / d ∣ n then ((W.prod id / d : Nat) : ℂ) else 0 := by
  have hP : 0 < W.prod id :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun q hq => (hW q hq).ne_zero)
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hP
  have hPm : W.prod id = d * (W.prod id / d) := (Nat.mul_div_cancel' hd).symm
  have hζ : IsPrimitiveRoot (cycle_root W) (W.prod id) := by
    unfold cycle_root
    exact Complex.isPrimitiveRoot_exp _ hP.ne'
  have hη : IsPrimitiveRoot (cycle_root W ^ d) (W.prod id / d) := hζ.pow_of_dvd hdpos.ne' hd
  have hfilter : (Finset.Icc 1 (W.prod id)).filter (fun k => d ∣ k)
      = (Finset.Icc 1 (W.prod id / d)).image (fun j => d * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, j, rfl⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with h | h
        · subst h
          simp at h1
        · exact h
      · rw [hPm] at h2
        exact Nat.le_of_mul_le_mul_left h2 hdpos
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hdpos (by omega), ?_⟩, ⟨j, rfl⟩⟩
      rw [hPm]
      exact Nat.mul_le_mul_left d h2
  have hinj : Set.InjOn (fun j => d * j) ↑(Finset.Icc 1 (W.prod id / d)) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hdpos hab
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, hfilter, Finset.sum_image hinj]
  have hr : ((cycle_root W ^ d) ^ n) ^ (W.prod id / d) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hη.pow_eq_one, one_pow]
  calc ∑ j ∈ Finset.Icc 1 (W.prod id / d), cycle_root W ^ (d * j * n)
      = ∑ j ∈ Finset.Icc 1 (W.prod id / d), ((cycle_root W ^ d) ^ n) ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
    _ = if (cycle_root W ^ d) ^ n = 1 then ((W.prod id / d : Nat) : ℂ) else 0 := period_sum hr
    _ = _ := by simp only [hη.pow_eq_one_iff_dvd]

/-- **The wheel product**, proved. -/
theorem ramanujan_wheel_product_holds : ramanujan_wheel_product := by
  intro W hW n
  unfold ramanujan_sum
  have hsurv : ∑ k ∈ survivors_upto W (W.prod id), cycle_root W ^ (k * n)
      = ∑ k ∈ Finset.Icc 1 (W.prod id),
          (if ∀ q ∈ W, ¬ q ∣ k then (1 : ℂ) else 0) * cycle_root W ^ (k * n) := by
    unfold survivors_upto
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [hsurv]
  simp only [survives_expand W hW, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ S ∈ W.powerset,
      ∑ k ∈ Finset.Icc 1 (W.prod id),
          (-1 : ℂ) ^ S.card * (if S.prod id ∣ k then 1 else 0) * cycle_root W ^ (k * n)
        = (-1 : ℂ) ^ S.card
            * (if (W \ S).prod id ∣ n then (((W \ S).prod id : Nat) : ℂ) else 0) := by
    intro S hS
    have hsub := Finset.mem_powerset.mp hS
    have hd : S.prod id ∣ W.prod id := Dvd.intro_left _ (Finset.prod_sdiff hsub)
    have h := multiples_root_sum W hW (S.prod id) n hd
    rw [complement_prod W S hW hsub] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [Finset.sum_congr rfl hterm]
  have hfactor : ∀ q ∈ W, (if q ∣ n then (q : ℂ) - 1 else -1)
      = (-1 : ℂ) + (if q ∣ n then (q : ℂ) else 0) := by
    intro q _
    split_ifs <;> ring
  rw [Finset.prod_congr rfl hfactor, Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS' : ∀ q ∈ W \ S, q.Prime := fun q hq => hW q (Finset.mem_sdiff.mp hq).1
  rw [Finset.prod_const, Finset.prod_ite_zero]
  congr 1
  by_cases h : ∀ q ∈ W \ S, q ∣ n
  · rw [if_pos h, if_pos ((prod_dvd_iff hS' n).mpr h), Nat.cast_prod]
    rfl
  · rw [if_neg h, if_neg (fun h' => h ((prod_dvd_iff hS' n).mp h'))]

end RNS.RamanujanSums

#print axioms RNS.RamanujanSums.ramanujan_wheel_product_holds
