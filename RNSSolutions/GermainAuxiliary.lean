/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.GermainAuxiliary.Conclusions
import RNSNetwork.Nodes.SophieGermainPowers.Conclusions
import Mathlib.RingTheory.Int.Basic                               -- odd powers, primes in ℤ
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity  -- `pow_dvd_pow_iff_dvd`
import Mathlib.RingTheory.PrincipalIdealDomain                    -- `isCoprime_of_prime_dvd`
import Mathlib.Algebra.Ring.GeomSum                               -- `Commute.geom_sum₂_mul`
import Mathlib.Data.Nat.Prime.Int                                 -- `Nat.prime_iff_prime_int`
import Mathlib.FieldTheory.Finite.Basic                           -- remainders mod a prime form a field
import Mathlib.Tactic.LinearCombination

/-!
# Proofs for GermainAuxiliary

Imports claims only, never other nodes' proofs. `auxiliary_prime_theorem`
and the two wheel certificates rest on no other node;
`sophie_germain_wheel_auxiliary` rests on `SophieGermainPowers`; the two
Fermat cases rest on the general theorem and a certificate. The steps are
joined in `RNSSolutions/Assemble.lean`. The first helpers repeat those in
`RNSSolutions/SophieGermainTheorem.lean`.

The proof of the general theorem is Sophie Germain's, with its two uses of
the wheel of size `2p + 1` replaced by the two auxiliary conditions:
"no neighbouring powers" makes the wheel block one of three `p`-th powers
that sum to 0, and "`p` is not a power position" is contradicted at the end,
where `p` is shown to sit at the `p`-th power of `α / c^(p-1)`.
-/

namespace RNS.GermainAuxiliary

/-- The cofactor of `y + z` in `y^p + z^p`, for odd `p`. -/
private def cof (y z : Int) (p : Nat) : Int :=
  ∑ i ∈ Finset.range p, y ^ i * (-z) ^ (p - 1 - i)

/-- For odd `p`, `y^p + z^p = (y + z) · cof`. -/
private theorem factor {p : Nat} (hodd : Odd p) (y z : Int) :
    (y + z) * cof y z p = y ^ p + z ^ p := by
  have h := (Commute.all y (-z)).geom_sum₂_mul p
  rw [hodd.neg_pow] at h
  unfold cof
  linear_combination h

/-- Modulo `y + z`, the cofactor is `p · y^(p-1)`. -/
private theorem cof_cong (y z : Int) (p : Nat) :
    y + z ∣ cof y z p - (p : Int) * y ^ (p - 1) := by
  have hsplit : ∑ i ∈ Finset.range p, y ^ i * y ^ (p - 1 - i) = (p : Int) * y ^ (p - 1) := by
    calc ∑ i ∈ Finset.range p, y ^ i * y ^ (p - 1 - i)
        = ∑ _i ∈ Finset.range p, y ^ (p - 1) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [← pow_add]
          congr 1
          have := Finset.mem_range.mp hi
          omega
      _ = (p : Int) * y ^ (p - 1) := by simp
  unfold cof
  rw [← hsplit, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i _
  have hd : y + z ∣ (-z) ^ (p - 1 - i) - y ^ (p - 1 - i) := by
    have := sub_dvd_pow_sub_pow (-z) y (p - 1 - i)
    rwa [show -z - y = -(y + z) by ring, neg_dvd] at this
  rw [← mul_sub]
  exact dvd_mul_of_dvd_right hd _

/-- If `y, z` are coprime and `p` does not divide `(y + z) · cof`, the two
factors are coprime. -/
private theorem cof_coprime {p : Nat} (hp : p.Prime) {y z : Int} (hyz : IsCoprime y z)
    (hnd : ¬ (p : Int) ∣ (y + z) * cof y z p) : IsCoprime (y + z) (cof y z p) := by
  apply isCoprime_of_prime_dvd
  · rintro ⟨h1, -⟩
    apply hnd
    rw [h1, zero_mul]
    exact dvd_zero _
  · intro r hr h1 h2
    have h3 : r ∣ (p : Int) * y ^ (p - 1) := by
      have := dvd_sub h2 (dvd_trans h1 (cof_cong y z p))
      rwa [sub_sub_cancel] at this
    rcases hr.dvd_or_dvd h3 with h4 | h4
    · have hra : r.natAbs ∣ p := by
        have := Int.natAbs_dvd_natAbs.mpr h4
        simpa using this
      have heq : r.natAbs = p :=
        (Nat.prime_dvd_prime_iff_eq (Int.prime_iff_natAbs_prime.mp hr) hp).mp hra
      have hpr : (p : Int) ∣ r := Int.natAbs_dvd_natAbs.mp (by simp [heq])
      exact hnd (dvd_mul_of_dvd_left (dvd_trans hpr h1) _)
    · have hry : r ∣ y := hr.dvd_of_dvd_pow h4
      have hrz : r ∣ z := by
        have := dvd_sub h1 hry
        simpa using this
      exact hr.not_isUnit (hyz.isUnit_of_dvd' hry hrz)

/-- For coprime `y, z` with `y^p + z^p = w^p` and `p` not dividing `w`, both
`y + z` and the cofactor are `p`-th powers. -/
private theorem pair_powers {p : Nat} (hp : p.Prime) (hodd : Odd p) {y z w : Int}
    (hyz : IsCoprime y z) (hsum : y ^ p + z ^ p = w ^ p) (hpw : ¬ (p : Int) ∣ w) :
    (∃ a, y + z = a ^ p) ∧ ∃ e, cof y z p = e ^ p := by
  have hpZ : Prime (p : Int) := Nat.prime_iff_prime_int.mp hp
  have hfac := factor hodd y z
  rw [hsum] at hfac
  have hnd : ¬ (p : Int) ∣ (y + z) * cof y z p := by
    rw [hfac]
    intro hd
    exact hpw (hpZ.dvd_of_dvd_pow hd)
  exact Int.eq_pow_of_mul_eq_pow_odd (cof_coprime hp hyz hnd) hodd hfac

/-- A prime wheel size is not a unit. -/
private theorem wheel_not_unit {q : Nat} (hq : q.Prime) : ¬ IsUnit (q : Int) := by
  intro hu
  have := hq.two_le
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega

/-- With no neighbouring powers on the wheel of size `q`, the wheel blocks one
of three numbers whose `p`-th powers sum to a blocked position. -/
private theorem blocked {p q : Nat} (hodd : Odd p) (hq : q.Prime)
    (hnn : no_neighbouring_powers p q) {x y z : Int} (hs : (q : Int) ∣ x ^ p + y ^ p + z ^ p) :
    (q : Int) ∣ x ∨ (q : Int) ∣ y ∨ (q : Int) ∣ z := by
  have : Fact q.Prime := ⟨hq⟩
  by_contra hnone
  have hx : (x : ZMod q) ≠ 0 :=
    fun h => hnone (Or.inl ((ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp h))
  have hy : (y : ZMod q) ≠ 0 :=
    fun h => hnone (Or.inr (Or.inl ((ZMod.intCast_zmod_eq_zero_iff_dvd y q).mp h)))
  have hz : (z : ZMod q) ≠ 0 :=
    fun h => hnone (Or.inr (Or.inr ((ZMod.intCast_zmod_eq_zero_iff_dvd z q).mp h)))
  have hs' : (x : ZMod q) ^ p + (y : ZMod q) ^ p + (z : ZMod q) ^ p = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hs
    push_cast at this
    exact this
  have hZ : (z : ZMod q) ^ p ≠ 0 := pow_ne_zero p hz
  have hX : (x : ZMod q) ^ p = -((y : ZMod q) ^ p + (z : ZMod q) ^ p) := by
    linear_combination hs'
  apply hnn (-(x : ZMod q) * (z : ZMod q)⁻¹) ((y : ZMod q) * (z : ZMod q)⁻¹)
    (mul_ne_zero (neg_ne_zero.mpr hx) (inv_ne_zero hz)) (mul_ne_zero hy (inv_ne_zero hz))
  rw [mul_pow, mul_pow, hodd.neg_pow, inv_pow, hX, neg_neg, add_mul, mul_inv_cancel₀ hZ,
    add_comm]

/-- The heart of the general proof, for pairwise coprime `x, y, z`, none
divisible by `p`, with the wheel of size `q` blocking `x`. -/
private theorem core {p q : Nat} (hp : p.Prime) (hodd : Odd p) (hq : q.Prime)
    (hnn : no_neighbouring_powers p q) (hnpos : p_not_power_position p q) {x y z : Int}
    (h : x ^ p + y ^ p + z ^ p = 0) (hxy : IsCoprime x y) (hyz : IsCoprime y z)
    (hzx : IsCoprime z x) (hnp : ¬ (p : Int) ∣ x * y * z) (hqx : (q : Int) ∣ x) : False := by
  have : Fact q.Prime := ⟨hq⟩
  have hpx : ¬ (p : Int) ∣ x := fun hd => hnp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd y) z)
  have hpy : ¬ (p : Int) ∣ y := fun hd => hnp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd x) z)
  have hpz : ¬ (p : Int) ∣ z := fun hd => hnp (dvd_mul_of_dvd_right hd (x * y))
  have hQ := wheel_not_unit hq
  obtain ⟨⟨a, ha⟩, ⟨α, hα⟩⟩ := pair_powers hp hodd hyz
    (show y ^ p + z ^ p = (-x) ^ p by rw [hodd.neg_pow]; linear_combination h)
    (fun hd => hpx (dvd_neg.mp hd))
  obtain ⟨⟨b, hb⟩, -⟩ := pair_powers hp hodd hzx
    (show z ^ p + x ^ p = (-y) ^ p by rw [hodd.neg_pow]; linear_combination h)
    (fun hd => hpy (dvd_neg.mp hd))
  obtain ⟨⟨c, hc⟩, -⟩ := pair_powers hp hodd hxy
    (show x ^ p + y ^ p = (-z) ^ p by rw [hodd.neg_pow]; linear_combination h)
    (fun hd => hpz (dvd_neg.mp hd))
  have hsum2 : c ^ p + b ^ p + (-a) ^ p = 2 * x := by
    rw [hodd.neg_pow, ← hc, ← hb, ← ha]
    ring
  have hQsum : (q : Int) ∣ c ^ p + b ^ p + (-a) ^ p := by
    rw [hsum2]
    exact dvd_mul_of_dvd_right hqx 2
  have hQc : ¬ (q : Int) ∣ c := by
    intro hd
    have h1 : (q : Int) ∣ x + y := by
      rw [hc]
      exact dvd_pow hd hp.ne_zero
    have hQy : (q : Int) ∣ y := by
      have := dvd_sub h1 hqx
      simpa using this
    exact hQ (hxy.isUnit_of_dvd' hqx hQy)
  have hQb : ¬ (q : Int) ∣ b := by
    intro hd
    have h1 : (q : Int) ∣ z + x := by
      rw [hb]
      exact dvd_pow hd hp.ne_zero
    have hQz : (q : Int) ∣ z := by
      have := dvd_sub h1 hqx
      simpa using this
    exact hQ (hzx.isUnit_of_dvd' hQz hqx)
  have hQa : (q : Int) ∣ a := by
    rcases blocked hodd hq hnn hQsum with h1 | h1 | h1
    · exact absurd h1 hQc
    · exact absurd h1 hQb
    · exact dvd_neg.mp h1
  have hQyz : (q : Int) ∣ y + z := by
    rw [ha]
    exact dvd_pow hQa hp.ne_zero
  have e1 : (α : ZMod q) ^ p = (p : ZMod q) * (y : ZMod q) ^ (p - 1) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (dvd_trans hQyz (cof_cong y z p))
    rw [hα] at this
    push_cast at this
    exact sub_eq_zero.mp this
  have e2 : (c : ZMod q) ^ p = (y : ZMod q) := by
    have hx0 : (x : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hqx
    have := congrArg (fun t : Int => (t : ZMod q)) hc
    push_cast at this
    rw [hx0, zero_add] at this
    exact this.symm
  have hc0 : (c : ZMod q) ≠ 0 := fun h0 => hQc ((ZMod.intCast_zmod_eq_zero_iff_dvd c q).mp h0)
  have hy0 : (y : ZMod q) ≠ 0 := by
    rw [← e2]
    exact pow_ne_zero p hc0
  -- `p` sits at the `p`-th power of `α / c^(p-1)`.
  apply hnpos ((α : ZMod q) * ((c : ZMod q) ^ (p - 1))⁻¹)
  rw [mul_pow, inv_pow, ← pow_mul, mul_comm (p - 1) p, pow_mul, e2, e1, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hy0), mul_one]

/-- **Germain's general theorem**, proved. -/
theorem auxiliary_prime_theorem_holds : auxiliary_prime_theorem := by
  intro p q hp2 ⟨hp, hq, hnn, hnpos⟩ x y z h
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  by_contra hnp
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hnp (by simp)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hnp (by simp)
  obtain ⟨g, x', y', hg, hcop, rfl, rfl⟩ := Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left y hx0)
  have hg0 : (g : Int) ≠ 0 := by exact_mod_cast hg.ne'
  rw [mul_pow, mul_pow] at h
  have hgz : (g : Int) ∣ z := by
    have : (g : Int) ^ p ∣ z ^ p := ⟨-(x' ^ p + y' ^ p), by linear_combination h⟩
    exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hp.ne_zero).mp this
  obtain ⟨z', rfl⟩ := hgz
  rw [mul_pow] at h
  have h' : x' ^ p + y' ^ p + z' ^ p = 0 := by
    have : (g : Int) ^ p * (x' ^ p + y' ^ p + z' ^ p) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd ((pow_eq_zero_iff hp.ne_zero).mp h0) hg0
    · exact h0
  have hxy : IsCoprime x' y' := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hx0' : x' ≠ 0 := by
    rintro rfl
    exact hx0 (by simp)
  have hy0' : y' ≠ 0 := by
    rintro rfl
    exact hy0 (by simp)
  have hyz : IsCoprime y' z' := by
    apply isCoprime_of_prime_dvd (fun hh => hy0' hh.1)
    intro r hr h1 h2
    have hrx : r ∣ x' ^ p := by
      have : x' ^ p = -(y' ^ p + z' ^ p) := by linear_combination h'
      rw [this]
      exact dvd_neg.mpr (dvd_add (dvd_pow h1 hp.ne_zero) (dvd_pow h2 hp.ne_zero))
    exact hr.not_isUnit (hxy.isUnit_of_dvd' (hr.dvd_of_dvd_pow hrx) h1)
  have hzx : IsCoprime z' x' := by
    apply isCoprime_of_prime_dvd (fun hh => hx0' hh.2)
    intro r hr h1 h2
    have hry : r ∣ y' ^ p := by
      have : y' ^ p = -(x' ^ p + z' ^ p) := by linear_combination h'
      rw [this]
      exact dvd_neg.mpr (dvd_add (dvd_pow h2 hp.ne_zero) (dvd_pow h1 hp.ne_zero))
    exact hr.not_isUnit (hxy.isUnit_of_dvd' h2 (hr.dvd_of_dvd_pow hry))
  have hnp' : ¬ (p : Int) ∣ x' * y' * z' := by
    intro hd
    apply hnp
    have := Dvd.dvd.mul_right hd ((g : Int) ^ 3)
    rwa [show x' * y' * z' * (g : Int) ^ 3 = x' * g * (y' * g) * (g * z') by ring] at this
  have hQsum : (q : Int) ∣ x' ^ p + y' ^ p + z' ^ p := by
    rw [h']
    exact dvd_zero _
  rcases blocked hodd hq hnn hQsum with hq1 | hq1 | hq1
  · exact core hp hodd hq hnn hnpos h' hxy hyz hzx hnp' hq1
  · exact core hp hodd hq hnn hnpos (by linear_combination h') hyz hzx hxy
      (by rwa [show y' * z' * x' = x' * y' * z' by ring]) hq1
  · exact core hp hodd hq hnn hnpos (by linear_combination h') hzx hxy hyz
      (by rwa [show z' * x' * y' = x' * y' * z' by ring]) hq1

/-- On the wheel of size `2p + 1`, `p` sits at none of 0, 1, -1. -/
private theorem p_position {p : Nat} (hp : p.Prime) [Fact (2 * p + 1).Prime] :
    (p : ZMod (2 * p + 1)) ≠ 0 ∧ (p : ZMod (2 * p + 1)) ≠ 1 ∧ (p : ZMod (2 * p + 1)) ≠ -1 := by
  have h2 := hp.two_le
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd hp.pos h0
    omega
  · have h3 : ((p - 1 : Nat) : ZMod (2 * p + 1)) = 0 := by
      rw [Nat.cast_sub hp.one_le, h1, Nat.cast_one, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by omega) h3
    omega
  · have h3 : ((p + 1 : Nat) : ZMod (2 * p + 1)) = 0 := by
      push_cast
      rw [h1]
      ring
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by omega) h3
    omega

/-- **Sophie Germain primes give auxiliary primes**, from the three positions
of `p`-th powers on the wheel of size `2p + 1`. -/
theorem sophie_germain_wheel_auxiliary_step
    (hpos : RNS.SophieGermainPowers.pth_power_positions) : sophie_germain_wheel_auxiliary := by
  intro p hp hp2 hq
  have : Fact (2 * p + 1).Prime := ⟨hq⟩
  have hpos' : ∀ a : ZMod (2 * p + 1), a ^ p = 0 ∨ a ^ p = 1 ∨ a ^ p = -1 := by
    intro a
    have := hpos p hp hq (ZMod.cast a : Int)
    simpa [ZMod.intCast_zmod_cast] using this
  have h2 := hp.two_le
  have h3 : (3 : ZMod (2 * p + 1)) ≠ 0 := by
    intro h
    have h' : ((3 : Nat) : ZMod (2 * p + 1)) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  refine ⟨hp, hq, ?_, ?_⟩
  · intro a b ha hb hab
    have unit_pos : ∀ t : ZMod (2 * p + 1), t ≠ 0 → t ^ p = 1 ∨ t ^ p = -1 := by
      intro t ht
      rcases hpos' t with h0 | e | e
      · exact absurd ((pow_eq_zero_iff hp.ne_zero).mp h0) ht
      · exact Or.inl e
      · exact Or.inr e
    rcases unit_pos a ha with ea | ea <;> rcases unit_pos b hb with eb | eb <;>
      rw [ea, eb] at hab <;>
      first
        | exact one_ne_zero (by linear_combination hab)
        | exact one_ne_zero (by linear_combination -hab)
        | exact h3 (by linear_combination -hab)
  · intro a ha
    obtain ⟨n0, n1, nm1⟩ := p_position hp
    rcases hpos' a with e | e | e <;> rw [ha] at e
    · exact n0 e
    · exact n1 e
    · exact nm1 e

/-- **The wheel of size 29 is auxiliary for 7**, by checking the wheel. -/
theorem auxiliary_seven_holds : auxiliary_seven :=
  ⟨by norm_num, by norm_num, by unfold no_neighbouring_powers; decide +kernel,
    by unfold p_not_power_position; decide +kernel⟩

/-- **The wheel of size 53 is auxiliary for 13**, by checking the wheel. -/
theorem auxiliary_thirteen_holds : auxiliary_thirteen :=
  ⟨by norm_num, by norm_num, by unfold no_neighbouring_powers; decide +kernel,
    by unfold p_not_power_position; decide +kernel⟩

/-- **Fermat's first case for 7**, from the general theorem and the wheel of
size 29. -/
theorem fermat_first_case_seven_step (hthm : auxiliary_prime_theorem)
    (hcert : auxiliary_seven) : fermat_first_case_seven := by
  intro x y z h
  have h7 := hthm 7 29 (by norm_num) hcert x y (-z)
    (by rw [Odd.neg_pow ⟨3, by norm_num⟩]; linear_combination h)
  rw [show x * y * -z = -(x * y * z) by ring, dvd_neg] at h7
  exact_mod_cast h7

/-- **Fermat's first case for 13**, from the general theorem and the wheel of
size 53. -/
theorem fermat_first_case_thirteen_step (hthm : auxiliary_prime_theorem)
    (hcert : auxiliary_thirteen) : fermat_first_case_thirteen := by
  intro x y z h
  have h13 := hthm 13 53 (by norm_num) hcert x y (-z)
    (by rw [Odd.neg_pow ⟨6, by norm_num⟩]; linear_combination h)
  rw [show x * y * -z = -(x * y * z) by ring, dvd_neg] at h13
  exact_mod_cast h13

end RNS.GermainAuxiliary

#print axioms RNS.GermainAuxiliary.auxiliary_prime_theorem_holds
#print axioms RNS.GermainAuxiliary.sophie_germain_wheel_auxiliary_step
#print axioms RNS.GermainAuxiliary.auxiliary_seven_holds
#print axioms RNS.GermainAuxiliary.auxiliary_thirteen_holds
#print axioms RNS.GermainAuxiliary.fermat_first_case_seven_step
#print axioms RNS.GermainAuxiliary.fermat_first_case_thirteen_step
