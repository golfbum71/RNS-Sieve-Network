/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SophieGermainTheorem.Conclusions
import RNSNetwork.Nodes.SophieGermainPowers.Conclusions
import Mathlib.RingTheory.Int.Basic                               -- odd powers, primes in ℤ
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity  -- `pow_dvd_pow_iff_dvd`
import Mathlib.RingTheory.PrincipalIdealDomain                    -- `isCoprime_of_prime_dvd`
import Mathlib.Algebra.Ring.GeomSum                               -- `Commute.geom_sum₂_mul`
import Mathlib.Data.Nat.Prime.Int                                 -- `Nat.prime_iff_prime_int`
import Mathlib.FieldTheory.Finite.Basic                           -- remainders mod a prime form a field
import Mathlib.Tactic.LinearCombination

/-!
# Proofs for SophieGermainTheorem

Imports claims only, never other nodes' proofs. Rests on `SophieGermainPowers`
(both claims) through `sophie_germain_theorem_step`; `fermat_first_case`
rests on `sophie_germain_theorem` through `fermat_first_case_step`. The steps
are joined to the proofs in `RNSSolutions/Assemble.lean`.

The classical proof. Write `q = 2p + 1`.
1. Divide out common factors, so `x, y, z` are pairwise coprime and none is
   divisible by `p`.
2. `y^p + z^p = (y + z) · C` with `C = Σ y^i (-z)^(p-1-i)`. The two factors
   are coprime (any common prime would divide `p y^(p-1)`), and their product
   is `(-x)^p`, so each is a `p`-th power: `y + z = a^p`, `C = α^p`. Likewise
   `z + x = b^p` and `x + y = c^p`.
3. The wheel of size `q` blocks one of `x, y, z` (SophieGermainPowers); by
   symmetry say `x`.
4. `c^p + b^p + (-a)^p = 2x`, so the wheel blocks one of `c, b, -a`. Not `c`
   or `b`: that would block `y` or `z` too, against coprimality. So it blocks
   `a`, hence `y + z`.
5. On the wheel, then, `C` sits where `p · y^(p-1)` does, and `y` sits where
   `c^p` does (since `x + y = c^p` and `x` is blocked), at 1 or -1. So
   `α^p` sits at `p`. But `α^p` sits at 0, 1 or -1, and `p` sits at none of
   them on a wheel of size `2p + 1`.
-/

namespace RNS.SophieGermainTheorem

open RNS.SophieGermainPowers

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

/-- Modulo `y + z`, the cofactor is `p · y^(p-1)`: there `-z` is `y`. -/
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
      exact hr.not_unit (hyz.isUnit_of_dvd' hry hrz)

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

/-- The wheel size `2p + 1` is not a unit. -/
private theorem wheel_not_unit {p : Nat} (hp : p.Prime) : ¬ IsUnit ((2 * p + 1 : Nat) : Int) := by
  intro hu
  have := hp.two_le
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> omega

/-- The heart of the proof, for pairwise coprime `x, y, z`, none divisible by
`p`, with the wheel of size `2p + 1` blocking `x`. -/
private theorem core {p : Nat} (hp : p.Prime) (hodd : Odd p) (hq : (2 * p + 1).Prime)
    (hpos : pth_power_positions) (hblock : three_powers_blocked) {x y z : Int}
    (h : x ^ p + y ^ p + z ^ p = 0) (hxy : IsCoprime x y) (hyz : IsCoprime y z)
    (hzx : IsCoprime z x) (hnp : ¬ (p : Int) ∣ x * y * z)
    (hqx : ((2 * p + 1 : Nat) : Int) ∣ x) : False := by
  haveI := Fact.mk hq
  have hpx : ¬ (p : Int) ∣ x := fun hd => hnp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd y) z)
  have hpy : ¬ (p : Int) ∣ y := fun hd => hnp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd x) z)
  have hpz : ¬ (p : Int) ∣ z := fun hd => hnp (dvd_mul_of_dvd_right hd (x * y))
  have hQ := wheel_not_unit hp
  -- Each pairwise sum is a `p`-th power.
  obtain ⟨⟨a, ha⟩, ⟨α, hα⟩⟩ := pair_powers hp hodd hyz
    (show y ^ p + z ^ p = (-x) ^ p by rw [hodd.neg_pow]; linear_combination h) hpx
  obtain ⟨⟨b, hb⟩, -⟩ := pair_powers hp hodd hzx
    (show z ^ p + x ^ p = (-y) ^ p by rw [hodd.neg_pow]; linear_combination h) hpy
  obtain ⟨⟨c, hc⟩, -⟩ := pair_powers hp hodd hxy
    (show x ^ p + y ^ p = (-z) ^ p by rw [hodd.neg_pow]; linear_combination h) hpz
  -- The wheel blocks `a`.
  have hsum2 : c ^ p + b ^ p + (-a) ^ p = 2 * x := by
    rw [hodd.neg_pow, ← hc, ← hb, ← ha]
    ring
  have hQsum : ((2 * p + 1 : Nat) : Int) ∣ c ^ p + b ^ p + (-a) ^ p := by
    rw [hsum2]
    exact dvd_mul_of_dvd_right hqx 2
  have hQc : ¬ ((2 * p + 1 : Nat) : Int) ∣ c := by
    intro hd
    have h1 : ((2 * p + 1 : Nat) : Int) ∣ x + y := by
      rw [hc]
      exact dvd_pow hd hp.ne_zero
    have hQy : ((2 * p + 1 : Nat) : Int) ∣ y := by
      have := dvd_sub h1 hqx
      simpa using this
    exact hQ (hxy.isUnit_of_dvd' hqx hQy)
  have hQb : ¬ ((2 * p + 1 : Nat) : Int) ∣ b := by
    intro hd
    have h1 : ((2 * p + 1 : Nat) : Int) ∣ z + x := by
      rw [hb]
      exact dvd_pow hd hp.ne_zero
    have hQz : ((2 * p + 1 : Nat) : Int) ∣ z := by
      have := dvd_sub h1 hqx
      simpa using this
    exact hQ (hzx.isUnit_of_dvd' hQz hqx)
  have hQa : ((2 * p + 1 : Nat) : Int) ∣ a := by
    rcases hblock p hp hq c b (-a) hQsum with h1 | h1 | h1
    · exact absurd h1 hQc
    · exact absurd h1 hQb
    · exact dvd_neg.mp h1
  have hQyz : ((2 * p + 1 : Nat) : Int) ∣ y + z := by
    rw [ha]
    exact dvd_pow hQa hp.ne_zero
  -- On the wheel: `α^p` sits where `p · y^(p-1)` does.
  have e1 : (α : ZMod (2 * p + 1)) ^ p = (p : ZMod (2 * p + 1)) * (y : ZMod (2 * p + 1)) ^ (p - 1) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 * p + 1)).mpr (dvd_trans hQyz (cof_cong y z p))
    rw [hα] at this
    push_cast at this
    exact sub_eq_zero.mp this
  -- `y` sits where `c^p` does, at 1 or -1.
  have e2 : (c : ZMod (2 * p + 1)) ^ p = (y : ZMod (2 * p + 1)) := by
    have hx0 : (x : ZMod (2 * p + 1)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hqx
    have := congrArg (fun t : Int => (t : ZMod (2 * p + 1))) hc
    push_cast at this
    rw [hx0, zero_add] at this
    exact this.symm
  have hc1 : (c : ZMod (2 * p + 1)) ^ p = 1 ∨ (c : ZMod (2 * p + 1)) ^ p = -1 := by
    rcases hpos p hp hq c with h0 | h1 | h1
    · exfalso
      push_cast at h0
      apply hQc
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (pow_eq_zero_iff hp.ne_zero).mp h0
    · left
      push_cast at h1
      exact h1
    · right
      push_cast at h1
      exact h1
  have heven : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  have hy1 : (y : ZMod (2 * p + 1)) ^ (p - 1) = 1 := by
    rw [← e2]
    rcases hc1 with h1 | h1 <;> rw [h1]
    · exact one_pow _
    · exact heven.neg_one_pow
  have hαp : (α : ZMod (2 * p + 1)) ^ p = (p : ZMod (2 * p + 1)) := by
    rw [e1, hy1, mul_one]
  -- But `α^p` sits at 0, 1 or -1, and `p` sits at none of them.
  have h2 := hp.two_le
  rcases hpos p hp hq α with h0 | h1 | h1
  · push_cast at h0
    rw [hαp, ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd hp.pos h0
    omega
  · push_cast at h1
    rw [hαp] at h1
    have h3 : ((p - 1 : Nat) : ZMod (2 * p + 1)) = 0 := by
      rw [Nat.cast_sub hp.one_le, h1, Nat.cast_one, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by omega) h3
    omega
  · push_cast at h1
    rw [hαp] at h1
    have h3 : ((p + 1 : Nat) : ZMod (2 * p + 1)) = 0 := by
      push_cast
      rw [h1]
      ring
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by omega) h3
    omega

/-- **Sophie Germain's theorem**, from the two wheel facts. -/
theorem sophie_germain_theorem_step (hpos : pth_power_positions)
    (hblock : three_powers_blocked) : sophie_germain_theorem := by
  intro p hp hq x y z h
  by_contra hnp
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hnp (by simp)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hnp (by simp)
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- `p = 2`: a sum of three squares is 0 only when all three are 0.
    have : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    exact hx0 ((pow_eq_zero_iff two_ne_zero).mp this)
  -- Divide out the common factor of `x` and `y`; it divides `z` too.
  obtain ⟨g, x', y', hg, hcop, rfl, rfl⟩ := Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left y hx0)
  have hg0 : (g : Int) ≠ 0 := by exact_mod_cast hg.ne'
  rw [mul_pow, mul_pow] at h
  have hgz : (g : Int) ∣ z := by
    have : (g : Int) ^ p ∣ z ^ p := ⟨-(x' ^ p + y' ^ p), by linear_combination h⟩
    exact (pow_dvd_pow_iff_dvd hp.ne_zero).mp this
  obtain ⟨z', rfl⟩ := hgz
  rw [mul_pow] at h
  have h' : x' ^ p + y' ^ p + z' ^ p = 0 := by
    have : (g : Int) ^ p * (x' ^ p + y' ^ p + z' ^ p) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd ((pow_eq_zero_iff hp.ne_zero).mp h0) hg0
    · exact h0
  -- The reduced triple is pairwise coprime and still has `p` dividing none.
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
    exact hr.not_unit (hxy.isUnit_of_dvd' (hr.dvd_of_dvd_pow hrx) h1)
  have hzx : IsCoprime z' x' := by
    apply isCoprime_of_prime_dvd (fun hh => hx0' hh.2)
    intro r hr h1 h2
    have hry : r ∣ y' ^ p := by
      have : y' ^ p = -(x' ^ p + z' ^ p) := by linear_combination h'
      rw [this]
      exact dvd_neg.mpr (dvd_add (dvd_pow h2 hp.ne_zero) (dvd_pow h1 hp.ne_zero))
    exact hr.not_unit (hxy.isUnit_of_dvd' h2 (hr.dvd_of_dvd_pow hry))
  have hnp' : ¬ (p : Int) ∣ x' * y' * z' := by
    intro hd
    apply hnp
    have := Dvd.dvd.mul_right hd ((g : Int) ^ 3)
    rwa [show x' * y' * z' * (g : Int) ^ 3 = x' * g * (y' * g) * (g * z') by ring] at this
  -- The wheel of size `2p + 1` blocks one of the three; rotate it to the front.
  have hQsum : ((2 * p + 1 : Nat) : Int) ∣ x' ^ p + y' ^ p + z' ^ p := by
    rw [h']
    exact dvd_zero _
  rcases hblock p hp hq x' y' z' hQsum with hq1 | hq1 | hq1
  · exact core hp hodd hq hpos hblock h' hxy hyz hzx hnp' hq1
  · exact core hp hodd hq hpos hblock (by linear_combination h') hyz hzx hxy
      (by rwa [show y' * z' * x' = x' * y' * z' by ring]) hq1
  · exact core hp hodd hq hpos hblock (by linear_combination h') hzx hxy hyz
      (by rwa [show z' * x' * y' = x' * y' * z' by ring]) hq1

/-- **Fermat's first case for Sophie Germain primes**, from Sophie Germain's
theorem applied to `x, y, -z`. -/
theorem fermat_first_case_step (hsg : sophie_germain_theorem) : fermat_first_case := by
  intro p hp hp2 hq x y z h
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have h' : x ^ p + y ^ p + (-z) ^ p = 0 := by
    rw [hodd.neg_pow]
    linear_combination h
  have := hsg p hp hq x y (-z) h'
  rwa [show x * y * -z = -(x * y * z) by ring, dvd_neg] at this

end RNS.SophieGermainTheorem

#print axioms RNS.SophieGermainTheorem.sophie_germain_theorem_step
#print axioms RNS.SophieGermainTheorem.fermat_first_case_step
