/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.FortunateCeiling.Conclusions
import RNSNetwork.Nodes.ShieldCertificates.Conclusions
import Mathlib.Tactic.Positivity                  -- `Finset.prod_pos`
import Mathlib.Data.Nat.Prime.Basic               -- `Nat.not_prime_of_dvd_of_lt`
import Mathlib.Data.Nat.Prime.Infinite            -- `Nat.exists_infinite_primes`
import Mathlib.Data.Nat.PrimeFin                  -- `Nat.infinite_setOfPred_prime`
import Mathlib.Order.Lattice.Nat                  -- `Nat.sInf_mem`
import Mathlib.NumberTheory.LSeries.PrimesInAP    -- Dirichlet: `Nat.forall_exists_prime_gt_and_eq_mod`

/-!
# Proofs for FortunateCeiling

Imports claims only, never other nodes' proofs. The prime-below-the-ceiling
claims rest on `ShieldCertificates.window_prime_iff`, taken as a named
hypothesis; everything else rests on Mathlib only.

Idea. Add a number above 1 to the cycle of the wheels below a bound. If the sum
is prime, a wheel dividing the number would divide the sum as well, and the sum
is bigger than the wheel, so no wheel divides it. Its smallest prime factor is
therefore at least the bound, so the number is at least the bound; below the
bound's square the window claim makes it prime; a composite one is at least
the square of its smallest prime factor; and below the bound's cube a composite
one is its smallest prime factor times a prime (the cofactor cannot be
composite, since then it would be at least the bound squared).

The proof that a suitable composite always exists for A038771 follows the
`a_n_exists` proof in DeepMind's `formal-conjectures` (`OEIS/38771.lean`),
which uses Mathlib's Dirichlet theorem.
-/

namespace RNS.FortunateCeiling

private theorem cycle_pos (L : Nat) : 0 < primorial_modulus L := by
  unfold primorial_modulus
  apply Finset.prod_pos
  intro q hq
  unfold active_primes at hq
  exact (Finset.mem_filter.mp hq).2.pos

theorem shift_avoids_wheels_holds : shift_avoids_wheels := by
  intro L m q hm hP hq hqL hdvd
  have hmem : q ∈ active_primes L := by
    unfold active_primes
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqL, hq⟩
  have hqQ : q ∣ primorial_modulus L := by
    unfold primorial_modulus
    exact Finset.dvd_prod_of_mem id hmem
  have hsum : q ∣ primorial_modulus L + m := Nat.dvd_add hqQ hdvd
  have hQ : q ≤ primorial_modulus L := Nat.le_of_dvd (cycle_pos L) hqQ
  rcases hP.eq_one_or_self_of_dvd q hsum with h1 | h2
  · exact hq.one_lt.ne' h1
  · omega

/-- Every prime factor of a shift that lands on a prime is at least the bound. -/
private theorem factor_ge (L m : Nat) (hm : 1 < m) (hP : (primorial_modulus L + m).Prime)
    (q : Nat) (hq : q.Prime) (hqm : q ∣ m) : L ≤ q := by
  by_contra h
  exact shift_avoids_wheels_holds L m q hm hP hq (by omega) hqm

private theorem minFac_ge (L m : Nat) (hm : 1 < m) (hP : (primorial_modulus L + m).Prime) :
    L ≤ m.minFac :=
  factor_ge L m hm hP _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd m)

theorem shift_prime_below_ceiling_step (h_win : RNS.ShieldCertificates.window_prime_iff) :
    shift_prime_below_ceiling := by
  intro L m hm hP hmL
  have hLm : L ≤ m := le_trans (minFac_ge L m hm hP) (Nat.minFac_le (by omega))
  refine (h_win L m hLm hmL).mpr ?_
  intro q hq hdq
  unfold active_primes at hq
  rcases Finset.mem_filter.mp hq with ⟨hqr, hqp⟩
  exact shift_avoids_wheels_holds L m q hm hP hqp (Finset.mem_range.mp hqr) hdq

theorem composite_shift_at_least_ceiling_holds : composite_shift_at_least_ceiling := by
  intro L m hm hnp hP
  have h1 := minFac_ge L m hm hP
  have h2 : m.minFac ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hnp
  rw [pow_two] at h2
  exact le_trans (Nat.mul_le_mul h1 h1) h2

theorem composite_shift_semiprime_below_cube_holds : composite_shift_semiprime_below_cube := by
  intro L m hm hnp hP hcube
  have hpP : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hpL : L ≤ m.minFac := minFac_ge L m hm hP
  obtain ⟨r, hr⟩ := Nat.minFac_dvd m
  generalize m.minFac = p at hr hpP hpL
  have hr1 : r ≠ 1 := by
    rintro rfl
    exact hnp (by rw [hr, mul_one]; exact hpP)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    omega
  have hrp : r.Prime := by
    by_contra hrp
    have hdm : r.minFac ∣ m := by
      rw [hr]
      exact Dvd.dvd.mul_left (Nat.minFac_dvd r) p
    have hL2 : L ≤ r.minFac := factor_ge L m hm hP _ (Nat.minFac_prime hr1) hdm
    have hsq : r.minFac ^ 2 ≤ r := Nat.minFac_sq_le_self (by omega) hrp
    rw [pow_two] at hsq
    have hLLr : L * L ≤ r := le_trans (Nat.mul_le_mul hL2 hL2) hsq
    have hbig : L * L * L ≤ m := by
      rw [hr, mul_assoc]
      exact Nat.mul_le_mul hpL hLLr
    exact absurd hcube (not_lt.mpr hbig)
  rw [hr]
  exact Nat.Prime.mul_isAlmostPrime_two hpP hrp

/-- The primes below the `k`-th prime (counting from 0) are exactly the first `k`. -/
private theorem active_primes_nth (k : Nat) :
    active_primes (Nat.nth Nat.Prime k) = (Finset.range k).image (Nat.nth Nat.Prime) := by
  ext q
  simp only [active_primes, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hqk, hq⟩
    refine ⟨Nat.count Nat.Prime q, ?_, Nat.nth_count hq⟩
    have h := Nat.nth_count hq
    rw [← h] at hqk
    exact (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp hqk
  · rintro ⟨i, hik, rfl⟩
    exact ⟨(Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mpr hik,
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i⟩

theorem first_primes_eq_cycle_holds : first_primes_eq_cycle := by
  intro k
  have hinj : Set.InjOn (Nat.nth Nat.Prime) (Finset.range k : Set Nat) := by
    intro a _ b _ h
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h
  unfold primorial_modulus
  rw [active_primes_nth k, Finset.prod_image hinj]
  try rfl

theorem primorial_eq_cycle_holds : primorial_eq_cycle := by
  intro n
  unfold primorial primorial_modulus active_primes
  refine Finset.prod_congr ?_ (fun _ _ => rfl)
  ext q
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hq, hp⟩
    refine ⟨?_, hp⟩
    have := (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mpr (Nat.lt_succ_self n)
    omega
  · rintro ⟨hq, hp⟩
    refine ⟨?_, hp⟩
    have h := Nat.nth_count hp
    rw [← h] at hq ⊢
    have hc := (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp hq
    have := (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr (Nat.lt_succ_iff.mp hc)
    omega

/-! ## Fortune -/

private theorem shift_set_nonempty (Q : Nat) : {m : Nat | 1 < m ∧ (Q + m).Prime}.Nonempty := by
  obtain ⟨P, hP1, hP2⟩ := Nat.exists_infinite_primes (Q + 2)
  exact ⟨P - Q, show 1 < P - Q ∧ (Q + (P - Q)).Prime from
    ⟨by omega, by rwa [Nat.add_sub_of_le (show Q ≤ P by omega)]⟩⟩

theorem fortunate_spec_holds : fortunate_spec := by
  intro n
  exact Nat.sInf_mem (shift_set_nonempty (primorial (Nat.nth Nat.Prime n)))

theorem fortunate_at_least_next_prime_holds : fortunate_at_least_next_prime := by
  intro n
  obtain ⟨h1, h2⟩ := fortunate_spec_holds n
  rw [primorial_eq_cycle_holds n] at h2
  exact le_trans (minFac_ge _ _ h1 h2) (Nat.minFac_le (by omega))

theorem fortunate_prime_below_ceiling_step (h_win : RNS.ShieldCertificates.window_prime_iff) :
    fortunate_prime_below_ceiling := by
  intro n hlt
  obtain ⟨h1, h2⟩ := fortunate_spec_holds n
  rw [primorial_eq_cycle_holds n] at h2
  exact shift_prime_below_ceiling_step h_win _ _ h1 h2 hlt

theorem fortune_of_ceiling_step (h_win : RNS.ShieldCertificates.window_prime_iff) :
    fortune_of_ceiling := by
  intro h n
  exact fortunate_prime_below_ceiling_step h_win n (h n)

/-! ## OEIS A038771 -/

/-- A composite number that lands on a prime always exists (Dirichlet's theorem),
following `a_n_exists` in `formal-conjectures`' `OEIS/38771.lean`. -/
private theorem composite_set_nonempty (Q : Nat) (hQ : 0 < Q) :
    {c : Nat | (1 < c ∧ ¬ c.Prime) ∧ (Q + c).Prime}.Nonempty := by
  obtain ⟨q, hqQ, hq⟩ := Nat.exists_infinite_primes (Q + 1)
  have : NeZero q := ⟨hq.ne_zero⟩
  have hunit : IsUnit (Q : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).2 ?_)
    intro hd
    have := Nat.le_of_dvd hQ hd
    omega
  obtain ⟨p, hp, hpp, hpq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (Q + q)
  have hdvd : q ∣ p - Q := by
    have h := (ZMod.natCast_eq_natCast_iff p Q q).1 hpq
    exact (Nat.modEq_iff_dvd' (by omega)).1 h.symm
  exact ⟨p - Q, show (1 < p - Q ∧ ¬ (p - Q).Prime) ∧ (Q + (p - Q)).Prime from
    ⟨⟨by omega, Nat.not_prime_of_dvd_of_lt hdvd hq.two_le (by omega)⟩,
      by rwa [Nat.add_sub_of_le (show Q ≤ p by omega)]⟩⟩

theorem smallest_composite_shift_spec_holds : smallest_composite_shift_spec := by
  intro n
  have hQ : 0 < ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i := by
    rw [first_primes_eq_cycle_holds n]
    exact cycle_pos _
  exact Nat.sInf_mem (composite_set_nonempty _ hQ)

theorem smallest_composite_shift_floor_holds : smallest_composite_shift_floor := by
  intro n
  obtain ⟨⟨h1, h2⟩, h3⟩ := smallest_composite_shift_spec_holds n
  rw [first_primes_eq_cycle_holds n] at h3
  exact composite_shift_at_least_ceiling_holds _ _ h1 h2 h3

theorem smallest_composite_shift_semiprime_below_cube_holds :
    smallest_composite_shift_semiprime_below_cube := by
  intro n hlt
  obtain ⟨⟨h1, h2⟩, h3⟩ := smallest_composite_shift_spec_holds n
  rw [first_primes_eq_cycle_holds n] at h3
  exact composite_shift_semiprime_below_cube_holds _ _ h1 h2 h3 hlt

theorem semiprime_conjecture_of_cube_holds : semiprime_conjecture_of_cube := by
  intro h n
  exact smallest_composite_shift_semiprime_below_cube_holds n (h n)

end RNS.FortunateCeiling

#print axioms RNS.FortunateCeiling.shift_avoids_wheels_holds
#print axioms RNS.FortunateCeiling.shift_prime_below_ceiling_step
#print axioms RNS.FortunateCeiling.composite_shift_at_least_ceiling_holds
#print axioms RNS.FortunateCeiling.composite_shift_semiprime_below_cube_holds
#print axioms RNS.FortunateCeiling.first_primes_eq_cycle_holds
#print axioms RNS.FortunateCeiling.primorial_eq_cycle_holds
#print axioms RNS.FortunateCeiling.fortunate_spec_holds
#print axioms RNS.FortunateCeiling.fortunate_at_least_next_prime_holds
#print axioms RNS.FortunateCeiling.fortunate_prime_below_ceiling_step
#print axioms RNS.FortunateCeiling.fortune_of_ceiling_step
#print axioms RNS.FortunateCeiling.smallest_composite_shift_spec_holds
#print axioms RNS.FortunateCeiling.smallest_composite_shift_floor_holds
#print axioms RNS.FortunateCeiling.smallest_composite_shift_semiprime_below_cube_holds
#print axioms RNS.FortunateCeiling.semiprime_conjecture_of_cube_holds
