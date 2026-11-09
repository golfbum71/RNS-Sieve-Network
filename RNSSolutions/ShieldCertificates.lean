/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Algebra.Field.ZMod        -- remainders modulo a prime form a field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Push               -- `push Not`
import RNSNetwork.Nodes.SquareRootShield.Conclusions
import RNSNetwork.Nodes.Admissibility.Conclusions
import RNSNetwork.Nodes.ShieldCertificates.Conclusions

/-!
# Proofs for ShieldCertificates

Imports claims only. The certificate claims are proved as steps from
`SquareRootShield.square_root_shield`, taken as the hypothesis `h_srs`. The
two Lagrange–Waring claims for actual prime runs (forward and backward) are
proved as steps from `Admissibility.ap_offsets_admissible_iff`, taken as the
hypothesis `h_lw`: a prime run that starts above its length has an admissible
offset pattern, and the pattern criterion then gives the divisibility. The
other obstruction claims rest on no other node.

Tactic proofs are copied from the "Shield Certificates" sections of
`rns_sieve_6.lean`. The one adaptation: the source unfolds a private
`shield_radius` to reach `p ≤ Nat.sqrt X`, which the network's statement of
the square-root shield now states directly.
-/

namespace RNS.ShieldCertificates

/-! ## Certificates (steps from the square-root shield) -/

private theorem cover_aux (h_srs : RNS.SquareRootShield.square_root_shield)
    (X n : Nat) (P : Finset Nat) (hn2 : 2 ≤ n) (hnX : n ≤ X)
    (hcover : ∀ q, q.Prime → q * q ≤ X → q ∈ P)
    (havoid : ∀ q ∈ P, q < n → ¬ q ∣ n) : n.Prime := by
  refine (h_srs X n hn2 hnX).mpr ?_
  intro hcontra
  obtain ⟨p, hp, hpd, hplt, hple⟩ := hcontra
  have hpp : p * p ≤ X := Nat.le_sqrt.mp hple
  exact havoid p (hcover p hp hpp) hplt hpd

private theorem active_cover_aux (X L : Nat) (hL : X < L * L) :
    ∀ q, q.Prime → q * q ≤ X → q ∈ active_primes L := by
  intro q hq hqq
  unfold active_primes
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hq⟩
  by_contra hqL
  have hLq : L ≤ q := not_lt.mp hqL
  have hLL : L * L ≤ q * q := Nat.mul_le_mul hLq hLq
  exact absurd hqq (not_le.mpr (lt_of_lt_of_le hL hLL))

private theorem family_aux (h_srs : RNS.SquareRootShield.square_root_shield)
    (ι : Type) (s : Finset ι) (f : ι → Nat) (X : Nat) (P : Finset Nat)
    (hcover : ∀ q, q.Prime → q * q ≤ X → q ∈ P)
    (h2 : ∀ i ∈ s, 2 ≤ f i) (hX : ∀ i ∈ s, f i ≤ X)
    (havoid : ∀ i ∈ s, ∀ q ∈ P, q < f i → ¬ q ∣ f i) :
    ∀ i ∈ s, (f i).Prime :=
  fun i hi => cover_aux h_srs X (f i) P (h2 i hi) (hX i hi) hcover (havoid i hi)

theorem prime_of_shield_cover_step (h_srs : RNS.SquareRootShield.square_root_shield) :
    prime_of_shield_cover := by
  unfold prime_of_shield_cover
  exact cover_aux h_srs

theorem active_primes_cover_holds : active_primes_cover := by
  unfold active_primes_cover
  exact active_cover_aux

theorem family_prime_of_shield_cover_step
    (h_srs : RNS.SquareRootShield.square_root_shield) : family_prime_of_shield_cover := by
  unfold family_prime_of_shield_cover
  exact family_aux h_srs

theorem forward_ap_prime_of_active_shield_step
    (h_srs : RNS.SquareRootShield.square_root_shield) :
    forward_ap_prime_of_active_shield := by
  unfold forward_ap_prime_of_active_shield
  intro a d k X L hL hlast h2 havoid
  exact family_aux h_srs Nat (Finset.range k) (fun i => a + i * d) X
    (active_primes L) (active_cover_aux X L hL) h2
    (fun i hi => by
      have hik : i ≤ k - 1 := by
        have := Finset.mem_range.mp hi
        omega
      have hmul : i * d ≤ (k - 1) * d := Nat.mul_le_mul hik (le_refl d)
      exact (Nat.add_le_add (le_refl a) hmul).trans hlast)
    havoid

theorem backward_ap_prime_of_active_shield_step
    (h_srs : RNS.SquareRootShield.square_root_shield) :
    backward_ap_prime_of_active_shield := by
  unfold backward_ap_prime_of_active_shield
  intro a d k X L hL haX h2 havoid
  exact family_aux h_srs Nat (Finset.range k) (fun i => a - i * d) X
    (active_primes L) (active_cover_aux X L hL) h2
    (fun i _ => (Nat.sub_le a (i * d)).trans haX) havoid

theorem tuple_prime_of_active_shield_step
    (h_srs : RNS.SquareRootShield.square_root_shield) :
    tuple_prime_of_active_shield := by
  unfold tuple_prime_of_active_shield
  intro n X L T hL h2 hX havoid
  exact family_aux h_srs Nat T (fun t => n + t) X (active_primes L)
    (active_cover_aux X L hL) h2 hX havoid

/-! ## Why prime runs stop (the divisibility claim is a step from `Admissibility`) -/

private theorem ap_hits_wheel_aux (a d k q : Nat) (hq : q.Prime) (hnd : ¬ q ∣ d)
    (hqk : q ≤ k) : ∃ i ∈ Finset.range k, q ∣ a + i * d := by
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero q := ⟨hq.pos.ne'⟩
  have hdne : (d : ZMod q) ≠ 0 := fun h => hnd ((ZMod.natCast_eq_zero_iff d q).mp h)
  set y : ZMod q := -(a : ZMod q) * (d : ZMod q)⁻¹ with hydef
  refine ⟨y.val, Finset.mem_range.mpr (lt_of_lt_of_le (ZMod.val_lt y) hqk), ?_⟩
  apply (ZMod.natCast_eq_zero_iff (a + y.val * d) q).mp
  push_cast
  rw [ZMod.natCast_rightInverse y, hydef, mul_assoc, inv_mul_cancel₀ hdne, mul_one]
  exact add_eq_zero_iff_eq_neg.mpr (neg_neg _).symm

private theorem run_hits_wheel_aux (a d k q : Nat) (hq : q.Prime) (hnd : ¬ q ∣ d)
    (hqk : q ≤ k) (hall : ∀ i ∈ Finset.range k, (a + i * d).Prime) :
    ∃ i ∈ Finset.range k, a + i * d = q := by
  obtain ⟨i, hi, hdvd⟩ := ap_hits_wheel_aux a d k q hq hnd hqk
  refine ⟨i, hi, ?_⟩
  rcases (hall i hi).eq_one_or_self_of_dvd q hdvd with h1 | hself
  · exact absurd h1 hq.one_lt.ne'
  · exact hself.symm

private theorem run_length_lt_aux (a d k q : Nat) (hq : q.Prime) (hnd : ¬ q ∣ d)
    (hall : ∀ i ∈ Finset.range k, (a + i * d).Prime)
    (hnoq : ∀ i ∈ Finset.range k, a + i * d ≠ q) : k < q := by
  by_contra hkq
  have hqk : q ≤ k := not_lt.mp hkq
  obtain ⟨i, hi, heq⟩ := run_hits_wheel_aux a d k q hq hnd hqk hall
  exact hnoq i hi heq

private theorem run_length_lt_of_lt_start_aux (a d k q : Nat) (hq : q.Prime)
    (hnd : ¬ q ∣ d) (hqa : q < a)
    (hall : ∀ i ∈ Finset.range k, (a + i * d).Prime) : k < q :=
  run_length_lt_aux a d k q hq hnd hall (fun i _ h => by
    have hle : a ≤ a + i * d := Nat.le_add_right a (i * d)
    rw [h] at hle
    exact absurd hle (not_le.mpr hqa))

theorem ap_hits_wheel_holds : ap_hits_wheel := by
  unfold ap_hits_wheel
  exact ap_hits_wheel_aux

theorem ap_prime_run_length_lt_of_lt_start_holds : ap_prime_run_length_lt_of_lt_start := by
  unfold ap_prime_run_length_lt_of_lt_start
  exact run_length_lt_of_lt_start_aux

/-- A spacing step: the remainder that `a + i * d` hits zero at is the
complement of `a`'s remainder. -/
private theorem dvd_of_mod_eq_complement (a d i q : Nat) (hq : 0 < q)
    (h : i * d % q = (q - a % q) % q) : q ∣ a + i * d := by
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, h]
  have hr : a % q < q := Nat.mod_lt _ hq
  rcases Nat.eq_zero_or_pos (a % q) with h0 | hpos
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.zero_mod]
  · rw [Nat.mod_eq_of_lt (Nat.sub_lt hq hpos), Nat.add_sub_of_le hr.le, Nat.mod_self]

/-- **A prime run's pattern is admissible.** If every term of a forward run
is prime and the run starts above its length, no wheel is covered by the
run's offset pattern: a wheel no larger than the length would have to divide
some term, and a larger wheel has more positions than the run has terms. -/
private theorem ap_prime_run_admissible (a d k : Nat) (hka : k < a)
    (hall : ∀ i ∈ Finset.range k, (a + i * d).Prime) :
    is_admissible (ap_offsets d k) := by
  intro q hq
  unfold w
  by_cases hqk : q ≤ k
  · have hsub : (ap_offsets d k).image (fun t => t % q) ⊆ Finset.range q := by
      intro x hx
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Nat.mod_lt _ hq.pos)
    have hmiss : (q - a % q) % q ∉ (ap_offsets d k).image (fun t => t % q) := by
      intro hx
      obtain ⟨t, ht, hteq⟩ := Finset.mem_image.mp hx
      unfold ap_offsets at ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      have hdvd : q ∣ a + i * d := dvd_of_mod_eq_complement a d i q hq.pos hteq
      rcases (hall i hi).eq_one_or_self_of_dvd q hdvd with h1 | hself
      · exact hq.one_lt.ne' h1
      · have hle : a ≤ q := by
          rw [hself]
          exact Nat.le_add_right a (i * d)
        omega
    have hssub : (ap_offsets d k).image (fun t => t % q) ⊂ Finset.range q :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hmiss (by
        rw [h]
        exact Finset.mem_range.mpr (Nat.mod_lt _ hq.pos))⟩
    have hcard := Finset.card_lt_card hssub
    rwa [Finset.card_range] at hcard
  · have h1 : (ap_offsets d k).card ≤ k := by
      unfold ap_offsets
      exact Finset.card_image_le.trans (Finset.card_range k).le
    exact lt_of_le_of_lt (Finset.card_image_le.trans h1) (not_le.mp hqk)

/-- **Lagrange–Waring for prime runs, from the pattern criterion.** The run's
pattern is admissible (above), so `Admissibility.ap_offsets_admissible_iff`
gives every prime up to the length dividing the spacing. -/
theorem ap_prime_run_forces_divisibility_step
    (h_lw : RNS.Admissibility.ap_offsets_admissible_iff) :
    ap_prime_run_forces_divisibility := by
  unfold ap_prime_run_forces_divisibility
  intro a d k hka hall p hp hpk
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [hd0]
    exact dvd_zero p
  · exact (h_lw d k hdpos.ne').mp (ap_prime_run_admissible a d k hka hall) p hp hpk

/-! ## The two-way window (steps from the square-root shield) -/

private theorem window_aux (h_srs : RNS.SquareRootShield.square_root_shield)
    (cutoff n : Nat) (hlo : cutoff ≤ n) (hhi : n < cutoff * cutoff) :
    n.Prime ↔ ∀ q ∈ active_primes cutoff, ¬ q ∣ n := by
  constructor
  · intro hp q hq hdvd
    have hqp : q.Prime := by
      unfold active_primes at hq
      exact (Finset.mem_filter.mp hq).2
    have hqlt : q < cutoff := by
      unfold active_primes at hq
      exact Finset.mem_range.mp (Finset.mem_filter.mp hq).1
    rcases hp.eq_one_or_self_of_dvd q hdvd with h1 | hqn
    · exact hqp.one_lt.ne' h1
    · rw [hqn] at hqlt
      exact absurd hqlt (not_lt.mpr hlo)
  · intro hall
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with hsmall | hbig
      · exfalso
        have hn1 : n ≤ 1 := Nat.le_of_lt_succ hsmall
        have hc : cutoff ≤ 1 := le_trans hlo hn1
        have hsq : cutoff * cutoff ≤ cutoff * 1 := Nat.mul_le_mul (le_refl cutoff) hc
        rw [Nat.mul_one] at hsq
        have hself : n < n := lt_of_lt_of_le hhi (le_trans hsq hlo)
        exact absurd hself (lt_irrefl n)
      · exact hbig
    exact cover_aux h_srs n n (active_primes cutoff) hn2 le_rfl
      (active_cover_aux n cutoff hhi) (fun q hq _ => hall q hq)

theorem window_prime_iff_step (h_srs : RNS.SquareRootShield.square_root_shield) :
    window_prime_iff := by
  unfold window_prime_iff
  exact window_aux h_srs

theorem window_twin_iff_step (h_srs : RNS.SquareRootShield.square_root_shield) :
    window_twin_iff := by
  unfold window_twin_iff
  intro cutoff n hlo hhi
  exact and_congr
    (window_aux h_srs cutoff n hlo (lt_of_le_of_lt (Nat.le_add_right n 2) hhi))
    (window_aux h_srs cutoff (n + 2) (le_trans hlo (Nat.le_add_right n 2)) hhi)

/-! ## Backward runs (the divisibility claim is a step from `Admissibility`) -/

private theorem backward_hits_aux (top step count q : Nat) (hq : q.Prime)
    (hnd : ¬ q ∣ step) (hqk : q ≤ count) (hfit : (count - 1) * step ≤ top) :
    ∃ i ∈ Finset.range count, q ∣ top - i * step := by
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero q := ⟨hq.pos.ne'⟩
  have hdne : (step : ZMod q) ≠ 0 := fun h => hnd ((ZMod.natCast_eq_zero_iff step q).mp h)
  set y : ZMod q := (top : ZMod q) * (step : ZMod q)⁻¹ with hydef
  have hylt : y.val < count := lt_of_lt_of_le (ZMod.val_lt y) hqk
  have hle : y.val * step ≤ top := by
    have hi : y.val ≤ count - 1 := by omega
    exact le_trans (Nat.mul_le_mul hi (le_refl step)) hfit
  refine ⟨y.val, Finset.mem_range.mpr hylt, ?_⟩
  apply (ZMod.natCast_eq_zero_iff (top - y.val * step) q).mp
  rw [Nat.cast_sub hle]
  push_cast
  rw [ZMod.natCast_rightInverse y, hydef, mul_assoc, inv_mul_cancel₀ hdne, mul_one, sub_self]

private theorem backward_run_hits_aux (top step count q : Nat) (hq : q.Prime)
    (hnd : ¬ q ∣ step) (hqk : q ≤ count) (hfit : (count - 1) * step ≤ top)
    (hall : ∀ i ∈ Finset.range count, (top - i * step).Prime) :
    ∃ i ∈ Finset.range count, top - i * step = q := by
  obtain ⟨i, hi, hdvd⟩ := backward_hits_aux top step count q hq hnd hqk hfit
  refine ⟨i, hi, ?_⟩
  rcases (hall i hi).eq_one_or_self_of_dvd q hdvd with h1 | hself
  · exact absurd h1 hq.one_lt.ne'
  · exact hself.symm

private theorem backward_length_lt_aux (top step count q : Nat) (hq : q.Prime)
    (hnd : ¬ q ∣ step) (hfit : (count - 1) * step ≤ top)
    (hall : ∀ i ∈ Finset.range count, (top - i * step).Prime)
    (hnoq : ∀ i ∈ Finset.range count, top - i * step ≠ q) : count < q := by
  by_contra hkq
  have hqk : q ≤ count := not_lt.mp hkq
  obtain ⟨i, hi, heq⟩ := backward_run_hits_aux top step count q hq hnd hqk hfit hall
  exact hnoq i hi heq

private theorem backward_length_lt_of_above_aux (top step count q : Nat)
    (hq : q.Prime) (hnd : ¬ q ∣ step) (hbot : q < top - (count - 1) * step)
    (hall : ∀ i ∈ Finset.range count, (top - i * step).Prime) : count < q := by
  have hfit : (count - 1) * step ≤ top := by
    by_contra h
    have h0 : top - (count - 1) * step = 0 :=
      Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp h))
    rw [h0] at hbot
    exact Nat.not_lt_zero q hbot
  refine backward_length_lt_aux top step count q hq hnd hfit hall ?_
  intro i hi h
  have hi' : i ≤ count - 1 := by
    have := Finset.mem_range.mp hi
    omega
  have hmul : i * step ≤ (count - 1) * step := Nat.mul_le_mul hi' (le_refl step)
  generalize i * step = A at hmul h
  generalize (count - 1) * step = B at hmul hbot
  omega

theorem backward_ap_hits_wheel_holds : backward_ap_hits_wheel := by
  unfold backward_ap_hits_wheel
  exact backward_hits_aux

theorem backward_ap_prime_run_length_lt_of_above_holds :
    backward_ap_prime_run_length_lt_of_above := by
  unfold backward_ap_prime_run_length_lt_of_above
  exact backward_length_lt_of_above_aux

/-- **Lagrange–Waring for backward prime runs.** Read from its bottom term
upward, a backward run is a forward run, so the forward step applies. -/
theorem backward_ap_prime_run_forces_divisibility_step
    (h_lw : RNS.Admissibility.ap_offsets_admissible_iff) :
    backward_ap_prime_run_forces_divisibility := by
  have hfwd := ap_prime_run_forces_divisibility_step h_lw
  unfold ap_prime_run_forces_divisibility at hfwd
  unfold backward_ap_prime_run_forces_divisibility
  intro top step count hka hall p hp hpk
  refine hfwd (top - (count - 1) * step) step count hka ?_ p hp hpk
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  have hj' : j ≤ count - 1 := by omega
  have hsplit : (count - 1) * step = (count - 1 - j) * step + j * step := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hj']
  have hmem : count - 1 - j ∈ Finset.range count := Finset.mem_range.mpr (by omega)
  have hprime := hall (count - 1 - j) hmem
  have heq : top - (count - 1) * step + j * step = top - (count - 1 - j) * step := by
    generalize (count - 1) * step = B at hsplit hka ⊢
    generalize (count - 1 - j) * step = C at hsplit ⊢
    generalize j * step = D at hsplit ⊢
    omega
  rw [heq]
  exact hprime

end RNS.ShieldCertificates

#print axioms RNS.ShieldCertificates.prime_of_shield_cover_step
#print axioms RNS.ShieldCertificates.active_primes_cover_holds
#print axioms RNS.ShieldCertificates.family_prime_of_shield_cover_step
#print axioms RNS.ShieldCertificates.forward_ap_prime_of_active_shield_step
#print axioms RNS.ShieldCertificates.backward_ap_prime_of_active_shield_step
#print axioms RNS.ShieldCertificates.tuple_prime_of_active_shield_step
#print axioms RNS.ShieldCertificates.ap_hits_wheel_holds
#print axioms RNS.ShieldCertificates.ap_prime_run_length_lt_of_lt_start_holds
#print axioms RNS.ShieldCertificates.ap_prime_run_forces_divisibility_step
#print axioms RNS.ShieldCertificates.window_prime_iff_step
#print axioms RNS.ShieldCertificates.window_twin_iff_step
#print axioms RNS.ShieldCertificates.backward_ap_hits_wheel_holds
#print axioms RNS.ShieldCertificates.backward_ap_prime_run_length_lt_of_above_holds
#print axioms RNS.ShieldCertificates.backward_ap_prime_run_forces_divisibility_step
