/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BuchstabIdentity.Conclusions
import Mathlib

/-!
# Proofs for BuchstabIdentity

Imports claims only, never other nodes' proofs. Rests on no other node.

Idea. Legendre's recurrence: split the survivors of the old wheels by whether
the new prime divides them. Those it does not divide are the survivors of all
the wheels. Those it divides are the new prime times a number up to the bound
divided by the prime; that number survives the old wheels, because a prime
wheel dividing the product divides one of the two factors and is not the new
prime. Dividing by the new prime and multiplying back is the bijection.

Buchstab's identity and the product form: add the new wheels one at a time,
largest last, using the recurrence (or the product rule) at each step.
-/

namespace RNS.BuchstabIdentity

private theorem filter_insert_max {E : Finset Nat} {a : Nat} (hlt : ∀ x ∈ E, x < a) :
    (insert a E).filter (fun r => r < a) = E := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hx | hx, hxa⟩
    · subst hx; exact absurd hxa (lt_irrefl _)
    · exact hx
  · intro hx
    exact ⟨Or.inr hx, hlt x hx⟩

private theorem filter_insert_lt {E : Finset Nat} {a q : Nat} (hlt : ∀ x ∈ E, x < a)
    (hq : q ∈ E) : (insert a E).filter (fun r => r < q) = E.filter (fun r => r < q) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hx | hx, hxq⟩
    · subst hx; exact absurd (lt_trans hxq (hlt q hq)) (lt_irrefl _)
    · exact ⟨hx, hxq⟩
  · rintro ⟨hx, hxq⟩
    exact ⟨Or.inr hx, hxq⟩

theorem legendre_phi_recurrence_holds : legendre_phi_recurrence := by
  intro W q N hW hq hqW
  have hq0 : 0 < q := hq.pos
  have hsplit : ((survivors_upto W N).filter (fun k => q ∣ k)).card +
      ((survivors_upto W N).filter (fun k => ¬ q ∣ k)).card = (survivors_upto W N).card :=
    Finset.card_filter_add_card_filter_not _
  have h1 : (survivors_upto W N).filter (fun k => ¬ q ∣ k) = survivors_upto (insert q W) N := by
    ext k
    simp only [survivors_upto, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
      forall_eq_or_imp]
    tauto
  have h2 : ((survivors_upto W N).filter (fun k => q ∣ k)).card =
      (survivors_upto W (N / q)).card := by
    apply Finset.card_nbij' (fun k => k / q) (fun j => q * j)
    · intro k hk
      simp only [Finset.mem_coe, survivors_upto, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      obtain ⟨⟨⟨h1k, hkN⟩, hsurv⟩, hqk⟩ := hk
      obtain ⟨j, rfl⟩ := hqk
      rw [Nat.mul_div_cancel_left j hq0]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj; simp at h1k
        · exact hj
      · exact (Nat.le_div_iff_mul_le hq0).mpr (by rw [mul_comm]; exact hkN)
      · intro r hr hrj
        exact hsurv r hr (Dvd.dvd.mul_left hrj q)
    · intro j hj
      simp only [Finset.mem_coe, survivors_upto, Finset.mem_filter, Finset.mem_Icc] at hj ⊢
      obtain ⟨⟨hj1, hjN⟩, hsurv⟩ := hj
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right q j⟩
      · have := Nat.mul_pos hq0 hj1
        omega
      · have := (Nat.le_div_iff_mul_le hq0).mp hjN
        rw [mul_comm]; exact this
      · intro r hr hrd
        rcases (Nat.Prime.dvd_mul (hW r hr)).mp hrd with h | h
        · have hrq : r = q := (Nat.prime_dvd_prime_iff_eq (hW r hr) hq).mp h
          subst hrq
          exact hqW hr
        · exact hsurv r hr h
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter] at hk
      show q * (k / q) = k
      exact Nat.mul_div_cancel' hk.2
    · intro j _
      show q * j / q = j
      exact Nat.mul_div_cancel_left j hq0
  rw [← h1, ← h2]
  omega

theorem buchstab_identity_holds : buchstab_identity := by
  intro W E N hW hE hWE
  induction E using Finset.induction_on_max with
  | empty => simp
  | insert a E hlt ih =>
    have hE' : ∀ r ∈ E, r.Prime := fun r hr => hE r (Finset.mem_insert_of_mem hr)
    have hWE' : Disjoint W E := Finset.disjoint_of_subset_right (Finset.subset_insert a E) hWE
    have haE : a ∉ E := fun h => lt_irrefl a (hlt a h)
    have haW : a ∉ W := fun h => Finset.disjoint_left.mp hWE h (Finset.mem_insert_self a E)
    have ha : a.Prime := hE a (Finset.mem_insert_self a E)
    have hWEp : ∀ r ∈ W ∪ E, r.Prime := fun r hr =>
      (Finset.mem_union.mp hr).elim (hW r) (hE' r)
    have haWE : a ∉ W ∪ E := fun h => (Finset.mem_union.mp h).elim haW haE
    have hrec := legendre_phi_recurrence_holds (W ∪ E) a N hWEp ha haWE
    have h3 : ((survivors_upto (insert a (W ∪ E)) N).card : ℤ) +
        ((survivors_upto (W ∪ E) (N / a)).card : ℤ) = ((survivors_upto (W ∪ E) N).card : ℤ) := by
      exact_mod_cast hrec
    have hsum : ∑ q ∈ E, ((survivors_upto (W ∪ (insert a E).filter (fun r => r < q)) (N / q)).card : ℤ)
        = ∑ q ∈ E, ((survivors_upto (W ∪ E.filter (fun r => r < q)) (N / q)).card : ℤ) :=
      Finset.sum_congr rfl (fun q hq => by rw [filter_insert_lt hlt hq])
    rw [Finset.union_insert, Finset.sum_insert haE, filter_insert_max hlt, hsum]
    have ih' := ih hE' hWE'
    linarith

theorem buchstab_product_identity_holds : buchstab_product_identity := by
  intro E x
  induction E using Finset.induction_on_max with
  | empty => simp
  | insert a E hlt ih =>
    have haE : a ∉ E := fun h => lt_irrefl a (hlt a h)
    have hsum : ∑ q ∈ E, x q * ∏ r ∈ (insert a E).filter (fun r => r < q), (1 - x r)
        = ∑ q ∈ E, x q * ∏ r ∈ E.filter (fun r => r < q), (1 - x r) :=
      Finset.sum_congr rfl (fun q hq => by rw [filter_insert_lt hlt hq])
    rw [Finset.prod_insert haE, Finset.sum_insert haE, filter_insert_max hlt, hsum]
    have hs : ∑ q ∈ E, x q * ∏ r ∈ E.filter (fun r => r < q), (1 - x r) =
        1 - ∏ q ∈ E, (1 - x q) := by linarith
    rw [hs]
    ring

#print axioms RNS.BuchstabIdentity.legendre_phi_recurrence_holds
#print axioms RNS.BuchstabIdentity.buchstab_identity_holds
#print axioms RNS.BuchstabIdentity.buchstab_product_identity_holds

end RNS.BuchstabIdentity
