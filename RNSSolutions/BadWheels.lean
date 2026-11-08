/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.BadWheels.Conclusions
import Mathlib

/-!
# Proofs for BadWheels

Imports claims only, never other nodes' proofs.

Idea. Work with divisibility by the wheel `p` in the integers. Two roots `r`
and `s` of one form give `p ∣ a·(r − s)`: either `p ∣ a`, and then `p ∣ b`
too, impossible when `a` and `b` share no factor, or `r` and `s` agree (both
are below `p`). A root exists when `p ∤ a`: take `−b/a` on the wheel. A common
root `r` of two forms gives `p ∣ a·(a'r + b') − a'·(ar + b) = a·b' − a'·b`;
conversely, when `p` divides that cross difference and not `a`, every root of
the first form is a root of the second. So the blocked positions are as many
as the forms exactly when no form loses its root and no two share one.
-/

namespace RNS.BadWheels

private theorem root_iff {a b p r : Nat} :
    (a * r + b) % p = 0 ↔ (p : ℤ) ∣ (a : ℤ) * r + b := by
  rw [← Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

private theorem blocked_eq_biUnion (L : Finset (Nat × Nat)) (p : Nat) :
    blocked L p = L.biUnion (fun ℓ => form_roots ℓ p) := by
  ext r
  simp only [blocked, form_roots, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hr, ℓ, hℓ, h⟩
    exact ⟨ℓ, hℓ, hr, h⟩
  · rintro ⟨ℓ, hℓ, hr, h⟩
    exact ⟨hr, ℓ, hℓ, h⟩

/-- A wheel dividing the leading coefficient of a primitive form blocks
nothing for it. -/
private theorem no_root_of_dvd {a b p r : Nat} (hp : p.Prime) (hcop : Nat.Coprime a b)
    (ha : (p : ℤ) ∣ a) (h : (p : ℤ) ∣ (a : ℤ) * r + b) : False := by
  have hb : (p : ℤ) ∣ b := by
    have := dvd_sub h (dvd_mul_of_dvd_left ha (r : ℤ))
    simpa using this
  have ha' : p ∣ a := by exact_mod_cast ha
  have hb' : p ∣ b := by exact_mod_cast hb
  have hg := Nat.dvd_gcd ha' hb'
  rw [Nat.Coprime.gcd_eq_one hcop] at hg
  exact hp.one_lt.ne' (Nat.dvd_one.mp hg)

private theorem roots_subsingleton {a b p r s : Nat} (hp : p.Prime) (hcop : Nat.Coprime a b)
    (hr : r < p) (hs : s < p) (h1 : (p : ℤ) ∣ (a : ℤ) * r + b)
    (h2 : (p : ℤ) ∣ (a : ℤ) * s + b) : r = s := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h3 : (p : ℤ) ∣ (a : ℤ) * ((r : ℤ) - s) := by
    have := dvd_sub h1 h2
    rwa [show (a : ℤ) * r + b - (a * s + b) = a * ((r : ℤ) - s) by ring] at this
  rcases hpZ.dvd_or_dvd h3 with ha | hrs
  · exact (no_root_of_dvd hp hcop ha h1).elim
  · have hmod : s ≡ r [MOD p] := Nat.modEq_iff_dvd.mpr hrs
    unfold Nat.ModEq at hmod
    rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hr] at hmod
    exact hmod.symm

private theorem roots_card_le_one {ℓ : Nat × Nat} {p : Nat} (hp : p.Prime)
    (hcop : Nat.Coprime ℓ.1 ℓ.2) : (form_roots ℓ p).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun r hr s hs => ?_
  simp only [form_roots, Finset.mem_filter, Finset.mem_range] at hr hs
  exact roots_subsingleton hp hcop hr.1 hs.1 (root_iff.mp hr.2) (root_iff.mp hs.2)

private theorem root_exists {a b p : Nat} (hp : p.Prime) (ha : ¬ (p : ℤ) ∣ a) :
    ∃ r < p, (p : ℤ) ∣ (a : ℤ) * r + b := by
  haveI := Fact.mk hp
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h
    apply ha
    rw [ZMod.natCast_eq_zero_iff] at h
    exact_mod_cast h
  refine ⟨((-(b : ZMod p)) * (a : ZMod p)⁻¹).val, ZMod.val_lt _, ?_⟩
  have key : ((a * ((-(b : ZMod p)) * (a : ZMod p)⁻¹).val + b : Nat) : ZMod p) = 0 := by
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    have hinv : (a : ZMod p) * (a : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ ha0
    linear_combination (-(b : ZMod p)) * hinv
  rw [ZMod.natCast_eq_zero_iff] at key
  exact_mod_cast key

private theorem roots_card_eq_one {ℓ : Nat × Nat} {p : Nat} (hp : p.Prime)
    (hcop : Nat.Coprime ℓ.1 ℓ.2) (ha : ¬ (p : ℤ) ∣ ℓ.1) : (form_roots ℓ p).card = 1 := by
  obtain ⟨r, hr, hroot⟩ := root_exists (b := ℓ.2) hp ha
  have hpos : 0 < (form_roots ℓ p).card := Finset.card_pos.mpr
    ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, root_iff.mpr hroot⟩⟩
  have := roots_card_le_one hp hcop
  omega

private theorem cross_of_common {a b a' b' p r : Nat} (h1 : (p : ℤ) ∣ (a : ℤ) * r + b)
    (h2 : (p : ℤ) ∣ (a' : ℤ) * r + b') : (p : ℤ) ∣ (a : ℤ) * b' - (a' : ℤ) * b := by
  have := dvd_sub (dvd_mul_of_dvd_right h2 (a : ℤ)) (dvd_mul_of_dvd_right h1 (a' : ℤ))
  rwa [show (a : ℤ) * (a' * r + b') - a' * (a * r + b) = a * b' - a' * b by ring] at this

private theorem root_transfer {a b a' b' p r : Nat} (hpZ : Prime (p : ℤ)) (ha : ¬ (p : ℤ) ∣ a)
    (hc : (p : ℤ) ∣ (a : ℤ) * b' - (a' : ℤ) * b) (h1 : (p : ℤ) ∣ (a : ℤ) * r + b) :
    (p : ℤ) ∣ (a' : ℤ) * r + b' := by
  have h : (p : ℤ) ∣ (a : ℤ) * ((a' : ℤ) * r + b') := by
    have := dvd_add (dvd_mul_of_dvd_right h1 (a' : ℤ)) hc
    rwa [show (a' : ℤ) * (a * r + b) + (a * b' - a' * b) = a * (a' * r + b') by ring] at this
  exact (hpZ.dvd_or_dvd h).resolve_left ha

theorem blocked_le_card_holds : blocked_le_card := by
  intro L p hp hcop
  rw [blocked_eq_biUnion]
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ ℓ ∈ L, (form_roots ℓ p).card ≤ ∑ ℓ ∈ L, 1 :=
        Finset.sum_le_sum (fun ℓ hℓ => roots_card_le_one hp (hcop ℓ hℓ))
    _ = L.card := by simp

theorem blocked_eq_card_iff_holds : blocked_eq_card_iff := by
  intro L p hp hcop
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [blocked_eq_biUnion]
  constructor
  · intro hcard hdvd
    obtain ⟨ℓ, hℓ, hsub⟩ : ∃ ℓ ∈ L,
        form_roots ℓ p ⊆ (L.erase ℓ).biUnion (fun m => form_roots m p) := by
      unfold bad_product at hdvd
      rcases hpZ.dvd_or_dvd hdvd with h | h
      · obtain ⟨ℓ, hℓ, ha⟩ := hpZ.exists_mem_finset_dvd h
        refine ⟨ℓ, hℓ, fun r hr => ?_⟩
        simp only [form_roots, Finset.mem_filter, Finset.mem_range] at hr
        exact (no_root_of_dvd hp (hcop ℓ hℓ) ha (root_iff.mp hr.2)).elim
      · obtain ⟨e, he, hc⟩ := hpZ.exists_mem_finset_dvd h
        obtain ⟨he1, he2, hne⟩ := Finset.mem_offDiag.mp he
        refine ⟨e.1, he1, fun r hr => ?_⟩
        simp only [form_roots, Finset.mem_filter, Finset.mem_range] at hr
        by_cases ha : (p : ℤ) ∣ (e.1.1 : ℤ)
        · exact (no_root_of_dvd hp (hcop e.1 he1) ha (root_iff.mp hr.2)).elim
        · refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_erase.mpr ⟨hne.symm, he2⟩, ?_⟩
          simp only [form_roots, Finset.mem_filter, Finset.mem_range]
          exact ⟨hr.1, root_iff.mpr (root_transfer hpZ ha
            (show (p : ℤ) ∣ (e.1.1 : ℤ) * e.2.2 - (e.2.1 : ℤ) * e.1.2 from hc) (root_iff.mp hr.2))⟩
    have hU : L.biUnion (fun m => form_roots m p) =
        (L.erase ℓ).biUnion (fun m => form_roots m p) := by
      conv_lhs => rw [← Finset.insert_erase hℓ]
      rw [Finset.biUnion_insert]
      ext r
      constructor
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · exact hsub h
        · exact h
      · intro h
        exact Finset.mem_union_right _ h
    have hle : ((L.erase ℓ).biUnion (fun m => form_roots m p)).card ≤ (L.erase ℓ).card := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ m ∈ L.erase ℓ, (form_roots m p).card ≤ ∑ m ∈ L.erase ℓ, 1 :=
            Finset.sum_le_sum (fun m hm => roots_card_le_one hp (hcop m (Finset.mem_of_mem_erase hm)))
        _ = (L.erase ℓ).card := by simp
    rw [hU] at hcard
    have herase := Finset.card_erase_of_mem hℓ
    have hpos : 0 < L.card := Finset.card_pos.mpr ⟨ℓ, hℓ⟩
    omega
  · intro hndvd
    have hna : ∀ ℓ ∈ L, ¬ (p : ℤ) ∣ (ℓ.1 : ℤ) := by
      intro ℓ hℓ h
      apply hndvd
      unfold bad_product
      exact dvd_mul_of_dvd_left (dvd_trans h (Finset.dvd_prod_of_mem (fun m => (m.1 : ℤ)) hℓ)) _
    have hnc : ∀ ℓ ∈ L, ∀ ℓ' ∈ L, ℓ ≠ ℓ' → ¬ (p : ℤ) ∣ cross ℓ ℓ' := by
      intro ℓ hℓ ℓ' hℓ' hne h
      apply hndvd
      unfold bad_product
      exact dvd_mul_of_dvd_right (dvd_trans h (Finset.dvd_prod_of_mem (fun e => cross e.1 e.2)
        (Finset.mem_offDiag.mpr ⟨hℓ, hℓ', hne⟩))) _
    rw [Finset.card_biUnion]
    · calc ∑ ℓ ∈ L, (form_roots ℓ p).card = ∑ ℓ ∈ L, 1 :=
            Finset.sum_congr rfl (fun ℓ hℓ => roots_card_eq_one hp (hcop ℓ hℓ) (hna ℓ hℓ))
        _ = L.card := by simp
    · intro ℓ hℓ ℓ' hℓ' hne
      show Disjoint (form_roots ℓ p) (form_roots ℓ' p)
      rw [Finset.disjoint_left]
      intro r hr hr'
      simp only [form_roots, Finset.mem_filter, Finset.mem_range] at hr hr'
      exact hnc ℓ (Finset.mem_coe.mp hℓ) ℓ' (Finset.mem_coe.mp hℓ') hne
        (cross_of_common (root_iff.mp hr.2) (root_iff.mp hr'.2))

theorem twin_columns_bad_wheels_holds : twin_columns_bad_wheels := by
  intro p hp
  have hcop : ∀ ℓ ∈ ({(6, 5), (6, 7)} : Finset (Nat × Nat)), Nat.Coprime ℓ.1 ℓ.2 := by decide
  have hE : bad_product {(6, 5), (6, 7)} = -5184 := by
    first | decide | rfl | norm_num [bad_product, cross, Finset.offDiag]
  have hcardL : ({(6, 5), (6, 7)} : Finset (Nat × Nat)).card = 2 := by decide
  have hle := blocked_le_card_holds _ p hp hcop
  have hiff := blocked_eq_card_iff_holds _ p hp hcop
  rw [hE, hcardL] at hiff
  rw [hcardL] at hle
  have hdiv : (p : ℤ) ∣ -5184 ↔ p = 2 ∨ p = 3 := by
    rw [dvd_neg, show (5184 : ℤ) = ((5184 : Nat) : ℤ) by norm_num, Int.natCast_dvd_natCast]
    constructor
    · intro h
      rw [show (5184 : Nat) = 2 ^ 6 * 3 ^ 4 by norm_num] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
      · left
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
      · right
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)
    · rintro (rfl | rfl) <;> norm_num
  constructor
  · intro hlt
    apply hdiv.mp
    by_contra hn
    have := hiff.mpr hn
    omega
  · intro h23
    have hd := hdiv.mpr h23
    have hne : (blocked {(6, 5), (6, 7)} p).card ≠ 2 := fun h => hiff.mp h hd
    omega

theorem divisors_pairwise_coprime_holds : divisors_pairwise_coprime := by
  intro L n d hd hcopE ℓ hℓ ℓ' hℓ' hne
  apply Nat.coprime_of_dvd
  intro q hq hq1 hq2
  have h1 : (q : ℤ) ∣ (ℓ.1 : ℤ) * n + ℓ.2 := by
    have := dvd_trans hq1 (hd ℓ hℓ); exact_mod_cast this
  have h2 : (q : ℤ) ∣ (ℓ'.1 : ℤ) * n + ℓ'.2 := by
    have := dvd_trans hq2 (hd ℓ' hℓ'); exact_mod_cast this
  have hc : (q : ℤ) ∣ cross ℓ ℓ' := cross_of_common h1 h2
  have hE : (q : ℤ) ∣ bad_product L := by
    unfold bad_product
    exact dvd_mul_of_dvd_right (dvd_trans hc (Finset.dvd_prod_of_mem (fun e => cross e.1 e.2)
      (Finset.mem_offDiag.mpr ⟨hℓ, hℓ', hne⟩))) _
  have hE' : q ∣ (bad_product L).natAbs := Int.natCast_dvd.mp hE
  have hg := Nat.dvd_gcd hq1 hE'
  rw [Nat.Coprime.gcd_eq_one (hcopE ℓ hℓ)] at hg
  exact hq.one_lt.ne' (Nat.dvd_one.mp hg)

#print axioms RNS.BadWheels.blocked_le_card_holds
#print axioms RNS.BadWheels.blocked_eq_card_iff_holds
#print axioms RNS.BadWheels.twin_columns_bad_wheels_holds
#print axioms RNS.BadWheels.divisors_pairwise_coprime_holds

end RNS.BadWheels
