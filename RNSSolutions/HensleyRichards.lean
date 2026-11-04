/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.HensleyRichards.Conclusions

/-!
# Proof for HensleyRichards

Rests on no other node. Tactic proofs are copied from
`rns_sieve_6_parts_J_K.lean`, Part J (reported clean by `#print axioms`).

Idea: Conjecture A, applied to the dense pattern, gives a starting number
past 3 at which every offset lands on a prime; those primes all sit in a
window of the given length, so the prime count across the window exceeds the
count up to the window length, contradicting Conjecture B.
-/

namespace RNS.HensleyRichards

private theorem primeCounting_add_ge_of_primes_in_window
    (x y : Nat) (S : Finset Nat)
    (hS : ∀ p ∈ S, p.Prime ∧ x < p ∧ p ≤ x + y) :
    Nat.primeCounting x + S.card ≤ Nat.primeCounting (x + y) := by
  have hmono : Nat.primesLE x ⊆ Nat.primesLE (x + y) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (Nat.le_add_right x y), hp.2⟩
  have hSsub : S ⊆ Nat.primesLE (x + y) \ Nat.primesLE x := by
    intro p hp
    have h := hS p hp
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
    refine ⟨⟨h.2.2, h.1⟩, ?_⟩
    rintro ⟨hle, -⟩
    omega
  have hcard_le : S.card ≤ (Nat.primesLE (x + y) \ Nat.primesLE x).card :=
    Finset.card_le_card hSsub
  rw [Finset.card_sdiff] at hcard_le
  have hinter : Nat.primesLE x ∩ Nat.primesLE (x + y) = Nat.primesLE x := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_inter]
    exact ⟨fun h => h.1, fun h => ⟨h, hmono h⟩⟩
  rw [hinter] at hcard_le
  have hmono_pc : Nat.primeCounting x ≤ Nat.primeCounting (x + y) :=
    Nat.monotone_primeCounting (Nat.le_add_right x y)
  rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hcard_le
  omega

theorem HL_A_and_B_incompatible_holds : HL_A_and_B_incompatible := by
  unfold HL_A_and_B_incompatible
  intro T y hTne hTadm hTwin hy2 hTcount
  rintro ⟨hA, hB⟩
  obtain ⟨n, hnS, hn3⟩ :=
    (hA T hTne hTadm).exists_notMem_finset (Finset.range 3)
  have hn3' : 3 ≤ n := by simpa [Finset.mem_range] using hn3
  have hnS' : ∀ t ∈ T, (n + t).Prime := hnS
  set x := n - 1 with hx_def
  have hx2 : 2 ≤ x := by omega
  set S : Finset Nat := T.image (fun t => n + t) with hS_def
  have hinj : Function.Injective (fun t : Nat => n + t) := by
    intro a b hab
    simp only at hab
    omega
  have hS_card : S.card = T.card := by
    rw [hS_def]; exact Finset.card_image_of_injective T hinj
  have hS_spec : ∀ p ∈ S, p.Prime ∧ x < p ∧ p ≤ x + y := by
    intro p hp
    rw [hS_def, Finset.mem_image] at hp
    obtain ⟨t, htT, hteq⟩ := hp
    have hteq' : n + t = p := hteq
    have htlt : t < y := hTwin t htT
    have hpprime : p.Prime := by rw [← hteq']; exact hnS' t htT
    refine ⟨hpprime, ?_, ?_⟩ <;> omega
  have hge := primeCounting_add_ge_of_primes_in_window x y S hS_spec
  rw [hS_card] at hge
  have hble := hB x y hx2 hy2
  omega

end RNS.HensleyRichards

#print axioms RNS.HensleyRichards.HL_A_and_B_incompatible_holds
