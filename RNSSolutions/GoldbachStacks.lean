/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Data.Nat.Prime.Basic      -- `Nat.Prime.even_iff`, `Nat.Prime.odd_of_ne_two`
import Mathlib.Data.Nat.Prime.Infinite   -- `Nat.exists_infinite_primes`
import Mathlib.Data.Nat.Find             -- `Nat.findGreatest`
import Mathlib.Tactic.NormNum.Prime      -- `norm_num` proving small numbers prime
import RNSNetwork.Nodes.GoldbachStacks.Conclusions

/-!
# Proofs for GoldbachStacks

Status: draft (written 2026-11-23, first build pending).

Proves the four equivalences of `RNS.GoldbachStacks`. None rests on another
node. The frontier form uses the infinitude of primes (a stack at least as
tall as any target) and the tallest stack below it (`Nat.findGreatest`).
-/

namespace RNS.GoldbachStacks

theorem goldbach_iff_odd_goldbach_holds : goldbach_iff_odd_goldbach := by
  unfold goldbach_iff_odd_goldbach goldbach odd_goldbach
  constructor
  · intro hg n hn he
    obtain ⟨p, q, hp, hq, hpq⟩ := hg n (by omega) he
    obtain ⟨r, hr⟩ := he
    have hp2 : p ≠ 2 := by
      rintro rfl
      have hqe : Even q := ⟨r - 1, by omega⟩
      have := hq.even_iff.1 hqe
      omega
    have hq2 : q ≠ 2 := by
      rintro rfl
      have hpe : Even p := ⟨r - 1, by omega⟩
      have := hp.even_iff.1 hpe
      omega
    exact ⟨p, q, hp, hq, hp.odd_of_ne_two hp2, hq.odd_of_ne_two hq2, hpq⟩
  · intro ho n hn he
    by_cases h4 : n = 4
    · subst h4
      exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
    · have h6 : 6 ≤ n := by
        obtain ⟨r, hr⟩ := he
        omega
      obtain ⟨p, q, hp, hq, -, -, hpq⟩ := ho n h6 he
      exact ⟨p, q, hp, hq, hpq⟩

theorem no_gap_iff_odd_goldbach_holds : no_gap_iff_odd_goldbach := by
  unfold no_gap_iff_odd_goldbach no_gap odd_goldbach built is_stack
  constructor
  · intro hb n hn he
    obtain ⟨r, hr⟩ := he
    obtain ⟨a, b, ⟨-, ha⟩, ⟨-, hb'⟩, hab⟩ := hb (r - 1) (by omega)
    exact ⟨2 * a + 1, 2 * b + 1, ha, hb', ⟨a, rfl⟩, ⟨b, rfl⟩, by omega⟩
  · intro ho T hT
    obtain ⟨p, q, hp, hq, ⟨a, rfl⟩, ⟨b, rfl⟩, hpq⟩ :=
      ho (2 * T + 2) (by omega) ⟨T + 1, by omega⟩
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · subst h
        exact absurd hp (by norm_num)
      · exact h
    have hb : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · subst h
        exact absurd hq (by norm_num)
      · exact h
    exact ⟨a, b, ⟨ha, hp⟩, ⟨hb, hq⟩, by omega⟩

theorem frontier_ahead_iff_no_gap_holds : frontier_ahead_iff_no_gap := by
  classical
  unfold frontier_ahead_iff_no_gap frontier_ahead no_gap built
  constructor
  · intro hf T hT
    -- a stack at least as tall as the target
    obtain ⟨p, hpT, hp⟩ := Nat.exists_infinite_primes (2 * T + 3)
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    set h' := p / 2 with hh'
    have hs' : is_stack h' := by
      unfold is_stack
      refine ⟨by omega, ?_⟩
      rw [show 2 * h' + 1 = p by omega]
      exact hp
    have hTh' : T ≤ h' := by omega
    have h1 : is_stack 1 := by
      unfold is_stack
      norm_num
    -- the tallest stack below it
    set h := Nat.findGreatest is_stack (h' - 1) with hh
    have hs : is_stack h := Nat.findGreatest_spec (m := 1) (by omega) h1
    have hlt : h < h' := by
      have := Nat.findGreatest_le (P := is_stack) (h' - 1)
      omega
    have hgap : ∀ m, h < m → m < h' → ¬ is_stack m := fun m hm1 hm2 =>
      Nat.findGreatest_is_greatest hm1 (by omega)
    obtain ⟨a, b, ha, hb, -, -, hab⟩ := hf h h' hs hs' hlt hgap T hT hTh'
    exact ⟨a, b, ha, hb, hab⟩
  · intro hn h h' hs hs' hlt hgap T hT hTh'
    obtain ⟨a, b, ha, hb, hab⟩ := hn T hT
    have ha1 : 1 ≤ a := by
      unfold is_stack at ha
      exact ha.1
    have hb1 : 1 ≤ b := by
      unfold is_stack at hb
      exact hb.1
    have ha' : a ≤ h := by
      by_contra hc
      exact hgap a (by omega) (by omega) ha
    have hb' : b ≤ h := by
      by_contra hc
      exact hgap b (by omega) (by omega) hb
    exact ⟨a, b, ha, hb, ha', hb', hab⟩

theorem frontier_ahead_iff_goldbach_holds : frontier_ahead_iff_goldbach := by
  have h1 := frontier_ahead_iff_no_gap_holds
  have h2 := no_gap_iff_odd_goldbach_holds
  have h3 := goldbach_iff_odd_goldbach_holds
  unfold frontier_ahead_iff_no_gap at h1
  unfold no_gap_iff_odd_goldbach at h2
  unfold goldbach_iff_odd_goldbach at h3
  unfold frontier_ahead_iff_goldbach
  exact h1.trans (h2.trans h3.symm)

end RNS.GoldbachStacks

#print axioms RNS.GoldbachStacks.goldbach_iff_odd_goldbach_holds
#print axioms RNS.GoldbachStacks.no_gap_iff_odd_goldbach_holds
#print axioms RNS.GoldbachStacks.frontier_ahead_iff_no_gap_holds
#print axioms RNS.GoldbachStacks.frontier_ahead_iff_goldbach_holds
