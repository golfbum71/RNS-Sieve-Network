/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Data.Nat.Prime.Basic      -- `Nat.Prime.even_iff`, `Nat.Prime.odd_of_ne_two`
import Mathlib.Data.Nat.Prime.Infinite   -- `Nat.exists_infinite_primes`
import Mathlib.Data.Nat.Find             -- `Nat.findGreatest`
import Mathlib.Tactic.NormNum.Prime      -- `norm_num` proving small numbers prime
import Mathlib.Algebra.Field.ZMod        -- remainders modulo a prime form a field
import Mathlib.Data.Finset.Card          -- `Finset.exists_mem_notMem_of_card_lt_card`
import RNSNetwork.Nodes.GoldbachStacks.Conclusions
import RNSNetwork.Nodes.CRT.Conclusions   -- `crt_map_bijective`, taken as a hypothesis

/-!
# Proofs for GoldbachStacks

Status: built clean on GitHub, standard axioms only (2026-11-23).

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

/-! ## The wheels never force a gap (added 2026-11-23, built clean, standard axioms) -/

namespace RNS.GoldbachStacks

theorem stack_mod_three_holds : stack_mod_three := by
  unfold stack_mod_three is_stack
  intro h ⟨_, hp⟩ h2 h1
  have h3 : 3 ∣ 2 * h + 1 := by omega
  rcases hp.eq_one_or_self_of_dvd 3 h3 with h' | h'
  · omega
  · omega

theorem wheel_no_gap_holds : wheel_no_gap := by
  unfold wheel_no_gap
  intro q hq r
  by_cases hq2 : q = 2
  · subst hq2
    revert r
    decide
  · classical
    have : Fact q.Prime := ⟨hq⟩
    have : NeZero q := ⟨hq.ne_zero⟩
    have h3 : 3 ≤ q := by
      have := hq.two_le
      omega
    have h2 : (2 : ZMod q) ≠ 0 := by
      intro h
      have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at h'
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h')
    -- the one height whose stack the wheel of size `q` removes
    set c : ZMod q := -(2 : ZMod q)⁻¹ with hc
    have hbad : ∀ x : ZMod q, 2 * x + 1 = 0 → x = c := by
      intro x hx
      calc x = (2 : ZMod q)⁻¹ * (2 * x) := by
              rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
        _ = (2 : ZMod q)⁻¹ * (2 * x + 1) - (2 : ZMod q)⁻¹ := by ring
        _ = c := by rw [hx, hc]; ring
    -- at most two heights are bad for the pair, and the wheel has at least three
    have hcard : ({c, r - c} : Finset (ZMod q)).card < (Finset.univ : Finset (ZMod q)).card := by
      rw [Finset.card_univ, ZMod.card]
      have := Finset.card_insert_le c ({r - c} : Finset (ZMod q))
      rw [Finset.card_singleton] at this
      omega
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨a, r - a, ?_, ?_, by ring⟩
    · intro h
      exact ha (by rw [hbad a h]; simp)
    · intro h
      have hra := hbad (r - a) h
      exact ha (by rw [show a = r - c by rw [← hra]; ring]; simp)

end RNS.GoldbachStacks

#print axioms RNS.GoldbachStacks.stack_mod_three_holds
#print axioms RNS.GoldbachStacks.wheel_no_gap_holds

/-! ## All the wheels of a cycle at once (added 2026-11-23, built clean, standard axioms)

Rests on `CRT`: its claim that the combined cycle matches the individual
wheels exactly is taken as the hypothesis `hcrt`. -/

namespace RNS.GoldbachStacks

theorem wheels_no_gap_step (hcrt : RNS.CRT.crt_map_bijective) : wheels_no_gap := by
  unfold wheels_no_gap
  intro limit r
  have hw := wheel_no_gap_holds
  unfold wheel_no_gap at hw
  have hq : ∀ q : active_primes limit, (q : ℕ).Prime := by
    intro q
    have h := q.2
    unfold active_primes at h
    exact (Finset.mem_filter.mp h).2
  -- a good pair on each wheel separately
  choose f g hf using fun q : active_primes limit => hw q (hq q) (crt_map limit r q)
  -- one position of the combined cycle with the chosen first height on every wheel
  obtain ⟨a, ha⟩ := (hcrt limit).2 f
  refine ⟨a, r - a, fun q => ⟨?_, ?_⟩, by ring⟩
  · rw [ha]
    exact (hf q).1
  · have hsub : crt_map limit (r - a) q = crt_map limit r q - crt_map limit a q := by
      simp only [crt_map, map_sub]
    have hg : crt_map limit r q - f q = g q := by
      rw [← (hf q).2.2]
      ring
    rw [hsub, ha, hg]
    exact (hf q).2.1

end RNS.GoldbachStacks

#print axioms RNS.GoldbachStacks.wheels_no_gap_step

/-! ## The open part, stated exactly (added 2026-11-23, built clean, standard axioms)

Only the equivalences are proved; `window_no_gap` itself is open. -/

namespace RNS.GoldbachStacks

theorem window_no_gap_iff_no_gap_holds : window_no_gap_iff_no_gap := by
  unfold window_no_gap_iff_no_gap window_no_gap no_gap built is_stack
  constructor
  · intro hw T hT
    obtain ⟨a, b, ha, hb, hab, hp⟩ := hw T hT
    -- surviving every wheel up to the square root makes the stack a prime
    have key : ∀ x, 1 ≤ x → x ≤ T →
        (∀ p, p.Prime → p * p ≤ 2 * T + 1 → p ∣ 2 * x + 1 → p = 2 * x + 1) →
        (2 * x + 1).Prime := by
      intro x hx hxT hx'
      by_contra hnp
      have hsq := Nat.minFac_sq_le_self (by omega : 0 < 2 * x + 1) hnp
      have hmp := Nat.minFac_prime (by omega : 2 * x + 1 ≠ 1)
      have hle : Nat.minFac (2 * x + 1) * Nat.minFac (2 * x + 1) ≤ 2 * T + 1 :=
        calc Nat.minFac (2 * x + 1) * Nat.minFac (2 * x + 1)
            = Nat.minFac (2 * x + 1) ^ 2 := (pow_two _).symm
          _ ≤ 2 * x + 1 := hsq
          _ ≤ 2 * T + 1 := by omega
      have heq := hx' _ hmp hle (Nat.minFac_dvd _)
      rw [heq] at hmp
      exact hnp hmp
    exact ⟨a, b,
      ⟨ha, key a ha (by omega) fun p hp1 hp2 hd => (hp p hp1 hp2).1 hd⟩,
      ⟨hb, key b hb (by omega) fun p hp1 hp2 hd => (hp p hp1 hp2).2 hd⟩, hab⟩
  · intro hn T hT
    obtain ⟨a, b, ⟨ha, hpa⟩, ⟨hb, hpb⟩, hab⟩ := hn T hT
    refine ⟨a, b, ha, hb, hab, fun p hp _ => ⟨fun hd => ?_, fun hd => ?_⟩⟩
    · rcases hpa.eq_one_or_self_of_dvd p hd with h | h
      · exact absurd h hp.one_lt.ne'
      · exact h
    · rcases hpb.eq_one_or_self_of_dvd p hd with h | h
      · exact absurd h hp.one_lt.ne'
      · exact h

theorem window_no_gap_iff_goldbach_holds : window_no_gap_iff_goldbach := by
  have h1 := window_no_gap_iff_no_gap_holds
  have h2 := no_gap_iff_odd_goldbach_holds
  have h3 := goldbach_iff_odd_goldbach_holds
  unfold window_no_gap_iff_no_gap at h1
  unfold no_gap_iff_odd_goldbach at h2
  unfold goldbach_iff_odd_goldbach at h3
  unfold window_no_gap_iff_goldbach
  exact h1.trans (h2.trans h3.symm)

end RNS.GoldbachStacks

#print axioms RNS.GoldbachStacks.window_no_gap_iff_no_gap_holds
#print axioms RNS.GoldbachStacks.window_no_gap_iff_goldbach_holds
