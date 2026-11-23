/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.TeamShift.Conclusions
import Mathlib.Tactic

/-!
# Proofs for TeamShift

Draft (2026-11-23).

Take the team's lonely time `k₀ / m₀` and the new denominator `|q| * m₀`. The
numerator `k₀ * |q| + j * m₀` keeps every team runner at `|q|` times its old
remainder, so its distance from the start in laps is unchanged. For the extra
runner, Bézout's identity for `u` and `q` reaches every spot `x + c * s`
(`x = u * k₀ * |q|`, `s = gcd(u, q) * m₀`), and these spots are evenly spaced,
at least two of them round the lap (`spaced_quarter`); the first one past a
quarter of a lap is also short of three quarters.
-/

namespace RNS.TeamShift

open RNS.PileUpLock

/-- Evenly spaced spots, at least two to a lap of length `E * s`, starting below
the spacing `s`: one of them lies between a quarter and three quarters of the lap. -/
theorem spaced_quarter (p0 s E : ℤ) (hs : 0 < s) (h0 : 0 ≤ p0) (h1 : p0 < s) (hE : 2 ≤ E) :
    ∃ c : ℕ, 0 ≤ p0 + c * s ∧ p0 + c * s < E * s ∧ E * s ≤ 4 * (p0 + c * s) ∧
      E * s ≤ 4 * (E * s - (p0 + c * s)) := by
  classical
  have hEs : 2 * s ≤ E * s := by nlinarith
  have hex : ∃ c : ℕ, E * s ≤ 4 * (p0 + (c : ℤ) * s) := by
    refine ⟨E.toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    nlinarith
  obtain ⟨c, hc, hmin⟩ : ∃ c : ℕ, E * s ≤ 4 * (p0 + (c : ℤ) * s) ∧
      ∀ c' : ℕ, c' < c → ¬ E * s ≤ 4 * (p0 + (c' : ℤ) * s) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun c' h => Nat.find_min hex h⟩
  refine ⟨c, ?_⟩
  cases c with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, add_zero] at hc ⊢
    refine ⟨h0, by linarith, hc, by linarith⟩
  | succ c' =>
    have hlt := not_le.mp (hmin c' (Nat.lt_succ_self c'))
    have e : ((c' + 1 : ℕ) : ℤ) * s = (c' : ℤ) * s + s := by push_cast; ring
    rw [e] at hc ⊢
    have hc's : 0 ≤ (c' : ℤ) * s := mul_nonneg (by positivity) hs.le
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem team_shift_holds : team_shift := by
  intro T u q hcard hu hq hqu hT
  obtain ⟨m0, k0, hm0, hfar⟩ := hT
  -- q is not 0: the team has two different speeds
  have hq0 : q ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
    have h1 := hq a ha
    have h2 := hq b hb
    rw [zero_dvd_iff] at h1 h2
    exact hab (h1.trans h2.symm)
  have hQ : 0 < |q| := abs_pos.mpr hq0
  have hm0' : (0 : ℤ) < m0 := by exact_mod_cast hm0
  -- the greatest common factor of u and q, and the number of spots
  set D : ℤ := (Int.gcd u q : ℤ) with hD
  have hDu : D ∣ u := Int.gcd_dvd_left u q
  obtain ⟨e, he⟩ : D ∣ q := Int.gcd_dvd_right u q
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  have hD0 : D ≠ 0 := by
    rintro h
    rw [h, zero_mul] at he
    exact hq0 he
  have hDpos : 0 < D := lt_of_le_of_ne hDnn (Ne.symm hD0)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [mul_zero] at he
    exact hq0 he
  set E : ℤ := |e| with hE
  have hE2 : 2 ≤ E := by
    have h0 : 0 < |e| := abs_pos.mpr he0
    by_contra hlt
    have hE_eq : |e| = 1 := by omega
    apply hqu
    rcases (abs_eq zero_le_one).mp hE_eq with h | h
    · rw [he, h, mul_one]; exact hDu
    · rw [he, h, mul_neg_one]; exact neg_dvd.mpr hDu
  have habs : |q| = D * E := by rw [he, abs_mul, abs_of_nonneg hDnn]
  obtain ⟨σ, hσ⟩ := abs_dvd_self q
  have hbez : D = u * Int.gcdA u q + q * Int.gcdB u q := Int.gcd_eq_gcd_ab u q
  -- the extra runner's spots
  set s : ℤ := D * m0 with hs
  have hspos : 0 < s := mul_pos hDpos hm0'
  set x : ℤ := u * k0 * |q| with hx
  have hxdiv := Int.emod_add_ediv_mul x s
  obtain ⟨c1, hP0, hP1, hP2, hP3⟩ := spaced_quarter (x % s) s E hspos
    (Int.emod_nonneg x (ne_of_gt hspos)) (Int.emod_lt_of_pos x hspos) hE2
  set c : ℤ := (c1 : ℤ) - x / s with hc
  set j : ℤ := Int.gcdA u q * c with hj
  set M : ℤ := |q| * (m0 : ℤ) with hM
  have hMs : M = E * s := by rw [hM, habs, hs]; ring
  have hMpos : 0 < M := mul_pos hQ hm0'
  refine ⟨q.natAbs * m0, k0 * |q| + j * m0, Nat.mul_pos (Int.natAbs_pos.mpr hq0) hm0, ?_⟩
  have hcast : ((q.natAbs * m0 : ℕ) : ℤ) = M := by
    rw [hM, Nat.cast_mul, Int.natCast_natAbs]
  have hn : ((insert u T).card : ℤ) + 1 = (T.card : ℤ) + 2 := by
    rw [Finset.card_insert_of_notMem hu]; push_cast; ring
  have hT2 : (2 : ℤ) ≤ T.card := by exact_mod_cast hcard
  intro v hv
  unfold far
  rw [hcast]
  push_cast
  rw [hn]
  rcases Finset.mem_insert.mp hv with heq | hvT
  · -- the extra runner lands on the chosen spot
    rw [heq]
    have hsplit : u * (k0 * |q| + j * m0) =
        ((x % s) + (c1 : ℤ) * s) + M * (-(σ * Int.gcdB u q * c)) := by
      have hqσ : q = |q| * σ := hσ
      have key : u * j * m0 = c * s - c * q * Int.gcdB u q * m0 := by
        rw [hj, hs]
        calc u * (Int.gcdA u q * c) * m0
            = c * (u * Int.gcdA u q + q * Int.gcdB u q) * m0 - c * q * Int.gcdB u q * m0 := by ring
          _ = c * (D * m0) - c * q * Int.gcdB u q * m0 := by rw [← hbez]; ring
      calc u * (k0 * |q| + j * m0)
          = x + u * j * m0 := by rw [hx]; ring
        _ = x + (c * s - c * q * Int.gcdB u q * m0) := by rw [key]
        _ = (x % s + x / s * s) + ((c1 - x / s) * s - c * (|q| * σ) * Int.gcdB u q * m0) := by
            rw [hxdiv, ← hqσ, hc]
        _ = ((x % s) + (c1 : ℤ) * s) + M * (-(σ * Int.gcdB u q * c)) := by rw [hM]; ring
    have hmod : (u * (k0 * |q| + j * m0)) % M = (x % s) + (c1 : ℤ) * s := by
      rw [hsplit, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt hP0 (by rw [hMs]; exact hP1)
    rw [hmod, hMs]
    have hT0 : (0 : ℤ) ≤ (T.card : ℤ) - 2 := by linarith
    constructor
    · nlinarith [mul_nonneg hT0 hP0]
    · nlinarith [mul_nonneg hT0 (show (0 : ℤ) ≤ E * s - (x % s + (c1 : ℤ) * s) by linarith)]
  · -- a team runner keeps its distance, scaled by |q|
    obtain ⟨w, hw⟩ := (abs_dvd q v).mpr (hq v hvT)
    have hold := hfar v hvT
    unfold far at hold
    push_cast at hold
    have hsplit : v * (k0 * |q| + j * m0) = |q| * (v * k0) + M * (w * j) := by
      rw [hM]
      calc v * (k0 * |q| + j * m0) = |q| * (v * k0) + v * j * m0 := by ring
        _ = |q| * (v * k0) + |q| * w * j * m0 := by rw [hw]
        _ = |q| * (v * k0) + |q| * (m0 : ℤ) * (w * j) := by ring
    have hmod : (v * (k0 * |q| + j * m0)) % M = |q| * ((v * k0) % m0) := by
      rw [hsplit, Int.add_mul_emod_self_left, hM, Int.mul_emod_mul_of_pos _ _ hQ]
    rw [hmod, hM]
    have hr0 : 0 ≤ (v * k0) % (m0 : ℤ) := Int.emod_nonneg _ (ne_of_gt hm0')
    have hr1 : (v * k0) % (m0 : ℤ) < m0 := Int.emod_lt_of_pos _ hm0'
    obtain ⟨hA, hB⟩ := hold
    have hr2 : (0 : ℤ) ≤ (m0 : ℤ) - (v * k0) % (m0 : ℤ) := by linarith
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hA hQ.le, mul_nonneg hQ.le hr0]
    · nlinarith [mul_le_mul_of_nonneg_left hB hQ.le, mul_nonneg hQ.le hr2]

theorem team_shift_step_holds_from (h : team_shift) : team_shift_step := by
  intro c hc T u q h0 hcard hcardc hu hq hqu
  exact h T u q hcard hu hq hqu (hc T h0 hcardc)

theorem team_shift_step_holds : team_shift_step :=
  team_shift_step_holds_from team_shift_holds

end RNS.TeamShift

#print axioms RNS.TeamShift.team_shift_holds
#print axioms RNS.TeamShift.team_shift_step_holds
