/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Algebra.Order.Interval.Finset.Basic -- `Finset.map_add_right_Icc`
import Mathlib.Tactic.Ring
import RNSNetwork.Nodes.UniformSubdivision.Conclusions

/-!
# Proofs for UniformSubdivision

Imports claims only, never other nodes' proofs. Proves all five of the
node's claims: `frozen_wheels_repeat`, `one_wheel_removed`,
`uniform_subdivision`, and the two column forms.

None rests on another node, so each is proved directly as a `_holds`
theorem; the later ones use the earlier ones and helper lemmas from this
file.
-/

namespace RNS.UniformSubdivision

/-- Adding the length of the combined cycle does not change whether a number
survives: every wheel size divides the cycle length. -/
private theorem survives_add_prod (W : Finset Nat) (k : Nat) :
    (∀ q ∈ W, ¬ q ∣ k + W.prod id) ↔ (∀ q ∈ W, ¬ q ∣ k) := by
  constructor
  · intro h q hq hdvd
    exact h q hq ((Nat.dvd_add_left (Finset.dvd_prod_of_mem id hq)).mpr hdvd)
  · intro h q hq hdvd
    exact h q hq ((Nat.dvd_add_left (Finset.dvd_prod_of_mem id hq)).mp hdvd)

/-- Splitting off one full cycle: the survivors up to one cycle plus `N` are
the survivors of the first cycle plus the survivors up to `N`. -/
private theorem card_survivors_prod_add (W : Finset Nat) (N : Nat) :
    (survivors_upto W (W.prod id + N)).card
      = (survivors_upto W (W.prod id)).card + (survivors_upto W N).card := by
  unfold survivors_upto
  -- The range up to one cycle plus `N` is the first cycle together with the
  -- range up to `N` slid up by one cycle.
  have hsplit : Finset.Icc 1 (W.prod id + N)
      = Finset.Icc 1 (W.prod id) ∪ (Finset.Icc 1 N).map (addRightEmbedding (W.prod id)) := by
    rw [Finset.map_add_right_Icc]
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (W.prod id))
      ((Finset.Icc 1 N).map (addRightEmbedding (W.prod id))) := by
    rw [Finset.map_add_right_Icc, Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_Icc] at hk hk'
    omega
  rw [hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
    Finset.filter_map, Finset.card_map]
  congr 1
  congr 1
  exact Finset.filter_congr (fun k _ => by
    simp only [Function.comp_apply, addRightEmbedding_apply]
    exact survives_add_prod W k)

/-- **Frozen wheels repeat**, proved. -/
theorem frozen_wheels_repeat_holds : frozen_wheels_repeat := by
  intro W m r
  induction m with
  | zero => simp
  | succ m ih =>
    have h : (m + 1) * W.prod id + r = W.prod id + (m * W.prod id + r) := by ring
    rw [h, card_survivors_prod_add, ih]
    ring

end RNS.UniformSubdivision

#print axioms RNS.UniformSubdivision.frozen_wheels_repeat_holds

/-! ## One wheel removed (Meissel's identity) -/

namespace RNS.UniformSubdivision

/-- The survivors of the wheels `W` together with a new wheel `p` are the
survivors of `W` that `p` does not divide. -/
private theorem survivors_insert (W : Finset Nat) (p N : Nat) :
    survivors_upto (insert p W) N = (survivors_upto W N).filter (fun k => ¬ p ∣ k) := by
  ext k
  simp only [survivors_upto, Finset.mem_filter, Finset.forall_mem_insert]
  tauto

/-- The survivors of `W` that the new prime `p` divides are exactly `p` times
the survivors of `W` up to `N / p`. -/
private theorem multiples_eq_image (W : Finset Nat) (p N : Nat) (hp : p.Prime)
    (hW : ∀ q ∈ W, q.Prime) (hpW : p ∉ W) :
    (survivors_upto W N).filter (fun k => p ∣ k)
      = (survivors_upto W (N / p)).image (fun j => p * j) := by
  ext k
  simp only [survivors_upto, Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hk1, hkN⟩, hsurv⟩, hpk⟩
    have hcancel : p * (k / p) = k := Nat.mul_div_cancel' hpk
    refine ⟨k / p, ⟨⟨?_, Nat.div_le_div_right hkN⟩, ?_⟩, hcancel⟩
    · rcases Nat.eq_zero_or_pos (k / p) with h0 | h0
      · rw [h0, Nat.mul_zero] at hcancel
        omega
      · omega
    · intro q hq hqj
      have hqk : q ∣ p * (k / p) := Nat.dvd_mul_left_of_dvd hqj p
      rw [hcancel] at hqk
      exact hsurv q hq hqk
  · rintro ⟨j, ⟨⟨hj1, hjN⟩, hsurv⟩, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, Nat.dvd_mul_right p j⟩
    · have hpos : 0 < p * j := Nat.mul_pos hp.pos (by omega)
      omega
    · calc p * j ≤ p * (N / p) := Nat.mul_le_mul (Nat.le_refl p) hjN
        _ ≤ N := Nat.mul_div_le N p
    · intro q hq hqd
      rcases (hW q hq).dvd_mul.mp hqd with h | h
      · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq (hW q hq) hp).mp h
        exact hpW (by rw [← hqp]; exact hq)
      · exact hsurv q hq h

/-- **One wheel removed**, proved. -/
theorem one_wheel_removed_holds : one_wheel_removed := by
  intro W p N hp hW hpW
  have hsplit : ((survivors_upto W N).filter (fun k => p ∣ k)).card
      + ((survivors_upto W N).filter (fun k => ¬ p ∣ k)).card = (survivors_upto W N).card :=
    Finset.card_filter_add_card_filter_not _
  have h1 : (survivors_upto (insert p W) N).card
      = ((survivors_upto W N).filter (fun k => ¬ p ∣ k)).card := by
    rw [survivors_insert]
  have hinj : Function.Injective (fun j : Nat => p * j) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hp.pos hab
  have h2 : ((survivors_upto W N).filter (fun k => p ∣ k)).card
      = (survivors_upto W (N / p)).card := by
    rw [multiples_eq_image W p N hp hW hpW, Finset.card_image_of_injective _ hinj]
  omega

end RNS.UniformSubdivision

#print axioms RNS.UniformSubdivision.one_wheel_removed_holds

/-! ## Uniform subdivision -/

namespace RNS.UniformSubdivision

/-- The arithmetic behind the subdivision. If `M` is `d` times a quotient
plus a remainder below `d`, then `M` times `d + 1`, divided by `d`, rounds
down to `M` plus the quotient, and that, divided by `d + 1`, rounds down to
the quotient. -/
private theorem floor_facts (M d a b : Nat) (hab : d * a + b = M) (hb : b < d) :
    M * (d + 1) / d = M + a ∧ (M + a) / (d + 1) = a := by
  subst hab
  constructor
  · apply Nat.div_eq_of_lt_le
    · have e1 : (d * a + b + a) * d = d * (d * a) + b * d + a * d := by ring
      have e2 : (d * a + b) * (d + 1) = d * (d * a) + b * d + a * d + b := by ring
      rw [e1, e2]
      omega
    · have e2 : (d * a + b) * (d + 1) = d * (d * a) + b * d + a * d + b := by ring
      have e3 : (d * a + b + a + 1) * d = d * (d * a) + b * d + a * d + d := by ring
      rw [e2, e3]
      omega
  · apply Nat.div_eq_of_lt_le
    · have e4 : a * (d + 1) = d * a + a := by ring
      rw [e4]
      omega
    · have e5 : (a + 1) * (d + 1) = d * a + a + d + 1 := by ring
      rw [e5]
      omega

/-- **Uniform subdivision**, proved from `frozen_wheels_repeat` and
`one_wheel_removed`. -/
theorem uniform_subdivision_holds : uniform_subdivision := by
  intro W p K hp hW hpW
  have hd : 0 < p - 1 := by
    have := hp.two_le
    omega
  have hp1 : p - 1 + 1 = p := by
    have := hp.two_le
    omega
  obtain ⟨hN, hNp⟩ := floor_facts (K * W.prod id) (p - 1) (K * W.prod id / (p - 1))
    (K * W.prod id % (p - 1)) (Nat.div_add_mod _ _) (Nat.mod_lt _ hd)
  rw [hp1] at hN hNp
  -- The end of the `K`-th interval is `K` frozen cycles plus the overhang.
  have hend : K * (W.prod id * p) / (p - 1) = K * W.prod id + K * W.prod id / (p - 1) := by
    rw [← hN, Nat.mul_assoc]
  rw [hend, one_wheel_removed_holds W p _ hp hW hpW, hNp, frozen_wheels_repeat_holds W K]
  omega

end RNS.UniformSubdivision

#print axioms RNS.UniformSubdivision.uniform_subdivision_holds

/-! ## The column forms -/

namespace RNS.UniformSubdivision

/-- Splitting off one period, for any test unchanged by a shift of one
period: the numbers passing it up to one period plus `N` are those in the
first period plus those up to `N`. -/
private theorem card_filter_Icc_add (P : Nat → Prop) [DecidablePred P] (Q N : Nat)
    (hP : ∀ k, P (k + Q) ↔ P k) :
    ((Finset.Icc 1 (Q + N)).filter P).card
      = ((Finset.Icc 1 Q).filter P).card + ((Finset.Icc 1 N).filter P).card := by
  have hsplit : Finset.Icc 1 (Q + N)
      = Finset.Icc 1 Q ∪ (Finset.Icc 1 N).map (addRightEmbedding Q) := by
    rw [Finset.map_add_right_Icc]
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 Q) ((Finset.Icc 1 N).map (addRightEmbedding Q)) := by
    rw [Finset.map_add_right_Icc, Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_Icc] at hk hk'
    omega
  rw [hsplit, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
    Finset.filter_map, Finset.card_map]
  congr 1
  congr 1
  exact Finset.filter_congr (fun k _ => by
    simp only [Function.comp_apply, addRightEmbedding_apply]
    exact hP k)

/-- Splitting off one cycle, within one column. With wheels 2 and 3 frozen,
the cycle is a multiple of 6, so a shift by one cycle keeps every number in
its column. -/
private theorem card_col_prod_add (W : Finset Nat) (r N : Nat) (h2 : 2 ∈ W) (h3 : 3 ∈ W) :
    (column_survivors_upto W r (W.prod id + N)).card
      = (column_survivors_upto W r (W.prod id)).card + (column_survivors_upto W r N).card := by
  have h2' : 2 ∣ W.prod id := Finset.dvd_prod_of_mem id h2
  have h3' : 3 ∣ W.prod id := Finset.dvd_prod_of_mem id h3
  unfold column_survivors_upto survivors_upto
  simp only [Finset.filter_filter]
  apply card_filter_Icc_add
  intro k
  try dsimp only
  have hmod : (k + W.prod id) % 6 = k % 6 := by omega
  rw [hmod, survives_add_prod]

/-- **Frozen wheels repeat, within one column.** -/
private theorem col_frozen_repeat (W : Finset Nat) (r K N : Nat) (h2 : 2 ∈ W) (h3 : 3 ∈ W) :
    (column_survivors_upto W r (K * W.prod id + N)).card
      = K * (column_survivors_upto W r (W.prod id)).card
        + (column_survivors_upto W r N).card := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h : (K + 1) * W.prod id + N = W.prod id + (K * W.prod id + N) := by ring
    rw [h, card_col_prod_add W r _ h2 h3, ih]
    ring

/-- **One wheel removed, within one column.** The multiples of the new prime
`p` in column `r` are `p` times the old survivors up to `N / p` in column `r'`,
where multiplying by `p` carries column `r'` to column `r`. Written added up,
to avoid truncated subtraction. -/
private theorem col_one_wheel_removed (W : Finset Nat) (p N r r' : Nat) (hp : p.Prime)
    (hW : ∀ q ∈ W, q.Prime) (hpW : p ∉ W) (hr : ∀ j, p * j % 6 = r ↔ j % 6 = r') :
    (column_survivors_upto (insert p W) r N).card + (column_survivors_upto W r' (N / p)).card
      = (column_survivors_upto W r N).card := by
  have hins : column_survivors_upto (insert p W) r N
      = (column_survivors_upto W r N).filter (fun k => ¬ p ∣ k) := by
    ext k
    simp only [column_survivors_upto, survivors_upto, Finset.mem_filter,
      Finset.forall_mem_insert]
    tauto
  have himg : (column_survivors_upto W r N).filter (fun k => p ∣ k)
      = (column_survivors_upto W r' (N / p)).image (fun j => p * j) := by
    ext k
    simp only [column_survivors_upto, survivors_upto, Finset.mem_filter, Finset.mem_image,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨hk1, hkN⟩, hsurv⟩, hkr⟩, hpk⟩
      have hcancel : p * (k / p) = k := Nat.mul_div_cancel' hpk
      refine ⟨k / p, ⟨⟨⟨?_, Nat.div_le_div_right hkN⟩, ?_⟩, ?_⟩, hcancel⟩
      · rcases Nat.eq_zero_or_pos (k / p) with h0 | h0
        · rw [h0, Nat.mul_zero] at hcancel
          omega
        · omega
      · intro q hq hqj
        have hqk : q ∣ p * (k / p) := Nat.dvd_mul_left_of_dvd hqj p
        rw [hcancel] at hqk
        exact hsurv q hq hqk
      · apply (hr (k / p)).mp
        rw [hcancel]
        exact hkr
    · rintro ⟨j, ⟨⟨⟨hj1, hjN⟩, hsurv⟩, hjr⟩, rfl⟩
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, (hr j).mpr hjr⟩, Nat.dvd_mul_right p j⟩
      · have hpos : 0 < p * j := Nat.mul_pos hp.pos (by omega)
        omega
      · calc p * j ≤ p * (N / p) := Nat.mul_le_mul (Nat.le_refl p) hjN
          _ ≤ N := Nat.mul_div_le N p
      · intro q hq hqd
        rcases (hW q hq).dvd_mul.mp hqd with h | h
        · have hqp : q = p := (Nat.prime_dvd_prime_iff_eq (hW q hq) hp).mp h
          exact hpW (by rw [← hqp]; exact hq)
        · exact hsurv q hq h
  have hsplit : ((column_survivors_upto W r N).filter (fun k => p ∣ k)).card
      + ((column_survivors_upto W r N).filter (fun k => ¬ p ∣ k)).card
      = (column_survivors_upto W r N).card :=
    Finset.card_filter_add_card_filter_not _
  have hinj : Function.Injective (fun j : Nat => p * j) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hp.pos hab
  have hmult : ((column_survivors_upto W r N).filter (fun k => p ∣ k)).card
      = (column_survivors_upto W r' (N / p)).card := by
    rw [himg, Finset.card_image_of_injective _ hinj]
  rw [hins]
  omega

/-- With wheels 2 and 3 frozen, every survivor leaves remainder 1 or 5 on
division by 6, so any other column is empty. -/
private theorem col_empty (W : Finset Nat) (r N : Nat) (h2 : 2 ∈ W) (h3 : 3 ∈ W)
    (hr : ¬ (r = 1 ∨ r = 5)) : (column_survivors_upto W r N).card = 0 := by
  rw [Finset.card_eq_zero]
  unfold column_survivors_upto
  rw [Finset.filter_eq_empty_iff]
  intro k hk hkr
  simp only [survivors_upto, Finset.mem_filter] at hk
  have h2k := hk.2 2 h2
  have h3k := hk.2 3 h3
  omega

/-- **Uniform subdivision, rotating wheel on the 6n+1 side**, proved. -/
theorem uniform_subdivision_plus_side_holds : uniform_subdivision_plus_side := by
  intro W p K r hp hW hpW h2 h3 hp6
  have hd : 0 < p - 1 := by
    have := hp.two_le
    omega
  have hp1 : p - 1 + 1 = p := by
    have := hp.two_le
    omega
  obtain ⟨hN, hNp⟩ := floor_facts (K * W.prod id) (p - 1) (K * W.prod id / (p - 1))
    (K * W.prod id % (p - 1)) (Nat.div_add_mod _ _) (Nat.mod_lt _ hd)
  rw [hp1] at hN hNp
  have hend : K * (W.prod id * p) / (p - 1) = K * W.prod id + K * W.prod id / (p - 1) := by
    rw [← hN, Nat.mul_assoc]
  -- Multiplying by a prime on the 6n+1 side keeps every column in place.
  have hr : ∀ j, p * j % 6 = r ↔ j % 6 = r := by
    intro j
    rw [Nat.mul_mod, hp6]
    omega
  have hA := col_one_wheel_removed W p (K * (W.prod id * p) / (p - 1)) r r hp hW hpW hr
  rw [hend, hNp, col_frozen_repeat W r K _ h2 h3] at hA
  rw [hend]
  omega

/-- **Uniform subdivision, rotating wheel on the 6n-1 side**, proved. -/
theorem uniform_subdivision_minus_side_holds : uniform_subdivision_minus_side := by
  intro W p K r hp hW hpW h2 h3 hp6
  have hd : 0 < p - 1 := by
    have := hp.two_le
    omega
  have hp1 : p - 1 + 1 = p := by
    have := hp.two_le
    omega
  obtain ⟨hN, hNp⟩ := floor_facts (K * W.prod id) (p - 1) (K * W.prod id / (p - 1))
    (K * W.prod id % (p - 1)) (Nat.div_add_mod _ _) (Nat.mod_lt _ hd)
  rw [hp1] at hN hNp
  have hend : K * (W.prod id * p) / (p - 1) = K * W.prod id + K * W.prod id / (p - 1) := by
    rw [← hN, Nat.mul_assoc]
  rw [hend]
  by_cases hr15 : r = 1 ∨ r = 5
  · -- Multiplying by a prime on the 6n-1 side swaps the two columns.
    have hr : ∀ j, p * j % 6 = r ↔ j % 6 = 6 - r := by
      intro j
      rw [Nat.mul_mod, hp6]
      omega
    have hA := col_one_wheel_removed W p (K * (W.prod id * p) / (p - 1)) r (6 - r)
      hp hW hpW hr
    rw [hend, hNp, col_frozen_repeat W r K _ h2 h3] at hA
    omega
  · -- Every other column is empty, so both sides are zero.
    have h6r : ¬ (6 - r = 1 ∨ 6 - r = 5) := by omega
    have e1 := col_empty (insert p W) r (K * W.prod id + K * W.prod id / (p - 1))
      (Finset.mem_insert_of_mem h2) (Finset.mem_insert_of_mem h3) hr15
    have e2 := col_empty W (6 - r) (K * W.prod id / (p - 1)) h2 h3 h6r
    have e3 := col_empty W r (W.prod id) h2 h3 hr15
    have e4 := col_empty W r (K * W.prod id / (p - 1)) h2 h3 hr15
    rw [e1, e2, e3, e4, Nat.mul_zero]

end RNS.UniformSubdivision

#print axioms RNS.UniformSubdivision.uniform_subdivision_plus_side_holds
#print axioms RNS.UniformSubdivision.uniform_subdivision_minus_side_holds
