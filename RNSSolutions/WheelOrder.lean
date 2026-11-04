/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List -- `List.prod_pos`
import Mathlib.Tactic.Push                                    -- `push Not`
import RNSNetwork.Nodes.WheelOrder.Conclusions

/-!
# Proofs for WheelOrder

Rests on no other node. Tactic proofs are copied from `rns_sieve_6.lean`,
Parts F and G; the only changes are an `unfold` of each stated claim, and
private helpers.
-/

namespace RNS.WheelOrder

/-! ## Part F: ordered marginal wheel contributions -/

private theorem card_filter_mod_mul (M A : Nat) (hM : 0 < M) (S : Finset Nat)
    (hS : ∀ r ∈ S, r < M) :
    ((Finset.range (M * A)).filter (fun k => k % M ∈ S)).card = S.card * A := by
  have hbij : ((Finset.range (M * A)).filter (fun k => k % M ∈ S)).card
      = (S ×ˢ Finset.range A).card := by
    apply Finset.card_bij' (fun k _ => (k % M, k / M)) (fun ra _ => M * ra.2 + ra.1)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hklt, hkS⟩ := hk
      simp only [Finset.mem_product, Finset.mem_range]
      refine ⟨hkS, ?_⟩
      have hdm := Nat.div_add_mod k M
      by_contra hcon
      push Not at hcon
      have hge : M * A ≤ M * (k / M) := Nat.mul_le_mul_left M hcon
      omega
    · rintro ⟨r, a⟩ hra
      simp only [Finset.mem_product, Finset.mem_range] at hra
      obtain ⟨hrS, haA⟩ := hra
      have hrM : r < M := hS r hrS
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ?_⟩
      · have haA1 : a + 1 ≤ A := haA
        have : M * a + M ≤ M * A := by
          have := Nat.mul_le_mul_left M haA1
          omega
        omega
      · have hmod : (M * a + r) % M = r := by
          have hcomm : M * a + r = r + a * M := by ring
          rw [hcomm, Nat.add_mul_mod_self_right]
          exact Nat.mod_eq_of_lt hrM
        rw [hmod]
        exact hrS
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      have hdm := Nat.div_add_mod k M
      simp only
      omega
    · rintro ⟨r, a⟩ hra
      simp only [Finset.mem_product, Finset.mem_range] at hra
      obtain ⟨hrS, haA⟩ := hra
      have hrM : r < M := hS r hrS
      have hmod : (M * a + r) % M = r := by
        have hcomm : M * a + r = r + a * M := by ring
        rw [hcomm, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt hrM
      have hdiv : (M * a + r) / M = a := by
        have hcomm : M * a + r = r + a * M := by ring
        rw [hcomm, Nat.add_mul_div_right r a hM, Nat.div_eq_of_lt hrM]
        omega
      simp only [hmod, hdiv]
  rw [hbij, Finset.card_product, Finset.card_range]

private theorem card_multiples_avoid (p R : Nat) (hp : p.Prime) (rest : List Nat)
    (hrest_prime : ∀ s ∈ rest, s.Prime) (hpnr : p ∉ rest) :
    ((Finset.range (p * R)).filter (fun k => p ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k)).card
      = ((Finset.range R).filter (fun j => ∀ s ∈ rest, ¬ s ∣ j)).card := by
  have himg : (Finset.range (p * R)).filter (fun k => p ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k)
      = ((Finset.range R).filter (fun j => ∀ s ∈ rest, ¬ s ∣ j)).image (fun j => p * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hklt, ⟨j, hjk⟩, hkavoid⟩
      refine ⟨j, ⟨?_, ?_⟩, hjk.symm⟩
      · have hplt : 0 < p := hp.pos
        rw [hjk] at hklt
        exact lt_of_mul_lt_mul_left hklt (Nat.zero_le p)
      · intro s hs hsdvd
        apply hkavoid s hs
        rw [hjk]
        exact Dvd.dvd.mul_left hsdvd p
    · rintro ⟨j, ⟨hjlt, hjavoid⟩, rfl⟩
      refine ⟨?_, ⟨j, rfl⟩, ?_⟩
      · exact (Nat.mul_lt_mul_left hp.pos).mpr hjlt
      · intro s hs hsdvd
        have hsprime : s.Prime := hrest_prime s hs
        rcases hsprime.dvd_mul.mp hsdvd with hsp | hsj
        · exfalso
          rcases hp.eq_one_or_self_of_dvd s hsp with h1 | hspq
          · exact absurd h1 hsprime.one_lt.ne'
          · exact hpnr (hspq ▸ hs)
        · exact hjavoid s hs hsj
  rw [himg]
  apply Finset.card_image_of_injective
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left hp.pos hab

private def avoid_count (l : List Nat) : Nat :=
  ((Finset.range l.prod).filter (fun x => ∀ q ∈ l, ¬ q ∣ x)).card

private theorem dvd_mod_iff_dvd (s R k : Nat) (hsR : s ∣ R) : s ∣ (k % R) ↔ s ∣ k := by
  have hdm : R * (k / R) + k % R = k := Nat.div_add_mod k R
  have hsdvd : s ∣ (R * (k / R)) := hsR.mul_right (k / R)
  constructor
  · intro h
    have hsum : s ∣ (R * (k / R) + k % R) := Nat.dvd_add hsdvd h
    rwa [hdm] at hsum
  · intro h
    rw [← hdm] at h
    exact (Nat.dvd_add_right hsdvd).mp h

private theorem mem_dvd_prod (l : List Nat) (q : Nat) (hq : q ∈ l) : q ∣ l.prod := by
  induction l with
  | nil => cases hq
  | cons a t ih =>
    rw [List.prod_cons]
    rcases List.mem_cons.mp hq with rfl | hqt
    · exact Dvd.dvd.mul_right (dvd_refl q) t.prod
    · exact (ih hqt).mul_left a

private theorem avoid_count_eq_prod (l : List Nat) (hl : ∀ q ∈ l, q.Prime) (hnd : l.Nodup) :
    avoid_count l = (l.map (· - 1)).prod := by
  induction l with
  | nil => simp [avoid_count]
  | cons q rest ih =>
    have hq_prime : q.Prime := hl q List.mem_cons_self
    have hrest_prime : ∀ s ∈ rest, s.Prime := fun s hs => hl s (List.mem_cons_of_mem q hs)
    have hqnr : q ∉ rest := (List.nodup_cons.mp hnd).1
    have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd).2
    have ih' : avoid_count rest = (rest.map (· - 1)).prod := ih hrest_prime hnd_rest
    set R := rest.prod with hRdef
    have hRpos : 0 < R := by
      rw [hRdef]
      exact List.prod_pos (fun s hs => (hrest_prime s hs).pos)
    set S : Finset Nat := (Finset.range R).filter (fun j => ∀ s ∈ rest, ¬ s ∣ j) with hSdef
    have hScard : S.card = avoid_count rest := by
      rw [hSdef, hRdef]
      rfl
    have hSlt : ∀ r ∈ S, r < R := by
      intro r hr
      rw [hSdef, Finset.mem_filter, Finset.mem_range] at hr
      exact hr.1
    have hblock := card_filter_mod_mul R q hRpos S hSlt
    rw [hScard] at hblock
    have hpred_eq : (Finset.range (R * q)).filter (fun k => k % R ∈ S)
        = (Finset.range (R * q)).filter (fun k => ∀ s ∈ rest, ¬ s ∣ k) := by
      apply Finset.filter_congr
      intro k _
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h s hs hsdvd
        have hsR : s ∣ R := hRdef ▸ mem_dvd_prod rest s hs
        exact h.2 s hs ((dvd_mod_iff_dvd s R k hsR).mpr hsdvd)
      · intro h
        refine ⟨Nat.mod_lt k hRpos, ?_⟩
        intro s hs hsdvd
        have hsR : s ∣ R := hRdef ▸ mem_dvd_prod rest s hs
        exact h s hs ((dvd_mod_iff_dvd s R k hsR).mp hsdvd)
    rw [hpred_eq] at hblock
    have hT1 : ((Finset.range (q * R)).filter (fun k => ∀ s ∈ rest, ¬ s ∣ k)).card
        = avoid_count rest * q := by
      rw [Nat.mul_comm q R]
      exact hblock
    have hmult : ((Finset.range (q * R)).filter (fun k => q ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k)).card
        = avoid_count rest := by
      rw [card_multiples_avoid q R hq_prime rest hrest_prime hqnr]
      exact hScard
    have hsplit : (Finset.range (q * R)).filter (fun k => ∀ s ∈ rest, ¬ s ∣ k)
        = ((Finset.range (q * R)).filter (fun k => q ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k))
          ∪ ((Finset.range (q * R)).filter (fun k => ¬ q ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range]
      constructor
      · rintro ⟨hklt, havoid⟩
        by_cases hqk : q ∣ k
        · exact Or.inl ⟨hklt, hqk, havoid⟩
        · exact Or.inr ⟨hklt, hqk, havoid⟩
      · rintro (⟨hklt, _, havoid⟩ | ⟨hklt, _, havoid⟩) <;> exact ⟨hklt, havoid⟩
    have hdisjoint : Disjoint
        ((Finset.range (q * R)).filter (fun k => q ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k))
        ((Finset.range (q * R)).filter (fun k => ¬ q ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_filter] at ha hb
      exact hb.2.1 ha.2.1
    have hcardsum : ((Finset.range (q * R)).filter (fun k => ∀ s ∈ rest, ¬ s ∣ k)).card
        = ((Finset.range (q * R)).filter (fun k => q ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k)).card
          + ((Finset.range (q * R)).filter (fun k => ¬ q ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k)).card := by
      rw [hsplit]
      exact Finset.card_union_of_disjoint hdisjoint
    have hfinal_set_eq : (Finset.range (q * R)).filter (fun k => ¬ q ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k)
        = (Finset.range ((q :: rest).prod)).filter (fun k => ∀ t ∈ (q :: rest), ¬ t ∣ k) := by
      have hprodeq : (q :: rest).prod = q * R := by
        rw [List.prod_cons, hRdef]
      rw [hprodeq]
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, List.mem_cons]
      constructor
      · rintro ⟨hklt, hqk, havoid⟩
        refine ⟨hklt, ?_⟩
        intro t ht
        rcases ht with rfl | htrest
        · exact hqk
        · exact havoid t htrest
      · intro ⟨hklt, havoid⟩
        refine ⟨hklt, havoid q (Or.inl rfl), ?_⟩
        intro s hs
        exact havoid s (Or.inr hs)
    have hqcount : avoid_count (q :: rest)
        = ((Finset.range (q * R)).filter (fun k => ¬ q ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k)).card := by
      unfold avoid_count
      rw [hfinal_set_eq]
    obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq_prime.two_le; omega⟩
    have hXeq : ((Finset.range (q * R)).filter (fun k => ¬ q ∣ k ∧ ∀ s ∈ rest, ¬ s ∣ k)).card
        = avoid_count rest * q' := by
      have hd : avoid_count rest * q = avoid_count rest * q' + avoid_count rest := by
        rw [hq']; ring
      omega
    rw [hqcount, hXeq]
    have hmap : (q :: rest).map (· - 1) = q' :: rest.map (· - 1) := by
      simp [hq']
    rw [hmap, List.prod_cons, ← ih']
    ring

private def new_wheel_count (before : List Nat) (p : Nat) (after : List Nat) : Nat :=
  ((Finset.range ((before ++ p :: after).prod)).filter
    (fun x => p ∣ x ∧ ∀ q ∈ before, ¬ q ∣ x)).card

private theorem wheel_marginal_new_formula_aux (before : List Nat) (p : Nat)
    (after : List Nat) (hp : p.Prime) (hbefore_prime : ∀ q ∈ before, q.Prime)
    (hbefore_nodup : before.Nodup) (hp_notin_before : p ∉ before) :
    new_wheel_count before p after = (before.map (· - 1)).prod * after.prod := by
  set Mb := before.prod with hMbdef
  set Ab := after.prod with hAbdef
  set M := Mb * p with hMdef
  have hMbpos : 0 < Mb := by
    rw [hMbdef]; exact List.prod_pos (fun q hq => (hbefore_prime q hq).pos)
  have hMpos : 0 < M := by rw [hMdef]; exact Nat.mul_pos hMbpos hp.pos
  have hprod_eq : (before ++ p :: after).prod = M * Ab := by
    rw [List.prod_append, List.prod_cons, hMdef, hMbdef, hAbdef]
    ring
  set S' : Finset Nat := (Finset.range M).filter (fun k => p ∣ k ∧ ∀ q ∈ before, ¬ q ∣ k)
    with hS'def
  have hS'lt : ∀ r ∈ S', r < M := by
    intro r hr
    rw [hS'def, Finset.mem_filter, Finset.mem_range] at hr
    exact hr.1
  have hblock := card_filter_mod_mul M Ab hMpos S' hS'lt
  have hpM : p ∣ M := by rw [hMdef]; exact Dvd.dvd.mul_left (dvd_refl p) Mb
  have hpred_eq : (Finset.range (M * Ab)).filter (fun k => k % M ∈ S')
      = (Finset.range (M * Ab)).filter (fun k => p ∣ k ∧ ∀ q ∈ before, ¬ q ∣ k) := by
    apply Finset.filter_congr
    intro k _
    rw [hS'def, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      refine ⟨(dvd_mod_iff_dvd p M k hpM).mp h.2.1, ?_⟩
      intro q hq hqdvd
      have hqM : q ∣ M := by
        rw [hMdef]; exact Dvd.dvd.mul_right (mem_dvd_prod before q hq) p
      exact h.2.2 q hq ((dvd_mod_iff_dvd q M k hqM).mpr hqdvd)
    · intro h
      refine ⟨Nat.mod_lt k hMpos, (dvd_mod_iff_dvd p M k hpM).mpr h.1, ?_⟩
      intro q hq hqdvd
      have hqM : q ∣ M := by
        rw [hMdef]; exact Dvd.dvd.mul_right (mem_dvd_prod before q hq) p
      exact h.2 q hq ((dvd_mod_iff_dvd q M k hqM).mp hqdvd)
  rw [hpred_eq] at hblock
  have hS'card : S'.card = (before.map (· - 1)).prod := by
    have h := card_multiples_avoid p Mb hp before hbefore_prime hp_notin_before
    have hMeq : M = p * Mb := by rw [hMdef]; ring
    have hrhs : ((Finset.range Mb).filter (fun j => ∀ q ∈ before, ¬ q ∣ j)).card
        = avoid_count before := by
      unfold avoid_count
      rw [hMbdef]
    rw [hS'def, hMeq, h, hrhs]
    exact avoid_count_eq_prod before hbefore_prime hbefore_nodup
  unfold new_wheel_count
  rw [hprod_eq, hblock, hS'card]

theorem wheel_marginal_new_formula_holds : wheel_marginal_new_formula := by
  unfold wheel_marginal_new_formula
  intro before p after hp hbefore_prime hbefore_nodup hp_notin_before
  exact wheel_marginal_new_formula_aux before p after hp hbefore_prime hbefore_nodup
    hp_notin_before

/-! ## Part G: the last-digit wheel -/

theorem prime_gt_five_digit_ok_holds : prime_gt_five_digit_ok := by
  unfold prime_gt_five_digit_ok
  intro p hp h_gt
  have h2 : ¬ (2 ∣ p) := by
    intro hdvd
    rcases hp.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega
  have h5 : ¬ (5 ∣ p) := by
    intro hdvd
    rcases hp.eq_one_or_self_of_dvd 5 hdvd with h | h <;> omega
  unfold digit_ok
  simp only [Bool.or_eq_true, beq_iff_eq]
  omega

private theorem wheel_gap_core (r6 r10 b : Nat) (hr10 : r10 < 10)
    (htrack : r6 = 1 ∨ r6 = 5) (hpar : r10 % 2 = 1)
    (hdigit : b = 1 ∨ b = 3 ∨ b = 7 ∨ b = 9) :
    (r6 + digit_gap r10 b) % 6 = 1 ∨ (r6 + digit_gap r10 b) % 6 = 5 ∨
    (r6 + digit_gap r10 b + 10) % 6 = 1 ∨ (r6 + digit_gap r10 b + 10) % 6 = 5 := by
  have hr10' : r10 = 1 ∨ r10 = 3 ∨ r10 = 5 ∨ r10 = 7 ∨ r10 = 9 := by omega
  rcases htrack with rfl | rfl <;>
  rcases hdigit with rfl | rfl | rfl | rfl <;>
  rcases hr10' with rfl | rfl | rfl | rfl | rfl <;>
  decide

theorem wheel_gap_floor_holds : wheel_gap_floor := by
  unfold wheel_gap_floor
  intro n b htrack hdigit
  unfold is_candidate at htrack ⊢
  simp only [Bool.or_eq_true, beq_iff_eq] at htrack ⊢
  have hr10 : n % 10 < 10 := Nat.mod_lt n (by norm_num)
  have hn2 : n % 2 = 1 := by omega
  have hpar : n % 10 % 2 = 1 := by omega
  have hcore := wheel_gap_core (n % 6) (n % 10) b hr10 htrack hpar hdigit
  omega

end RNS.WheelOrder

#print axioms RNS.WheelOrder.wheel_marginal_new_formula_holds
#print axioms RNS.WheelOrder.prime_gt_five_digit_ok_holds
#print axioms RNS.WheelOrder.wheel_gap_floor_holds
