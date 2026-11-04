/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.CRT.Conclusions
import RNSNetwork.Nodes.SurvivorCount.Conclusions

/-!
# Proofs for SurvivorCount

Imports claims only, never other nodes' proofs. Two of the three conclusions
are proved as steps from the `CRT` claim, taken as the hypothesis `h_crt`;
`RNSSolutions/Assemble.lean` plugs in the finished `CRT` proof.

Tactic proofs: the twin-pattern count is from `wheelSurvivorsCardFormula` in
the `HardyLittlewood` repository; the general-pattern counts are from
`rns_sieve_6.lean`, Part B Step 4. The only change in each is that the call
to the CRT bijection is replaced by the hypothesis `h_crt`.
-/

namespace RNS.SurvivorCount

private theorem mem_active_primes_is_prime (limit : Nat) (q : Nat)
    (hq : q ∈ active_primes limit) : q.Prime := by
  unfold active_primes at hq
  exact (Finset.mem_filter.mp hq).2

/-! ## The twin pattern -/

private theorem local_survivors_card_two : (local_survivors 2 (by norm_num)).card = 1 := by
  decide

private theorem local_survivors_card (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2) :
    (local_survivors p hp).card = p - 2 := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hne : (0 : ZMod p) ≠ (-2 : ZMod p) := by
    intro heq
    have h2 : (2 : ZMod p) = 0 := by
      have := neg_eq_zero.mp heq.symm
      simpa using this
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (le_antisymm hle hp.two_le)
  have hclogged : Finset.univ.filter (fun n : ZMod p => n = 0 ∨ n = -2) = {0, -2} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
  have hcard2 : ({0, -2} : Finset (ZMod p)).card = 2 := Finset.card_pair hne
  have hcompl : local_survivors p hp
      = Finset.univ \ Finset.univ.filter (fun n : ZMod p => n = 0 ∨ n = -2) := by
    unfold local_survivors
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_or]
  rw [hcompl, hclogged, Finset.card_sdiff, Finset.inter_eq_left.mpr
      (by intro n _; exact Finset.mem_univ n), Finset.card_univ, ZMod.card, hcard2]

private theorem local_survivors_card_eq_two_of_eq (p : Nat) (hp : p.Prime) (h : p = 2) :
    (local_survivors p hp).card = 1 := by
  subst h
  exact local_survivors_card_two

private theorem wheel_survivors_card_eq_prod (h_crt : RNS.CRT.crt_map_bijective)
    (limit : Nat) :
    (wheel_survivors limit).card =
      ∏ q : active_primes limit,
        (local_survivors q.1 (mem_active_primes_is_prime limit q.1 q.2)).card := by
  set e : ZMod (primorial_modulus limit) ≃ (∀ q : active_primes limit, ZMod (q : ℕ)) :=
    Equiv.ofBijective (crt_map limit) (h_crt limit) with he
  have himg : wheel_survivors limit
      = (Fintype.piFinset (fun q : active_primes limit =>
          local_survivors q.1 (mem_active_primes_is_prime limit q.1 q.2))).image e.symm := by
    have hcoe : (e : ZMod (primorial_modulus limit) → ∀ q : active_primes limit, ZMod (q : ℕ))
        = crt_map limit := by
      rw [he]; rfl
    ext n
    unfold wheel_survivors local_survivors
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Fintype.mem_piFinset]
    constructor
    · intro hn
      refine ⟨e n, fun q => ?_, e.symm_apply_apply n⟩
      rw [congrFun hcoe n]
      exact hn q
    · rintro ⟨f, hf, rfl⟩
      intro q
      have hcrt : crt_map limit (e.symm f) = f := by
        rw [← hcoe]
        exact e.apply_symm_apply f
      rw [congrFun hcrt q]
      exact hf q
  rw [himg, Finset.card_image_of_injective _ e.symm.injective, Fintype.card_piFinset]

/-- **Step:** the `CRT` claim implies the twin-pattern survivor count. -/
theorem twin_survivor_count_step (h_crt : RNS.CRT.crt_map_bijective) :
    twin_survivor_count := by
  unfold twin_survivor_count
  intro limit
  rw [wheel_survivors_card_eq_prod h_crt, ← Finset.prod_coe_sort (active_primes limit)
      (fun q => if q = 2 then 1 else q - 2)]
  apply Finset.prod_congr rfl
  intro q _
  by_cases hq2 : (q.1 : ℕ) = 2
  · simp only [hq2]
    exact local_survivors_card_eq_two_of_eq q.1 (mem_active_primes_is_prime limit q.1 q.2) hq2
  · simp only [hq2]
    exact local_survivors_card q.1 (mem_active_primes_is_prime limit q.1 q.2) hq2

/-! ## A general pattern -/

private theorem cast_injOn_range (p : Nat) (hp : 0 < p) :
    Set.InjOn (fun x : ℕ => (x : ZMod p)) {x | x < p} := by
  have : NeZero p := ⟨hp.ne'⟩
  intro a ha b hb hab
  simp only [Set.mem_ofPred_eq] at ha hb
  dsimp only at hab
  have hval : (ZMod.val (a : ZMod p)) = (ZMod.val (b : ZMod p)) := by rw [hab]
  rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at hval

private theorem local_survivors_gen_card (T : Finset Nat) (p : Nat) (hp : p.Prime) :
    (local_survivors_gen T p hp).card = p - w T p := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  have hforbid_eq : Finset.univ.filter (fun n : ZMod p => ∃ t ∈ T, n + (t : ZMod p) = 0)
      = T.image (fun t : ℕ => -(t : ZMod p)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨t, htT, heq⟩
      exact ⟨t, htT, (add_eq_zero_iff_eq_neg.mp heq).symm⟩
    · rintro ⟨t, htT, heq⟩
      exact ⟨t, htT, add_eq_zero_iff_eq_neg.mpr heq.symm⟩
  have himg_card : (T.image (fun t : ℕ => -(t : ZMod p))).card = w T p := by
    have hstep1 : T.image (fun t : ℕ => -(t : ZMod p))
        = (T.image (fun t : ℕ => (t : ZMod p))).image (fun x => -x) := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨t, htT, rfl⟩
        exact ⟨(t : ZMod p), ⟨t, htT, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨t, htT, rfl⟩, rfl⟩
        exact ⟨t, htT, rfl⟩
    have hstep2 : T.image (fun t : ℕ => (t : ZMod p))
        = (T.image (fun t => t % p)).image (fun r : ℕ => (r : ZMod p)) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro t _
      exact (ZMod.natCast_mod t p).symm
    have hinj : Set.InjOn (fun r : ℕ => (r : ZMod p)) ↑(T.image (fun t => t % p)) := by
      apply Set.InjOn.mono _ (cast_injOn_range p hp.pos)
      intro r hr
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hr
      obtain ⟨t, _, rfl⟩ := hr
      exact Nat.mod_lt t hp.pos
    rw [hstep1, hstep2, Finset.card_image_of_injective _ neg_injective,
      Finset.card_image_of_injOn hinj]
    rfl
  have hcompl : local_survivors_gen T p hp
      = Finset.univ \ Finset.univ.filter (fun n : ZMod p => ∃ t ∈ T, n + (t : ZMod p) = 0) := by
    unfold local_survivors_gen
    ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_exists,
      not_and]
  rw [hcompl, hforbid_eq, Finset.card_sdiff, Finset.inter_univ, himg_card, Finset.card_univ,
    ZMod.card]

/-- Survivors on one wheel: rests on no other node. -/
theorem local_survivor_count_holds : local_survivor_count := by
  unfold local_survivor_count
  exact local_survivors_gen_card

private theorem wheel_survivors_gen_card_eq_prod (h_crt : RNS.CRT.crt_map_bijective)
    (T : Finset Nat) (limit : Nat) :
    (wheel_survivors_gen T limit).card =
      ∏ q : active_primes limit,
        (local_survivors_gen T q.1 (mem_active_primes_is_prime limit q.1 q.2)).card := by
  set e : ZMod (primorial_modulus limit) ≃ (∀ q : active_primes limit, ZMod (q : ℕ)) :=
    Equiv.ofBijective (crt_map limit) (h_crt limit) with he
  have himg : wheel_survivors_gen T limit
      = (Fintype.piFinset (fun q : active_primes limit =>
          local_survivors_gen T q.1 (mem_active_primes_is_prime limit q.1 q.2))).image
            e.symm := by
    have hcoe : (e : ZMod (primorial_modulus limit) → ∀ q : active_primes limit, ZMod (q : ℕ))
        = crt_map limit := by
      rw [he]; rfl
    ext n
    unfold wheel_survivors_gen local_survivors_gen
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Fintype.mem_piFinset]
    constructor
    · intro hn
      refine ⟨e n, fun q => ?_, e.symm_apply_apply n⟩
      intro t htT
      rw [congrFun hcoe n]
      exact hn q t htT
    · rintro ⟨f, hf, rfl⟩
      intro q t htT
      have hcrt : crt_map limit (e.symm f) = f := by
        rw [← hcoe]
        exact e.apply_symm_apply f
      rw [congrFun hcrt q]
      exact hf q t htT
  rw [himg, Finset.card_image_of_injective _ e.symm.injective, Fintype.card_piFinset]

/-- **Step:** the `CRT` claim implies the whole-cycle survivor count. -/
theorem general_survivor_count_step (h_crt : RNS.CRT.crt_map_bijective) :
    general_survivor_count := by
  unfold general_survivor_count
  intro T limit
  rw [wheel_survivors_gen_card_eq_prod h_crt, ← Finset.prod_coe_sort (active_primes limit)
      (fun q => q - w T q)]
  apply Finset.prod_congr rfl
  intro q _
  exact local_survivors_gen_card T q.1 (mem_active_primes_is_prime limit q.1 q.2)

end RNS.SurvivorCount

#print axioms RNS.SurvivorCount.twin_survivor_count_step
#print axioms RNS.SurvivorCount.local_survivor_count_holds
#print axioms RNS.SurvivorCount.general_survivor_count_step
