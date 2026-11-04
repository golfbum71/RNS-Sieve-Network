/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SingularSeries.Conclusions
import RNSNetwork.Nodes.TwinConstant.Conclusions

/-!
# Proof for TwinConstant

Imports claims only, never other nodes' proofs. The conclusion is proved as
a step from the claim `SingularSeries.factor_multipliable`, taken as the
hypothesis `h_mult`; `RNSSolutions/Assemble.lean` plugs in the finished proof.

Tactic proof: from `twin_prime_constant_eq_classical` and its helpers in
`rns_sieve_6.lean` (Bonus section and Part B Step 3 testbed), with the call
to the product's convergence replaced by `h_mult`.

Idea: the wheel of size 2 contributes exactly the factor 2; every odd wheel
contributes exactly one minus one over (its size minus one) squared; so
splitting the product at 2 gives the classical form.
-/

namespace RNS.TwinConstant

private theorem w_eq_card_of_lt (T : Finset Nat) (p : Nat) (hT : ∀ t ∈ T, t < p) :
    w T p = T.card := by
  unfold w
  have himg : T.image (fun t => t % p) = T := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨t, htT, rfl⟩
      rwa [Nat.mod_eq_of_lt (hT t htT)]
    · intro hx
      exact ⟨x, hx, Nat.mod_eq_of_lt (hT x hx)⟩
  rw [himg]

private noncomputable def singular_series_delta (T : Finset Nat) (p : Nat) : Real :=
  singular_series_factor T p - 1

private theorem factor_eq_one_add (T : Finset Nat) (p : Nat) :
    singular_series_factor T p = 1 + singular_series_delta T p := by
  unfold singular_series_delta
  ring

private theorem w_twin_eq_two (p : Nat) (hp2 : 2 < p) :
    w ({0, 2} : Finset Nat) p = 2 := by
  have hlt : ∀ t ∈ ({0, 2} : Finset Nat), t < p := by
    intro t ht
    fin_cases ht <;> omega
  have hcard : ({0, 2} : Finset Nat).card = 2 := by decide
  rw [w_eq_card_of_lt _ p hlt, hcard]

private theorem delta_eq_twin (p : Nat) (hp2 : 2 < p) :
    singular_series_delta ({0, 2} : Finset Nat) p = -1 / ((p : Real) - 1) ^ 2 := by
  have hcard : ({0, 2} : Finset Nat).card = 2 := by decide
  have hw := w_twin_eq_two p hp2
  unfold singular_series_delta singular_series_factor
  rw [hcard, hw]
  have hpR : (2 : Real) < (p : Real) := by exact_mod_cast hp2
  have hden_ne : ((p : Real) - 1) ≠ 0 := by linarith
  push_cast
  field_simp
  ring

private theorem singular_series_factor_two_eq_two :
    singular_series_factor ({0, 2} : Finset Nat) 2 = 2 := by
  have hw : w ({0, 2} : Finset Nat) 2 = 1 := by decide
  unfold singular_series_factor
  rw [hw]
  norm_num

private theorem singular_series_factor_odd_eq_classical (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    singular_series_factor ({0, 2} : Finset Nat) (p : ℕ)
      = 1 - 1 / (((p : ℕ) : Real) - 1) ^ 2 := by
  have hgt : 2 < (p : ℕ) := lt_of_le_of_ne p.2.two_le (Ne.symm hp2)
  rw [factor_eq_one_add, delta_eq_twin (p : ℕ) hgt]
  ring

private theorem hasProd_update_one (f : Nat.Primes → ℝ) (p₂ : Nat.Primes) (a : ℝ)
    (hf : HasProd f a) (hne : f p₂ ≠ 0) :
    HasProd (Function.update f p₂ 1) (a / f p₂) := by
  unfold HasProd SummationFilter.unconditional at hf ⊢
  have heq : (fun s : Finset Nat.Primes => ∏ p ∈ s, Function.update f p₂ 1 p)
      =ᶠ[Filter.atTop] (fun s : Finset Nat.Primes => (∏ p ∈ s, f p) / f p₂) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨{s : Finset Nat.Primes | p₂ ∈ s}, ?_, ?_⟩
    · rw [Filter.mem_atTop_sets]
      exact ⟨{p₂}, fun s hs => hs (Finset.mem_singleton_self p₂)⟩
    · intro s hp2s
      dsimp only
      simp only [Set.mem_ofPred_eq] at hp2s
      rw [← Finset.prod_erase_mul s (Function.update f p₂ 1) hp2s,
          ← Finset.prod_erase_mul s f hp2s, Function.update_self]
      have herase : ∀ p ∈ s.erase p₂, Function.update f p₂ 1 p = f p := fun p hp =>
        Function.update_of_ne (Finset.ne_of_mem_erase hp) 1 f
      rw [Finset.prod_congr rfl herase, mul_one]
      field_simp
  have hlim : Filter.Tendsto (fun s : Finset Nat.Primes => (∏ p ∈ s, f p) / f p₂)
      Filter.atTop (nhds (a / f p₂)) := hf.div_const (f p₂)
  exact hlim.congr' heq.symm

/-- **Step:** convergence of the correction product implies that the twin
constant equals the classical one. -/
theorem twin_prime_constant_eq_classical_step
    (h_mult : RNS.SingularSeries.factor_multipliable) :
    twin_prime_constant_eq_classical := by
  unfold twin_prime_constant_eq_classical
  set T : Finset Nat := ({0, 2} : Finset Nat) with hTdef
  set f : Nat.Primes → ℝ := fun p => singular_series_factor T p with hfdef
  set p₂ : Nat.Primes := ⟨2, Nat.prime_two⟩ with hp2def
  have hk : 1 ≤ T.card := by rw [hTdef]; decide
  have hf2 : f p₂ = 2 := by
    rw [hfdef]; exact singular_series_factor_two_eq_two
  have hf2ne : f p₂ ≠ 0 := by rw [hf2]; norm_num
  have hHP : HasProd f (hardy_littlewood_constant T) := (h_mult T hk).hasProd
  have hupd : HasProd (Function.update f p₂ 1) (hardy_littlewood_constant T / f p₂) :=
    hasProd_update_one f p₂ (hardy_littlewood_constant T) hHP hf2ne
  set g : {q : Nat.Primes // (q : ℕ) ≠ 2} → Nat.Primes := Subtype.val with hgdef
  have hginj : Function.Injective g := Subtype.val_injective
  have hcond : ∀ x ∉ Set.range g, Function.update f p₂ 1 x = 1 := by
    intro x hx
    have hx2 : (x : ℕ) = 2 := by
      by_contra hne
      exact hx ⟨⟨x, hne⟩, rfl⟩
    have hxp2 : x = p₂ := Subtype.ext hx2
    rw [hxp2]
    exact Function.update_self p₂ 1 f
  have hiff := hginj.hasProd_iff (f := Function.update f p₂ 1)
      (a := hardy_littlewood_constant T / f p₂) hcond
  have hHPsub : HasProd ((Function.update f p₂ 1) ∘ g) (hardy_littlewood_constant T / f p₂) :=
    hiff.mpr hupd
  have heq_on_sub : ((Function.update f p₂ 1) ∘ g) = (f ∘ g) := by
    funext q
    have hqne2 : (q : ℕ) ≠ 2 := q.2
    have hqnep2 : (g q) ≠ p₂ := by
      intro h
      apply hqne2
      have hval : (g q : ℕ) = (p₂ : ℕ) := congrArg Subtype.val h
      simpa [hgdef, hp2def] using hval
    show Function.update f p₂ 1 (g q) = f (g q)
    exact Function.update_of_ne hqnep2 1 f
  rw [heq_on_sub] at hHPsub
  have htprod_eq : ∏' q : {q : Nat.Primes // (q : ℕ) ≠ 2}, f (g q)
      = hardy_littlewood_constant T / f p₂ := hHPsub.tprod_eq
  have hterms_eq : ∏' q : {q : Nat.Primes // (q : ℕ) ≠ 2}, f (g q)
      = ∏' q : {q : Nat.Primes // (q : ℕ) ≠ 2},
          (1 - 1 / (((q : Nat.Primes) : ℕ) - 1 : Real) ^ 2) := by
    apply tprod_congr
    intro q
    show f q.1 = _
    rw [hfdef]
    exact singular_series_factor_odd_eq_classical q.1 q.2
  rw [hterms_eq] at htprod_eq
  unfold twin_prime_classical_constant
  rw [htprod_eq, hf2]
  ring

end RNS.TwinConstant

#print axioms RNS.TwinConstant.twin_prime_constant_eq_classical_step
