/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Data.ZMod.QuotientRing          -- `ZMod.prodEquivPi` (Chinese Remainder)
import Mathlib.Algebra.Ring.Pi                 -- `Pi.evalRingHom`
import Mathlib.Data.Nat.Prime.Basic            -- `Nat.coprime_primes`
import RNSNetwork.Nodes.CRT.Conclusions

/-!
# Proof for CRT

Proves `RNS.CRT.crt_map_bijective`. The tactic proof is the one from
`crtMapBijective` in the `HardyLittlewood` repository (already compiled on
this Lean version), renamed back to the `rns_sieve_6.lean` names.

Idea: the active primes are pairwise coprime, so Mathlib's Chinese Remainder
ring isomorphism `ZMod.prodEquivPi` identifies remainders modulo their product
with tuples of remainders modulo each one; `crt_map` agrees with that
isomorphism coordinate by coordinate, so it is a bijection too.
-/

namespace RNS.CRT

private theorem mem_active_primes_is_prime (limit : Nat) (q : Nat)
    (hq : q ∈ active_primes limit) : q.Prime := by
  unfold active_primes at hq
  exact (Finset.mem_filter.mp hq).2

private theorem active_prime_dvd_primorial_modulus (limit : Nat) (q : Nat)
    (hq : q ∈ active_primes limit) : q ∣ primorial_modulus limit := by
  unfold primorial_modulus
  exact Finset.dvd_prod_of_mem id hq

theorem crt_map_bijective_holds : crt_map_bijective := by
  unfold crt_map_bijective
  intro limit
  have hcoprime :
      Pairwise (Function.onFun Nat.Coprime (fun q : active_primes limit => (q : ℕ))) := by
    intro q q' hne
    have hqp : (q : ℕ).Prime := mem_active_primes_is_prime limit q q.2
    have hqp' : (q' : ℕ).Prime := mem_active_primes_is_prime limit q' q'.2
    have hneq : (q : ℕ) ≠ (q' : ℕ) := fun h => hne (Subtype.ext h)
    exact (Nat.coprime_primes hqp hqp').mpr hneq
  have hprodeq : (∏ q : active_primes limit, (q : ℕ)) = primorial_modulus limit := by
    unfold primorial_modulus
    exact Finset.prod_coe_sort (active_primes limit) id
  have E : ZMod (primorial_modulus limit) ≃+* (∀ q : active_primes limit, ZMod (q : ℕ)) := by
    rw [← hprodeq]
    exact ZMod.prodEquivPi (fun q : active_primes limit => (q : ℕ)) hcoprime
  have hfun_eq : crt_map limit
      = (E : ZMod (primorial_modulus limit) → ∀ q : active_primes limit, ZMod (q : ℕ)) := by
    funext n
    funext q
    have hring_eq :
        ZMod.castHom (active_prime_dvd_primorial_modulus limit q q.2) (ZMod (q : ℕ))
          = (Pi.evalRingHom (fun q : active_primes limit => ZMod (q : ℕ)) q).comp
              E.toRingHom := by
      apply Subsingleton.elim
    change (ZMod.castHom (active_prime_dvd_primorial_modulus limit q q.2) (ZMod (q : ℕ))) n
      = E n q
    calc (ZMod.castHom (active_prime_dvd_primorial_modulus limit q q.2) (ZMod (q : ℕ))) n
        = ((Pi.evalRingHom (fun q : active_primes limit => ZMod (q : ℕ)) q).comp
            E.toRingHom) n := by
          rw [hring_eq]
      _ = E n q := by simp [Pi.evalRingHom_apply]
  rw [hfun_eq]
  exact E.bijective

end RNS.CRT

#print axioms RNS.CRT.crt_map_bijective_holds
