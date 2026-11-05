/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# GermainCriterion — when the survivors of two wheels split evenly

Freeze two prime wheels and cut their combined cycle into a given number of
equal parts. The survivors split evenly when every part holds the same share.
Germain (2005) gave the exact rule: for two wheels, the split is even exactly
when one wheel leaves remainder 1 on division by the number of parts, or the
first wheel's square leaves remainder 1 and the second wheel leaves the
negative of the first. Erdős's conjecture on Lehmer's even split (proved by
Hall and Shiu, 2002) is the "only if" half of this rule.

This file states the "if" half (`two_wheel_split_of_remainders`), which needs
no characters: it is remainder arithmetic in the signed sum of
`Sawtooth.even_split_iff_remainders_cancel`. The "only if" half needs odd
Dirichlet characters and the nonvanishing of their L-functions at 1, and is
the next stage of this node.

Proof: `RNSSolutions/GermainCriterion.lean`. Rests on `Sawtooth`.
Metadata: `formalization.yaml`.
-/

namespace RNS.GermainCriterion

/-- **The two-wheel even split, sufficient direction.** For two different
prime wheels `p` and `q` and a number of equal parts `k`: if `p` or `q` leaves
remainder 1 on division by `k`, or `p` times `p` leaves remainder 1 and `p`
plus `q` is a multiple of `k`, then for every `a` the survivors up to `a`
`k`-ths of the cycle are exactly `a` shares of the cycle's survivors. -/
def two_wheel_split_of_remainders : Prop :=
  ∀ p q k a : Nat, p.Prime → q.Prime → p ≠ q → 0 < k →
    (p % k = 1 % k ∨ q % k = 1 % k ∨ ((p * p) % k = 1 % k ∧ (p + q) % k = 0)) →
    k * (survivors_upto {p, q} (a * ({p, q} : Finset Nat).prod id / k)).card
      = a * (survivors_upto {p, q} (({p, q} : Finset Nat).prod id)).card

/-- **An odd primitive character's L-function does not vanish at 0.** For a
modulus `N` and an odd primitive Dirichlet character `χ` modulo `N`,
`L(χ, 0) ≠ 0`. From Mathlib: the functional equation, the nonvanishing of
`L(χ⁻¹, 1)`, and the root number and gamma factors being nonzero. -/
def odd_primitive_LFunction_zero_ne_zero : Prop :=
  ∀ (N : Nat) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ.Odd →
    DirichletCharacter.LFunction χ 0 ≠ 0

/-- **The weighted residue sum of an odd primitive character is not zero.**
Adding up each residue of the cycle `N`, weighted by an odd primitive character
`χ`, never gives 0. This is the quantity Germain's criterion is built from. -/
def odd_primitive_weighted_sum_ne_zero : Prop :=
  ∀ (N : Nat) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ.Odd →
    ∑ j : ZMod N, χ j * (j.val : ℂ) ≠ 0

end RNS.GermainCriterion
