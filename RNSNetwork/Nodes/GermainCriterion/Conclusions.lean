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

The "if" half (`two_wheel_split_of_remainders`) needs no characters: it is
remainder arithmetic in the signed sum of
`Sawtooth.even_split_iff_remainders_cancel`. The "only if" half
(`two_wheel_remainders_of_split`, Erdős's conjecture) follows Germain: the
character transform, his Proposition 3.1 and Corollary 3.2, his Proposition
2.1 (c)-(e), his Theorem 1.1 for distinct prime wheels with a wheel not
dividing the number of parts (`germain_theorem`), and character separation
through odd characters. Both halves together: `two_wheel_split_iff`.

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

/-- **The character transform of the remainder sum.** Take prime wheels `W`,
none dividing the number of parts `k`, and any Dirichlet character `χ` for
`k`. Weight `Sawtooth`'s signed remainder sum (with `a` the residue `j`) by the
conjugate character `χ⁻¹ j` and add over all residues `j`. The result is the
product over the wheels of `χ(wheel) - 1`, times the residue sum weighted by
`χ⁻¹`. This is Germain's (3.1) in remainder form; the sawtooth's `-1/2` is not
needed. -/
def character_transform : Prop :=
  ∀ (k : Nat) [NeZero k] (W : Finset Nat) (χ : DirichletCharacter ℂ k),
    (∀ p ∈ W, p.Prime) → (∀ p ∈ W, ¬ p ∣ k) →
    ∑ j : ZMod k, χ⁻¹ j * (((∑ S ∈ W.powerset,
        (-1 : Int) ^ S.card * ((j.val * (W \ S).prod id % k : Nat) : Int) : Int)) : ℂ)
      = (∏ p ∈ W, (χ (p : ZMod k) - 1)) * ∑ i : ZMod k, χ⁻¹ i * (i.val : ℂ)

/-- **The weighted residue sum is a value of the L-function.** For a modulus
`N` other than 1 and a nontrivial Dirichlet character `ψ` modulo `N`, the sum
of each residue weighted by `ψ` equals `-N` times `L(ψ, 0)`. -/
def weighted_sum_eq_LFunction_zero : Prop :=
  ∀ (N : Nat) [NeZero N] (ψ : DirichletCharacter ℂ N), N ≠ 1 → ψ ≠ 1 →
    ∑ j : ZMod N, ψ j * (j.val : ℂ) = -(N : ℂ) * DirichletCharacter.LFunction ψ 0

/-- **When the weighted residue sum of an odd character vanishes** (Germain's
(3.2)). For any odd Dirichlet character `ψ` modulo `k`, primitive or not, the
sum of each residue weighted by `ψ` is nonzero exactly when the primitive
character behind `ψ` differs from 1 at every prime dividing `k`. -/
def odd_weighted_sum_ne_zero_iff : Prop :=
  ∀ (k : Nat) [NeZero k] (ψ : DirichletCharacter ℂ k), ψ.Odd →
    (∑ j : ZMod k, ψ j * (j.val : ℂ) ≠ 0 ↔
      ∀ p ∈ k.primeFactors, ψ.primitiveCharacter (p : ZMod ψ.conductor) ≠ 1)

/-- **Germain's Proposition 3.1, in remainder form.** For a nonempty set of
prime wheels `W`, none dividing the number of parts `k`: `Sawtooth`'s signed
remainder sum vanishes at every residue coprime to `k` (equivalently, by
`Sawtooth`, the survivors split evenly there) exactly when every odd Dirichlet
character `χ` modulo `k` either equals 1 at some wheel, or has the primitive
character behind `χ⁻¹` equal to 1 at some prime dividing `k`. -/
def coprime_split_iff_characters : Prop :=
  ∀ (k : Nat) [NeZero k] (W : Finset Nat), W.Nonempty → (∀ p ∈ W, p.Prime) →
    (∀ p ∈ W, ¬ p ∣ k) →
    ((∀ j : ZMod k, IsUnit j →
        ∑ S ∈ W.powerset, (-1 : Int) ^ S.card * ((j.val * (W \ S).prod id % k : Nat) : Int) = 0) ↔
      ∀ χ : DirichletCharacter ℂ k, χ.Odd →
        (∃ p ∈ W, χ (p : ZMod k) = 1) ∨
        (∃ p ∈ k.primeFactors, χ⁻¹.primitiveCharacter (p : ZMod χ⁻¹.conductor) = 1))

/-- **Germain's Corollary 3.2, in remainder form: every residue, wheels only.**
For a nonempty set of prime wheels `W`, none dividing the number of parts `k`:
`Sawtooth`'s signed remainder sum vanishes at every starting residue (so, by
`Sawtooth`, the survivors split evenly whatever the residue) exactly when every
odd Dirichlet character modulo `k` equals 1 at some wheel. -/
def all_residues_split_iff_wheels : Prop :=
  ∀ (k : Nat) [NeZero k] (W : Finset Nat), W.Nonempty → (∀ p ∈ W, p.Prime) →
    (∀ p ∈ W, ¬ p ∣ k) →
    ((∀ a : Nat,
        ∑ S ∈ W.powerset, (-1 : Int) ^ S.card * ((a * (W \ S).prod id % k : Nat) : Int) = 0) ↔
      ∀ χ : DirichletCharacter ℂ k, χ.Odd → ∃ p ∈ W, χ (p : ZMod k) = 1)

/-! ## Germain's Proposition 2.1: adding and removing wheels

Germain's parts (a) and (b) concern a cycle with a repeated prime; the
network's cycle is always a product of distinct wheels, so they do not arise.
Parts (c), (d) and (e) are stated below in remainder form. -/

/-- **The survivors of the wheels `W` split evenly into `k` parts, in remainder
form**: `Sawtooth`'s signed remainder sum vanishes at every starting residue
`a`. By `Sawtooth.even_split_iff_remainders_cancel` this is the even split. -/
def remainders_cancel (W : Finset Nat) (k : Nat) : Prop :=
  ∀ a : Nat, ∑ S ∈ W.powerset, (-1 : Int) ^ S.card * ((a * (W \ S).prod id % k : Nat) : Int) = 0

/-- **Adding a wheel keeps an even split** (Germain's Proposition 2.1 (c)). If
the survivors of `W` split evenly into `k` parts, so do the survivors of `W`
with one more wheel `q`. No primality is needed. -/
def split_add_wheel : Prop :=
  ∀ (W : Finset Nat) (k q : Nat), q ∉ W → remainders_cancel W k → remainders_cancel (insert q W) k

/-- **Fewer parts** (Germain's Proposition 2.1 (d)). An even split into `k`
parts gives an even split into `h` parts for every `h` dividing `k`. -/
def split_fewer_parts : Prop :=
  ∀ (W : Finset Nat) (k h : Nat), 0 < k → h ∣ k → remainders_cancel W k → remainders_cancel W h

/-- **Removing a wheel that divides the number of parts keeps an even split**
(Germain's Proposition 2.1 (e)). For prime wheels `W`, a prime `p` not among
them dividing the number of parts `k`, and `W` not empty: if the survivors of
`W` with `p` added split evenly into `k` parts, so do the survivors of `W`. -/
def split_remove_dividing_wheel : Prop :=
  ∀ (W : Finset Nat) (k p : Nat), (∀ q ∈ W, q.Prime) → p.Prime → p ∉ W → W.Nonempty → 0 < k →
    p ∣ k → remainders_cancel (insert p W) k → remainders_cancel W k

/-- **The exception to Germain's Theorem 1.1.** The single wheel 2 does not
split evenly into 2 parts, yet there is no odd character modulo 2, so
Germain's criterion ("every odd character equals 1 at some wheel") holds
vacuously. His Theorem 1.1 as printed fails here (and for the empty cycle);
the network's form of it asks for at least one wheel not dividing the number
of parts. -/
def two_parts_exception : Prop :=
  ¬ remainders_cancel {2} 2 ∧ ∀ χ : DirichletCharacter ℂ 2, ¬ χ.Odd

/-! ## Germain's Theorem 1.1 -/

/-- **Only the wheels not dividing the number of parts matter.** For prime
wheels `W`, at least one of them not dividing `k`: the survivors of `W` split
evenly into `k` parts exactly when the survivors of the wheels of `W` that do
not divide `k` do. (Remove the dividing wheels one at a time with
Proposition 2.1 (e); put them back with (c).) -/
def split_iff_nondividing_wheels : Prop :=
  ∀ (W : Finset Nat) (k : Nat), 0 < k → (∀ p ∈ W, p.Prime) → (∃ p ∈ W, ¬ p ∣ k) →
    (remainders_cancel W k ↔ remainders_cancel (W.filter (fun p => ¬ p ∣ k)) k)

/-- **Germain's Theorem 1.1, for distinct prime wheels.** For prime wheels `W`,
at least one of them not dividing the number of parts `k`: for every `a`, the
survivors up to `a` `k`-ths of the cycle are exactly `a` shares of the cycle's
survivors (the survivors split evenly into `k` parts) exactly when every odd
Dirichlet character modulo `k` equals 1 at some wheel. Without a wheel not
dividing `k` this can fail: see `two_parts_exception`. -/
def germain_theorem : Prop :=
  ∀ (k : Nat) [NeZero k] (W : Finset Nat), (∀ p ∈ W, p.Prime) → (∃ p ∈ W, ¬ p ∣ k) →
    ((∀ a : Nat, k * (survivors_upto W (a * W.prod id / k)).card
        = a * (survivors_upto W (W.prod id)).card) ↔
      ∀ χ : DirichletCharacter ℂ k, χ.Odd → ∃ p ∈ W, χ (p : ZMod k) = 1)

/-! ## Two wheels: Erdős's conjecture and Germain's Corollary 1.4 -/

/-- **Character separation through odd characters.** For a residue `u` that is
a unit modulo `k`: if every odd Dirichlet character modulo `k` equals 1 at `u`,
then `u` is 1. (Every even character is a fixed odd one times an odd one; and
modulo 1 or 2, where no odd character exists, the only unit is 1.) -/
def eq_one_of_odd_characters : Prop :=
  ∀ (k : Nat) [NeZero k] (u : ZMod k), IsUnit u →
    (∀ χ : DirichletCharacter ℂ k, χ.Odd → χ u = 1) → u = 1

/-- **Erdős's conjecture on Lehmer's even split** (proved by Hall and Shiu,
2002; here by Germain's route, his Corollary 1.4 proof (ii)). For two different
prime wheels `p` and `q` and a number of equal parts `k`: if the survivors
split evenly into `k` parts, then `p` or `q` leaves remainder 1 on division by
`k`, or `p` times `p` leaves remainder 1 and `p` plus `q` is a multiple of
`k`. -/
def two_wheel_remainders_of_split : Prop :=
  ∀ p q k : Nat, p.Prime → q.Prime → p ≠ q → 0 < k →
    (∀ a : Nat, k * (survivors_upto {p, q} (a * ({p, q} : Finset Nat).prod id / k)).card
      = a * (survivors_upto {p, q} (({p, q} : Finset Nat).prod id)).card) →
    (p % k = 1 % k ∨ q % k = 1 % k ∨ ((p * p) % k = 1 % k ∧ (p + q) % k = 0))

/-- **Germain's Corollary 1.4: the two-wheel even split, exactly.** For two
different prime wheels `p` and `q` and a number of equal parts `k`: the
survivors split evenly into `k` parts exactly when `p` or `q` leaves remainder
1 on division by `k`, or `p` times `p` leaves remainder 1 and `p` plus `q` is a
multiple of `k`. -/
def two_wheel_split_iff : Prop :=
  ∀ p q k : Nat, p.Prime → q.Prime → p ≠ q → 0 < k →
    ((∀ a : Nat, k * (survivors_upto {p, q} (a * ({p, q} : Finset Nat).prod id / k)).card
      = a * (survivors_upto {p, q} (({p, q} : Finset Nat).prod id)).card) ↔
    (p % k = 1 % k ∨ q % k = 1 % k ∨ ((p * p) % k = 1 % k ∧ (p + q) % k = 0)))

end RNS.GermainCriterion
