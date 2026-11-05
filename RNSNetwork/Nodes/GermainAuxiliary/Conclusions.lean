/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# GermainAuxiliary — Sophie Germain's theorem with any suitable wheel

Sophie Germain's own general form of her theorem. Fix an odd prime exponent
`p` and look for a prime wheel size `q` with two properties:

* **no neighbouring powers**: on the wheel of size `q`, no two positions
  reached by `p`-th powers of unblocked numbers sit next to each other
  (no `a^p = 1 + b^p` with `a, b` not at 0);
* **`p` is not a power position**: the position of `p` itself on that wheel
  is not reached by any `p`-th power.

Such a `q` is an *auxiliary prime* for `p`. If one exists, then
`x^p + y^p + z^p = 0` forces `p` to divide `x y z`: the first case of
Fermat's Last Theorem holds for `p`.

The wheel of size `2p + 1` is auxiliary whenever `p` is a Sophie Germain
prime (node `SophieGermainPowers`: its `p`-th power positions are only 0, 1,
-1), which recovers node `SophieGermainTheorem`. But auxiliary wheels exist
for other exponents too: 7 is not a Sophie Germain prime (15 is not prime),
yet the wheel of size 29 is auxiliary for it, and the wheel of size 53 for
13. Each is a finite check of one wheel, done here by Lean's kernel; it
gives the first case of Fermat's Last Theorem for that exponent.

Germain found an auxiliary prime for every odd prime below 100 (Legendre,
1823). The definitions follow Ballenghien's Isabelle formalization, stated as
wheel positions.

Proof: `RNSSolutions/GermainAuxiliary.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.GermainAuxiliary

/-- **No neighbouring powers** on the wheel of size `q`: no two `p`-th powers of
unblocked positions sit next to each other. -/
def no_neighbouring_powers (p q : Nat) : Prop :=
  ∀ a b : ZMod q, a ≠ 0 → b ≠ 0 → a ^ p ≠ 1 + b ^ p

/-- **`p` is not a power position** on the wheel of size `q`: no `p`-th power
sits where `p` does. -/
def p_not_power_position (p q : Nat) : Prop :=
  ∀ a : ZMod q, a ^ p ≠ (p : ZMod q)

/-- An **auxiliary prime** `q` for the exponent `p`. -/
def auxiliary_prime (p q : Nat) : Prop :=
  p.Prime ∧ q.Prime ∧ no_neighbouring_powers p q ∧ p_not_power_position p q

/-- **Germain's general theorem.** For an odd prime `p` with an auxiliary
prime `q`, any integer solution of `x^p + y^p + z^p = 0` has `p` dividing
`x y z`. -/
def auxiliary_prime_theorem : Prop :=
  ∀ p q : Nat, p ≠ 2 → auxiliary_prime p q → ∀ x y z : Int,
    x ^ p + y ^ p + z ^ p = 0 → (p : Int) ∣ x * y * z

/-- **Sophie Germain primes give auxiliary primes.** For an odd prime `p` with
`2p + 1` prime, the wheel of size `2p + 1` is auxiliary for `p`. -/
def sophie_germain_wheel_auxiliary : Prop :=
  ∀ p : Nat, p.Prime → p ≠ 2 → (2 * p + 1).Prime → auxiliary_prime p (2 * p + 1)

/-- **The wheel of size 29 is auxiliary for 7.** -/
def auxiliary_seven : Prop := auxiliary_prime 7 29

/-- **The wheel of size 53 is auxiliary for 13.** -/
def auxiliary_thirteen : Prop := auxiliary_prime 13 53

/-- **Fermat's first case for the exponent 7.** -/
def fermat_first_case_seven : Prop :=
  ∀ x y z : Int, x ^ 7 + y ^ 7 = z ^ 7 → (7 : Int) ∣ x * y * z

/-- **Fermat's first case for the exponent 13.** -/
def fermat_first_case_thirteen : Prop :=
  ∀ x y z : Int, x ^ 13 + y ^ 13 = z ^ 13 → (13 : Int) ∣ x * y * z

end RNS.GermainAuxiliary
