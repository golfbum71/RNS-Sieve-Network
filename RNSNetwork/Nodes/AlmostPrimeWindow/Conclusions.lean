/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.AlmostPrime                 -- `Nat.IsSemiprime`
import Mathlib.NumberTheory.ArithmeticFunction.Misc     -- `ArithmeticFunction.cardFactors`

/-!
# AlmostPrimeWindow — survivors between the cutoff and its cube

Take the wheels below a cutoff. Between the cutoff and its square, a number
that no wheel divides is prime (`ShieldCertificates.window_prime_iff`). One
step further, between the cutoff and its cube, a number that no wheel divides
is a prime or a product of exactly two primes: every prime factor is at least
the cutoff, so three of them would already reach the cube. The composite ones
are exactly the products of two primes that are each at least the cutoff.

This is the almost-prime mechanism behind Chen's theorem (a sieve level at the
cube root turns survivors into primes or semiprimes). It also shows exactly
where the parity problem sits for the wheels: in this window a survivor is
prime precisely when its number of prime factors (counted with multiplicity)
is odd, and the wheels alone see no difference between one factor and two.

It generalises `FortunateCeiling.composite_shift_semiprime_below_cube`, which
is the case of a number added to the cycle.

Proof: `RNSSolutions/AlmostPrimeWindow.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.AlmostPrimeWindow

/-- No wheel below the cutoff divides the number. -/
def wheel_free (cutoff n : Nat) : Prop := ∀ q ∈ active_primes cutoff, ¬ q ∣ n

/-- **Prime or semiprime below the cube.** From the cutoff (at least 2) up to
just below its cube, a number no wheel divides is prime or a product of
exactly two primes. -/
def window_almost_prime : Prop :=
  ∀ cutoff n : Nat, 2 ≤ cutoff → cutoff ≤ n → n < cutoff * cutoff * cutoff →
    wheel_free cutoff n → n.Prime ∨ n.IsSemiprime

/-- **The composite survivors of the window.** From the cutoff (at least 2) up
to just below its cube, a number is a composite that no wheel divides exactly
when it is a product of two primes that are each at least the cutoff. -/
def window_composite_iff : Prop :=
  ∀ cutoff n : Nat, 2 ≤ cutoff → cutoff ≤ n → n < cutoff * cutoff * cutoff →
    ((wheel_free cutoff n ∧ ¬ n.Prime) ↔
      ∃ p r : Nat, p.Prime ∧ r.Prime ∧ cutoff ≤ p ∧ cutoff ≤ r ∧ n = p * r)

/-- **Where parity bites.** From the cutoff (at least 2) up to just below its
cube, a number no wheel divides is prime exactly when its number of prime
factors, counted with multiplicity, is odd. -/
def window_prime_iff_odd_factors : Prop :=
  ∀ cutoff n : Nat, 2 ≤ cutoff → cutoff ≤ n → n < cutoff * cutoff * cutoff →
    wheel_free cutoff n → (n.Prime ↔ Odd (ArithmeticFunction.cardFactors n))

end RNS.AlmostPrimeWindow
