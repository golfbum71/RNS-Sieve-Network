/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# Schatunowsky — 30 is the largest number whose survivors are all prime

Treat a number as a cycle: its survivors are the numbers below it that share
no factor with it. For 30 (the cycle of the wheels 2, 3, 5) every survivor
other than 1 is prime: 7, 11, 13, 17, 19, 23, 29. Schatunowsky's theorem
(1893) says no larger number has this property.

The argument is the ceiling. If a prime's square lies below the number and
the prime does not divide it, that square is a survivor and not prime. So
every prime whose square lies below the number must be one of its wheels
(`ceiling_forces_wheels`), and the number is at least the product of those
wheels. Once the wheels reach 7, Bonse's inequality (node `BonseCeiling`)
puts that product above the next ceiling, which is impossible; below that,
the wheels 2, 3, 5 force a multiple of 30, and only 30 itself fits.

Proof: `RNSSolutions/Schatunowsky.lean`. The bound rests on
`BonseCeiling.ceiling_inside_cycle`. Metadata: `formalization.yaml`.
-/

namespace RNS.Schatunowsky

/-- Every survivor of the number `N` other than 1 is prime: each number from 2
up to `N - 1` that shares no factor with `N` is prime. -/
def survivors_all_prime (N : Nat) : Prop :=
  ∀ m : Nat, 1 < m → m < N → Nat.gcd m N = 1 → m.Prime

/-- **The ceiling forces the wheels.** If every survivor of `N` is prime, then
every prime `p` whose square lies below `N` divides `N`. -/
def ceiling_forces_wheels : Prop :=
  ∀ N p : Nat, survivors_all_prime N → p.Prime → p * p < N → p ∣ N

/-- **30 has the property**: every survivor of 30 other than 1 is prime. -/
def thirty_survivors_all_prime : Prop :=
  survivors_all_prime 30

/-- **Schatunowsky's theorem (1893).** A number whose survivors are all prime is
at most 30. -/
def schatunowsky_bound : Prop :=
  ∀ N : Nat, survivors_all_prime N → N ≤ 30

end RNS.Schatunowsky
