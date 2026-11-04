/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# SquareRootShield — trial division only needs the small wheels

Below a ceiling, a number is prime exactly when no prime at or below the
square root of the ceiling divides it (other than the number itself). This
is what turns the wheel into a sieve: whatever survives the small wheels
below the ceiling is certified prime.

Proof: `RNSSolutions/SquareRootShield.lean`. Metadata: `formalization.yaml`.
Source of record: `rns_sieve_6.lean`, Part A, Step 5 (`square_root_shield`).
The source states the right-hand side through two private helpers,
`shield_radius` and `has_small_proper_prime_factor`; here they are written
out in full, with the same meaning.
-/

namespace RNS.SquareRootShield

/-- **The square-root shield.** For every ceiling and every number from 2 up
to that ceiling: the number is prime exactly when it has no prime factor
that is smaller than itself and at most the (whole-number) square root of
the ceiling. -/
def square_root_shield : Prop :=
  ∀ X x : Nat, 2 ≤ x → x ≤ X →
    (x.Prime ↔ ¬ ∃ p, p.Prime ∧ p ∣ x ∧ p < x ∧ p ≤ Nat.sqrt X)

end RNS.SquareRootShield
