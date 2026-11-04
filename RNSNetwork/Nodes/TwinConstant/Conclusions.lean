/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# TwinConstant — the classical twin-prime constant is recovered

For the twin pattern, the constant built from the wheels equals the textbook
value: 2 times the product, over the odd primes, of one minus one over (the
prime minus one) squared.

Proof: `RNSSolutions/TwinConstant.lean`, which assumes
`SingularSeries.factor_multipliable` and nothing else. Metadata:
`formalization.yaml`.

Source of record: `rns_sieve_6.lean`, Bonus section
(`twin_prime_classical_constant`, `twin_prime_constant_eq_classical`).
-/

namespace RNS.TwinConstant

/-- The classical closed form of the twin-prime constant, about 1.3203:
2 times the product over the odd primes of one minus one over (the prime
minus one) squared. Defined here rather than in the Vocabulary because only
this node uses it. -/
noncomputable def twin_prime_classical_constant : Real :=
  2 * ∏' p : {q : Nat.Primes // (q : ℕ) ≠ 2},
    (1 - 1 / (((p : Nat.Primes) : ℕ) - 1 : Real) ^ 2)

/-- **The wheel-built constant is the classical one.** The Hardy–Littlewood
constant of the twin pattern {0, 2} equals the classical twin-prime
constant. -/
def twin_prime_constant_eq_classical : Prop :=
  hardy_littlewood_constant ({0, 2} : Finset Nat) = twin_prime_classical_constant

end RNS.TwinConstant
