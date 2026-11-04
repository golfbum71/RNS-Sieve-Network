/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import RNSNetwork.Vocabulary

/-!
# HardyLittlewood — the conjecture, and what it would give

The Hardy–Littlewood prime k-tuple conjecture says that the count of starting
numbers below a bound that make every member of an admissible offset pattern
prime grows like the Hardy–Littlewood constant times the bound divided by its
logarithm raised to the number of offsets.

**The conjecture is open.** It is stated below precisely, and never claimed:
it appears only as the hypothesis of the one claim this node makes, that the
conjecture for the twin pattern would give infinitely many twin primes.

Proof: `RNSSolutions/HardyLittlewood.lean`, which assumes
`SingularSeries.hardy_littlewood_constant_pos` and
`Admissibility.zero_two_admissible`. Metadata: `formalization.yaml`.

Source of record: `rns_sieve_6.lean`, Part B Step 5 and Lemma 3. The source's
`hardy_littlewood_conjecture` also takes an admissibility proof as an argument
that its body never uses; it is dropped here, so the twin-pattern instance can
be written without a proof term in this file.
-/

namespace RNS.HardyLittlewood

/-- **The Hardy–Littlewood conjecture** for an offset pattern (open, never
claimed): the actual count of prime patterns below the bound is
asymptotically equivalent to the predicted main term. -/
def hardy_littlewood_conjecture (T : Finset Nat) : Prop :=
  Asymptotics.IsEquivalent Filter.atTop
    (fun N => (actual_tuple_count T N : Real))
    (fun N => hardy_littlewood_main_term T N)

/-- **The conjecture would give infinitely many twin primes.** If the
Hardy–Littlewood conjecture holds for the twin pattern {0, 2}, then there are
infinitely many primes whose successor-but-one is also prime. -/
def twin_prime_conjecture_implies_infinite_twin_primes : Prop :=
  hardy_littlewood_conjecture ({0, 2} : Finset Nat) →
    {n : ℕ | n.Prime ∧ (n + 2).Prime}.Infinite

end RNS.HardyLittlewood
