/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# DirichletColumns — both columns hold infinitely many primes

Infinitely many entries of each of the two columns 6n-1 and 6n+1 are prime,
and past any position there is a later prime entry. This is Dirichlet's
theorem on primes in arithmetic progressions, which Mathlib proves, applied to
the two columns.

Proof: `RNSSolutions/DirichletColumns.lean`; rests on no other node (only on
Mathlib's Dirichlet theorem). Metadata: `formalization.yaml`.

Source of record: `rns_sieve_6.lean`, Part I.
-/

namespace RNS.DirichletColumns

/-- **Infinitely many 6n-1 entries are prime.** -/
def col_minus_primes_infinite : Prop :=
  {n : ℕ | (col_minus n).Prime}.Infinite

/-- **Infinitely many 6n+1 entries are prime.** -/
def col_plus_primes_infinite : Prop :=
  {n : ℕ | (col_plus n).Prime}.Infinite

/-- **Past any position, a later 6n-1 entry is prime.** -/
def col_minus_primes_unbounded : Prop :=
  ∀ N : ℕ, ∃ n > N, (col_minus n).Prime

/-- **Past any position, a later 6n+1 entry is prime.** -/
def col_plus_primes_unbounded : Prop :=
  ∀ N : ℕ, ∃ n > N, (col_plus n).Prime

end RNS.DirichletColumns
