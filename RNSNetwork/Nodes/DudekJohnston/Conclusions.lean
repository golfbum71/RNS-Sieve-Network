/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.Data.Nat.Factors          -- `Nat.primeFactorsList`
import RNSNetwork.Vocabulary

/-!
# DudekJohnston — a near-prime between every pair of squares

Between every two consecutive squares there is a number with at most four
prime factors, counted with repetition. This is a proven, published weakening
of Legendre's conjecture, which asks for a prime there.

Source: Adrian W. Dudek and Daniel R. Johnston, *Almost primes between all
squares*, arXiv:2501.18048 (2025), Theorem 1.2.

**This node is cited, not proved in Lean.** The statement below is precise;
its justification is the paper, recorded in `formalization.yaml`. There is
deliberately no proof file and no `sorry`: the network records what the claim
rests on (a published proof) instead of pretending to have checked it.

Source of record: `dudek_johnston_rns.lean`.
-/

namespace RNS.DudekJohnston

/-- The number of prime factors of a number, counted with repetition. Defined
here because only this node uses it. -/
def primeOmega (n : Nat) : Nat := n.primeFactorsList.length

/-- **Dudek–Johnston, Theorem 1.2** (cited): for every n from 1 on, some number
strictly between n² and (n + 1)² has at most four prime factors, counted with
repetition. -/
def dudek_johnston_statement : Prop :=
  ∀ n : Nat, 1 ≤ n → ∃ a, n ^ 2 < a ∧ a < (n + 1) ^ 2 ∧ primeOmega a ≤ 4

end RNS.DudekJohnston
