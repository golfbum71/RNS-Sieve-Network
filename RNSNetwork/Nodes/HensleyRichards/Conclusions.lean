/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib.NumberTheory.PrimeCounting
import RNSNetwork.Vocabulary

/-!
# HensleyRichards — Hardy and Littlewood's two conjectures clash

Hardy and Littlewood (1923) proposed Conjecture A, that every admissible
offset pattern is realized as simultaneous primes infinitely often, and
Conjecture B, that the prime-counting function is subadditive. Hensley and
Richards (1973/74) showed the two cannot both hold, given an admissible
pattern that packs more offsets into a window than there are primes in a
window of that length (their example has 447 offsets in a window of length
3159, against 446 primes up to 3159).

**Both conjectures are open.** This node states them and claims only the
conditional incompatibility, given such a pattern. Exhibiting the explicit
447-offset pattern is not part of this node.

Proof: `RNSSolutions/HensleyRichards.lean`; rests on no other node.
Metadata: `formalization.yaml`.

Source of record: `rns_sieve_6_parts_J_K.lean`, Part J.
-/

namespace RNS.HensleyRichards

/-- **Hardy–Littlewood Conjecture A** (open, never claimed): every nonempty
admissible offset pattern is realized as simultaneous primes infinitely
often. -/
def HL_conjecture_A : Prop :=
  ∀ T : Finset Nat, T.Nonempty → is_admissible T →
    {n : Nat | ∀ t ∈ T, (n + t).Prime}.Infinite

/-- **Hardy–Littlewood Conjecture B** (open, never claimed): the number of
primes up to a sum of two numbers, each at least 2, is at most the sum of
the counts up to each. -/
def HL_conjecture_B : Prop :=
  ∀ x y : Nat, 2 ≤ x → 2 ≤ y →
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y

/-- **The two conjectures are incompatible.** If a nonempty admissible pattern
fits in a window of a given length (at least 2) and has more offsets than
there are primes up to that length, Conjectures A and B cannot both hold. -/
def HL_A_and_B_incompatible : Prop :=
  ∀ (T : Finset Nat) (y : Nat), T.Nonempty → is_admissible T →
    (∀ t ∈ T, t < y) → 2 ≤ y → Nat.primeCounting y < T.card →
      ¬ (HL_conjecture_A ∧ HL_conjecture_B)

end RNS.HensleyRichards
