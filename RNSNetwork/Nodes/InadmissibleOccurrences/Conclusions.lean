/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# InadmissibleOccurrences — inadmissible patterns sit next to their blocking wheel

If an offset pattern covers every position on the wheel of some prime, then
wherever every member of the pattern is prime, one member is that prime
itself: whatever the starting number, some member is a multiple of the
prime. So the pattern occurs only finitely often. Corollary: the six numbers
at offsets 0, 2, 6, 8, 12, 14 are all prime only when starting at 5 (giving
5, 7, 11, 13, 17, 19), since those offsets cover every position on the wheel
of size 5. In particular the prime-gap block 2, 4, 2, 4, 2 occurs only there.

Proof: `RNSSolutions/InadmissibleOccurrences.lean`. Metadata:
`formalization.yaml`.

Source: DeepMind formal-conjectures, `OeisA1223.conjecture` (the gap-block
statement).
-/

namespace RNS.InadmissibleOccurrences

/-- **A covered wheel forces its prime into every occurrence.** If the offset
pattern `T` occupies all `p` positions on the wheel of the prime `p`, and
every member `n + t` of the pattern starting at `n` is prime, then some member
equals `p`. -/
def inadmissible_occurrence_contains_prime : Prop :=
  ∀ (T : Finset Nat) (p n : Nat), p.Prime → w T p = p →
    (∀ t ∈ T, (n + t).Prime) → ∃ t ∈ T, n + t = p

/-- **The gap block 2, 4, 2, 4, 2 occurs once.** The six numbers at offsets 0,
2, 6, 8, 12, 14 from a starting number are all prime only when the starting
number is 5. -/
def gap_block_24242_unique : Prop :=
  ∀ n : Nat, n.Prime → (n + 2).Prime → (n + 6).Prime → (n + 8).Prime →
    (n + 12).Prime → (n + 14).Prime → n = 5

end RNS.InadmissibleOccurrences
