/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# SophieGermainTheorem — the first case of Fermat's Last Theorem for Sophie Germain primes

Sophie Germain's theorem (about 1823). Let `p` be a prime with `2p + 1` also
prime. If `x^p + y^p + z^p = 0` in integers, then `p` divides `x y z`. For
odd `p` this is the "first case" of Fermat's Last Theorem for the exponent
`p`: `x^p + y^p = z^p` has no solution with `p` dividing none of `x, y, z`.

Where the RNS enters: everything rests on the wheel of size `2p + 1`, on
which `p`-th powers sit at only three positions (node `SophieGermainPowers`).
That wheel must block one of `x, y, z`; and since each pairwise sum `y + z`,
`z + x`, `x + y` turns out to be a `p`-th power, the wheel must also block
one of their `p`-th roots. Following where it blocks leads to `p` itself
sitting at position 0, 1 or -1 on the wheel, which it does not.

Proof: `RNSSolutions/SophieGermainTheorem.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.SophieGermainTheorem

/-- **Sophie Germain's theorem.** For a prime `p` with `2p + 1` prime, any
integer solution of `x^p + y^p + z^p = 0` has `p` dividing `x y z`. -/
def sophie_germain_theorem : Prop :=
  ∀ p : Nat, p.Prime → (2 * p + 1).Prime → ∀ x y z : Int,
    x ^ p + y ^ p + z ^ p = 0 → (p : Int) ∣ x * y * z

/-- **Fermat's Last Theorem, first case, for Sophie Germain primes.** For an
odd prime `p` with `2p + 1` prime, any integer solution of `x^p + y^p = z^p`
has `p` dividing `x y z`. -/
def fermat_first_case : Prop :=
  ∀ p : Nat, p.Prime → p ≠ 2 → (2 * p + 1).Prime → ∀ x y z : Int,
    x ^ p + y ^ p = z ^ p → (p : Int) ∣ x * y * z

end RNS.SophieGermainTheorem
