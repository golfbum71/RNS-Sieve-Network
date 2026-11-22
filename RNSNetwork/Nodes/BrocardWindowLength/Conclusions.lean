/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# BrocardWindowLength — the window between two prime squares is a multiple of 24

For primes from 5 on, the distance from the square of the smaller prime to the
square of the larger one is always a multiple of 24, and it is at least four
times the smaller prime plus 4. For consecutive primes this distance is the
length of the Brocard window.

Proof: `RNSSolutions/BrocardWindowLength.lean`; the multiple-of-24 claim rests
on `UnitSquares24.prime_sq_mod_24`. Metadata: `formalization.yaml`.
-/

namespace RNS.BrocardWindowLength

/-- **The window is a multiple of 24.** For primes from 5 on, the larger square
minus the smaller square is divisible by 24. -/
def window_length_mod_24 : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → 5 ≤ p → p < q → 24 ∣ q ^ 2 - p ^ 2

/-- **The window is at least four times the smaller prime plus 4.** For primes
from 3 on, the larger square minus the smaller square is at least four times the
smaller prime plus 4. -/
def window_length_lower : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → 3 ≤ p → p < q → 4 * p + 4 ≤ q ^ 2 - p ^ 2

end RNS.BrocardWindowLength
