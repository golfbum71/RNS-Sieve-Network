/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.PileUpLock.Conclusions
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval

/-!
# FieldSizeTimes — times with the number of runners as denominator

With the number of runners as the denominator, the track is cut into exactly
that many equal parts, and one part is exactly the loneliness distance. So at
such a time a runner is far enough from the start exactly when it is not at the
start (`field_size_far_iff`), and the runner standing still is lonely exactly
when no speed times the numerator is a multiple of the number of runners
(`field_size_lonely_iff`).

When the number of runners is prime, the consecutive speeds 1, 2, … up to one
less than it are lonely at such a time exactly when the numerator is not a
multiple of the number of runners (`consecutive_prime_field`): these are the
tight cases, with every runner at its own fence post. This is the easy half of
Sungkawichai and Trakulthongchai's Remark 3.2 (arXiv 2604.23906), the reason
their method needs the number of runners prime. Their polynomial method over the
remainders for a prime number of runners (Proposition 4.1) is not proved here.

Proof: `RNSSolutions/FieldSizeTimes.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.FieldSizeTimes

open RNS.PileUpLock

/-- **One part is the loneliness distance.** With `N` parts to the lap and `N`
runners, a point is far enough from the start exactly when it is not at the
start. -/
def field_size_far_iff : Prop :=
  ∀ (N : ℕ) (y : ℤ), 0 < N → (far N N y ↔ ¬ (N : ℤ) ∣ y)

/-- **Lonely at a field-size time.** The runner standing still is lonely at the
time `s / (number of runners)` exactly when no speed times `s` is a multiple of
the number of runners. -/
def field_size_lonely_iff : Prop :=
  ∀ (S : Finset ℤ) (s : ℤ),
    lonely_at S (S.card + 1) s ↔ ∀ v ∈ S, ¬ ((S.card + 1 : ℕ) : ℤ) ∣ v * s

/-- **Consecutive speeds with a prime number of runners.** If `k + 1` is prime,
the speeds `1, …, k` are lonely at the time `s / (k + 1)` exactly when `s` is
not a multiple of `k + 1`. -/
def consecutive_prime_field : Prop :=
  ∀ (k : ℕ), (k + 1).Prime → ∀ s : ℤ,
    lonely_at (Finset.Icc (1 : ℤ) k) (k + 1) s ↔ ¬ ((k + 1 : ℕ) : ℤ) ∣ s

end RNS.FieldSizeTimes
