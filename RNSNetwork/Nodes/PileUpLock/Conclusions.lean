/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Ring.Abs

/-!
# PileUpLock — when one runner can be freed while the rest are together

Runners go round a track of length one. Speeds are whole numbers (laps per unit
of time); times are fractions, a numerator over a positive denominator. At the
time `k / m`, the runner of speed `v` stands at the remainder of `v * k` on
division by `m`, counted in `m`-ths of a lap: the residue picture of the RNS.

Pick a target runner and call the rest the pack. The pack is together at the
start exactly when the denominator divides the greatest common factor of the
pack's speeds times the numerator (`pack_together_iff`). A target whose speed
is a multiple of that greatest common factor is locked: whenever the whole pack
is at the start, so is the target (`locked_never_separated`). Otherwise the
target can be freed: some moment has the pack at the start and the target at
least a third of a lap away, and this happens only for unlocked targets
(`pile_up_frees_iff`). The same holds with the pack together at any shared
point, measuring speeds relative to one pack runner (`shared_point_pile_up`).

This file also holds the shared vocabulary of the Lonely Runner family:
`far`, `lonely_at`, `has_lonely_time`, `lonely_runner_upto`. These use times
that are fractions; the usual statement with real times is equivalent (a
classical fact, not proved here).

Original to this project (Geo's pile-up idea). Proof:
`RNSSolutions/PileUpLock.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.PileUpLock

/-- **At least one `n`-th of a lap from the start.** The point `y / m` of a lap
(read as the remainder of `y` on division by `m`) is at least `1 / n` of a lap
from the start, measured both ways round. -/
def far (n m : ℕ) (y : ℤ) : Prop :=
  (m : ℤ) ≤ (n : ℤ) * (y % (m : ℤ)) ∧ (m : ℤ) ≤ (n : ℤ) * ((m : ℤ) - y % (m : ℤ))

/-- **A lonely moment for the runner standing still.** The runner to be lonely
stands at the start (speed 0, after measuring all speeds relative to it); the
moving runners have the speeds in `S`. At the time `k / m` (with `m` positive)
every moving runner is at least `1 / (number of runners)` of a lap away. -/
def lonely_at (S : Finset ℤ) (m : ℕ) (k : ℤ) : Prop :=
  0 < m ∧ ∀ v ∈ S, far (S.card + 1) m (v * k)

/-- The runner standing still has some lonely moment at a time that is a fraction. -/
def has_lonely_time (S : Finset ℤ) : Prop :=
  ∃ m : ℕ, ∃ k : ℤ, lonely_at S m k

/-- **The Lonely Runner Conjecture for fields of up to `c + 1` runners**, at
times that are fractions: every set of at most `c` distinct nonzero speeds has
a lonely moment for the runner standing still. Open in general; proved for
small fields (node `LonelyRecords`). Used only as a named hypothesis. -/
def lonely_runner_upto (c : ℕ) : Prop :=
  ∀ S : Finset ℤ, 0 ∉ S → S.card ≤ c → has_lonely_time S

/-- **When the pack is together at the start.** For pack runners indexed by
`P` with speeds `sp`, all are at the start at the time `k / m` exactly when `m`
divides the greatest common factor of their speeds times `k`. -/
def pack_together_iff : Prop :=
  ∀ (ι : Type) (P : Finset ι) (sp : ι → ℤ) (m : ℕ) (k : ℤ),
    (∀ i ∈ P, (m : ℤ) ∣ sp i * k) ↔ (m : ℤ) ∣ P.gcd sp * k

/-- **A locked target is never separated by a pile-up.** If the target's speed
`u` is a multiple of the greatest common factor of the pack's speeds, then at
every moment when the whole pack is at the start, so is the target. -/
def locked_never_separated : Prop :=
  ∀ (ι : Type) (P : Finset ι) (sp : ι → ℤ) (u : ℤ) (m : ℕ) (k : ℤ), 0 < m →
    (∀ i ∈ P, (m : ℤ) ∣ sp i * k) → P.gcd sp ∣ u → (u * k) % (m : ℤ) = 0

/-- **The pile-up frees exactly the unlocked targets.** Some moment has the
whole pack at the start and the target at least a third of a lap away if and
only if the target's speed is not a multiple of the greatest common factor of
the pack's speeds. A third of a lap is enough for any field of three or more
runners. -/
def pile_up_frees_iff : Prop :=
  ∀ (ι : Type) (P : Finset ι) (sp : ι → ℤ) (u : ℤ),
    (∃ m : ℕ, ∃ k : ℤ, 0 < m ∧ (∀ i ∈ P, (m : ℤ) ∣ sp i * k) ∧ far 3 m (u * k)) ↔
      ¬ P.gcd sp ∣ u

/-- **Pile-up at a shared point.** Measuring every speed relative to a pack
speed `a`: some moment has the whole pack together at one point and the target
at least a third of a lap from it if and only if the target's relative speed
is not a multiple of the greatest common factor of the pack's relative speeds. -/
def shared_point_pile_up : Prop :=
  ∀ (ι : Type) (P : Finset ι) (sp : ι → ℤ) (a u : ℤ),
    (∃ m : ℕ, ∃ k : ℤ, 0 < m ∧ (∀ i ∈ P, (m : ℤ) ∣ (sp i - a) * k) ∧
        far 3 m ((u - a) * k)) ↔
      ¬ P.gcd (fun i => sp i - a) ∣ (u - a)

end RNS.PileUpLock
