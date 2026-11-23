/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Algebra.Ring.Parity   -- `Even`, `Odd`

/-!
# GoldbachStacks — Goldbach's conjecture as a building problem

Each odd prime is drawn as a stack two wide with one point sticking up: the
prime 3 is a stack of height 1, 5 of height 2, 7 of height 3, 11 of height 5,
so a stack of height `h` stands for the prime `2h + 1`. Two stacks put
together, with their two sticking-up points making one more unit, give the
number twice their total height plus 2. Building every pair of stacks, a
target height is reached when some pair of stacks adds up to it.

This node proves that three ways of saying Goldbach's conjecture are the same:

* the usual one (every even number above 2 is a sum of two primes);
* the stack one (every target height from 2 on is built from two stacks);
* the frontier one (when stacks arrive in order, by the time a new stack
  arrives every target up to its height is already built from the stacks
  before it).

It proves the equivalences only; Goldbach's conjecture itself stays open.
Original to this project.

Proof: `RNSSolutions/GoldbachStacks.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.GoldbachStacks

/-- A stack height: a number `h` from 1 on with `2h + 1` prime (the stack of
the odd prime `2h + 1`). -/
def is_stack (h : ℕ) : Prop := 1 ≤ h ∧ (2 * h + 1).Prime

/-- The target height `T` is built from two stacks: two stack heights add up
to `T`. -/
def built (T : ℕ) : Prop := ∃ a b, is_stack a ∧ is_stack b ∧ a + b = T

/-- Goldbach's conjecture, the usual form: every even number above 2 is a
sum of two primes. -/
def goldbach : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q, p.Prime ∧ q.Prime ∧ p + q = n

/-- Goldbach's conjecture with odd primes: every even number from 6 on is a
sum of two odd primes. -/
def odd_goldbach : Prop :=
  ∀ n : ℕ, 6 ≤ n → Even n → ∃ p q, p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p + q = n

/-- The stacks never leave a gap: every target height from 2 on is built
from two stacks. -/
def no_gap : Prop := ∀ T : ℕ, 2 ≤ T → built T

/-- The frontier stays ahead: for any two stacks in a row (no stack between
them), every target from 2 up to the height of the later one is built from
stacks no taller than the earlier one. -/
def frontier_ahead : Prop :=
  ∀ h h' : ℕ, is_stack h → is_stack h' → h < h' →
    (∀ m, h < m → m < h' → ¬ is_stack m) →
    ∀ T, 2 ≤ T → T ≤ h' →
      ∃ a b, is_stack a ∧ is_stack b ∧ a ≤ h ∧ b ≤ h ∧ a + b = T

/-- **Odd primes are enough.** The usual Goldbach conjecture holds exactly
when every even number from 6 on is a sum of two odd primes. -/
def goldbach_iff_odd_goldbach : Prop := goldbach ↔ odd_goldbach

/-- **Stacks never leave a gap exactly under Goldbach.** Every target from 2
on is built from two stacks exactly when every even number from 6 on is a sum
of two odd primes. -/
def no_gap_iff_odd_goldbach : Prop := no_gap ↔ odd_goldbach

/-- **The frontier form.** The frontier staying ahead of every new stack is
the same as the stacks never leaving a gap. -/
def frontier_ahead_iff_no_gap : Prop := frontier_ahead ↔ no_gap

/-- **The frontier form is Goldbach's conjecture.** The frontier staying
ahead of every new stack holds exactly when every even number above 2 is a
sum of two primes. -/
def frontier_ahead_iff_goldbach : Prop := frontier_ahead ↔ goldbach

end RNS.GoldbachStacks

/-! ## The wheels never force a gap (added 2026-11-23)

A stack survives the wheel of size `q` when `q` does not divide its prime
`2h + 1`. At the wheel of size 3 the stacks above height 1 have heights that
leave remainder 0 or 2, never 1. At any single wheel, the surviving heights,
taken in pairs, reach every remainder: no wheel on its own can leave a target
unbuilt. -/

namespace RNS.GoldbachStacks

/-- **The wheel of size 3.** Every stack taller than 1 has a height leaving
remainder 0 or 2 on division by 3, never 1 (remainder 1 would make its prime a
multiple of 3). -/
def stack_mod_three : Prop :=
  ∀ h : ℕ, is_stack h → 2 ≤ h → h % 3 ≠ 1

/-- **No single wheel forces a gap.** For every prime `q` and every remainder
`r` modulo `q`, there are two heights `a` and `b` modulo `q` whose stacks
survive the wheel of size `q` (twice the height plus 1 is not a multiple of
`q`) and whose sum leaves remainder `r`. -/
def wheel_no_gap : Prop :=
  ∀ q : ℕ, q.Prime → ∀ r : ZMod q,
    ∃ a b : ZMod q, 2 * a + 1 ≠ 0 ∧ 2 * b + 1 ≠ 0 ∧ a + b = r

end RNS.GoldbachStacks

/-! ## All the wheels of a cycle at once (added 2026-11-23)

The combined cycle of the wheels below a bound (its length is the
primorial) reads each position as one position on every wheel. Choosing a
good pair of heights on each wheel separately and joining the choices through
the Chinese Remainder Theorem gives one pair for the whole cycle. -/

namespace RNS.GoldbachStacks

/-- **No combined cycle forces a gap.** For every bound and every target
position `r` of the combined cycle of the wheels below that bound, there are
two positions `a` and `b` of the cycle whose stacks survive every one of those
wheels (on each wheel, twice the height plus 1 is not on the blocked
position) and whose sum is `r`. -/
def wheels_no_gap : Prop :=
  ∀ limit : ℕ, ∀ r : ZMod (primorial_modulus limit),
    ∃ a b : ZMod (primorial_modulus limit),
      (∀ q : active_primes limit,
        2 * crt_map limit a q + 1 ≠ 0 ∧ 2 * crt_map limit b q + 1 ≠ 0) ∧
      a + b = r

end RNS.GoldbachStacks

/-! ## The open part, stated exactly (added 2026-11-23)

A stack is an actual prime exactly when it survives every wheel up to the
square root of its prime. So a target `T` is built when some pair of heights
adding to `T` survives every wheel whose square is at most `2T + 1`. The
heights range only from 1 to `T − 1`, while the combined cycle of those wheels
(their primorial) is far longer, so the combined-cycle result above does not
reach it: this window is the open part. -/

namespace RNS.GoldbachStacks

/-- **The window statement (open, never claimed; it is Goldbach's
conjecture).** Every target `T` from 2 on is the sum of two heights `a` and
`b`, each at least 1, whose stacks survive every wheel no larger than the
square root of `2T + 1`: a wheel of size `p` with `p · p ≤ 2T + 1` divides
twice the height plus 1 only when it is that prime itself. -/
def window_no_gap : Prop :=
  ∀ T : ℕ, 2 ≤ T → ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ a + b = T ∧
    ∀ p : ℕ, p.Prime → p * p ≤ 2 * T + 1 →
      (p ∣ 2 * a + 1 → p = 2 * a + 1) ∧ (p ∣ 2 * b + 1 → p = 2 * b + 1)

/-- **The window is exactly the stack picture.** The window statement holds
exactly when the stacks never leave a gap. -/
def window_no_gap_iff_no_gap : Prop := window_no_gap ↔ no_gap

/-- **The window is exactly Goldbach's conjecture.** The window statement
holds exactly when every even number above 2 is a sum of two primes. -/
def window_no_gap_iff_goldbach : Prop := window_no_gap ↔ goldbach

end RNS.GoldbachStacks
