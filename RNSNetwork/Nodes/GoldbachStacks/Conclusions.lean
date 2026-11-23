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
