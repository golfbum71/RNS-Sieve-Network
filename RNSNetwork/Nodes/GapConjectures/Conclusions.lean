/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# GapConjectures — Legendre, Brocard, Oppermann, Andrica

Four classical conjectures about primes between squares, and the checked
implications among them. Each "survivor bound" says a window of a certain
length is never entirely blocked by the small wheels; each implies its
conjecture. Oppermann's conjecture in turn implies both Andrica's and
Legendre's, so Legendre's has two independent routes.

**Every conjecture and survivor bound here is open.** They are stated below
and appear only as hypotheses of the claims.

Proof: `RNSSolutions/GapConjectures.lean`; rests on no other node. Metadata:
`formalization.yaml`.

Source of record: `rns_open_conjectures.lean`, Parts 1–5. The source's
`brocard_blocked` is identical in meaning to `legendre_blocked`, so both
uses are written with the shared Vocabulary definition.
-/

-- Counting "the numbers in a window that no small wheel divides" needs the
-- property to be decidable; `legendre_blocked` is an unbounded existential,
-- so classical decidability is used, exactly as in the source file. The
-- proof file opens it too, so both elaborate the count the same way.
open scoped Classical

namespace RNS.GapConjectures

/-- The survivor bound behind Legendre (open): no run of twice-n consecutive
numbers is entirely blocked by the primes up to n. -/
def jacobsthal_bound_holds (n : Nat) : Prop :=
  ∀ x, ∃ i, i < 2 * n ∧ ¬ legendre_blocked n (x + i)

/-- **Legendre's conjecture** (open): a prime lies strictly between every two
consecutive squares from 1 on. -/
def legendre_conjecture : Prop :=
  ∀ n : Nat, 1 ≤ n → ∃ p, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- The survivor bound behind Brocard (open): every window of length 4p + 4
holds at least 4 numbers that no prime up to p divides. -/
def four_survivors_bound_holds (p : Nat) : Prop :=
  ∀ x, 4 ≤ ((Finset.Ico x (x + (4 * p + 4))).filter (fun y => ¬ legendre_blocked p y)).card

/-- **Brocard's conjecture** (open): between the squares of two consecutive
primes from 3 on there are at least 4 primes. -/
def brocard_conjecture : Prop :=
  ∀ p q, consecutive_primes p q → 3 ≤ p →
    4 ≤ ((Finset.Ico (p ^ 2) (q ^ 2)).filter Nat.Prime).card

/-- The survivor bound behind Oppermann (open), on both sides of n squared. -/
def oppermann_bound_holds (n : Nat) : Prop :=
  (∀ x, ∃ i, i < n - 1 ∧ ¬ legendre_blocked (n - 1) (x + i)) ∧
  (∀ x, ∃ i, i < n - 1 ∧ ¬ legendre_blocked n (x + i))

/-- **Oppermann's conjecture** (open): for every n from 2 on, a prime lies
strictly between n² − n and n², and another strictly between n² and n² + n. -/
def oppermann_conjecture : Prop :=
  ∀ n : Nat, 2 ≤ n →
    (∃ p, p.Prime ∧ n ^ 2 - n < p ∧ p < n ^ 2) ∧
    (∃ p, p.Prime ∧ n ^ 2 < p ∧ p < n ^ 2 + n)

/-- **Andrica's conjecture** (open), squared twice to stay in whole numbers:
for consecutive primes from 3 on, (gap − 1)² is less than 4 times the smaller
prime — equivalent to the square roots differing by less than 1. -/
def andrica_conjecture : Prop :=
  ∀ p q, consecutive_primes p q → 3 ≤ p → (q - p - 1) ^ 2 < 4 * p

/-- **The survivor bound gives Legendre.** -/
def legendre_of_jacobsthal : Prop :=
  (∀ n, 1 ≤ n → jacobsthal_bound_holds n) → legendre_conjecture

/-- **The four-survivor bound gives Brocard.** -/
def brocard_of_four_survivors : Prop :=
  (∀ p, p.Prime → 3 ≤ p → four_survivors_bound_holds p) → brocard_conjecture

/-- **The two-sided survivor bound gives Oppermann.** -/
def oppermann_of_bound : Prop :=
  (∀ n, 2 ≤ n → oppermann_bound_holds n) → oppermann_conjecture

/-- **Oppermann gives Andrica.** -/
def andrica_of_oppermann : Prop :=
  oppermann_conjecture → andrica_conjecture

/-- **Oppermann gives Legendre** (a second route to Legendre). -/
def legendre_of_oppermann : Prop :=
  oppermann_conjecture → legendre_conjecture

end RNS.GapConjectures
