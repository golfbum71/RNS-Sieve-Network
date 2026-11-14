/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.ArithmeticFunction.Moebius   -- the Möbius function

/-!
# BrocardPrediction — the exact count and the cycling-only count in a window

The window is the numbers strictly between two bounds `A` and `B`; for
Brocard's conjecture `A` is a base prime's square and `B` the next prime's
square. The slots are the window numbers on the 6n±1 tracks (not divisible by
2 or 3). The wheels are the primes from 5 up.

Letters used in the statements:

* `A`, `B` — the window's two ends;
* `q` — a wheel; `D` — a set of smaller wheels; `r` — a member of `D`;
* `p` — the base prime; `P` — the next prime; `L` — the window length.

Three things are stated.

* **The exact count.** The slots a wheel is the first to block number an
  alternating sum, over the sets of smaller wheels, of the shared slots of the
  wheel and the set (Legendre's formula in the collision-rule form of
  `BrocardWindow`). Adding these over the wheels up to the base prime, and
  adding the primes of the window, gives all the slots.
* **The cycling-only count.** Replace each shared-slot count by its forced
  value (the window length over three times the product of the wheels) and
  drop every product longer than the window. When the window length is below
  five times the base prime plus five (true for twin primes), the result is a
  third of the window length times: one, minus the sum of the reciprocals of
  the primes above the base prime up to the window length, minus the Möbius
  sum over the numbers up to the window length on the 6n±1 tracks.
* **The twin prediction.** For twin primes the window length is four times
  the base prime plus four; the prediction is a third of that, minus one,
  minus the cycling-only count of blocked slots.

Nothing here bounds the true number of primes in the window.

Proof: `RNSSolutions/BrocardPrediction.lean`. Metadata: `formalization.yaml`.
Notes: `docs/BROCARD_NOTES.md`.
-/

namespace RNS.BrocardPrediction

/-- The wheels from 5 up to (not including) `z`. -/
def wheels_below (z : ℕ) : Finset ℕ :=
  (Finset.range z).filter (fun r => r.Prime ∧ 5 ≤ r)

/-- The shared slots of a product `n` of wheels: the numbers `t` on the 6n±1
tracks with `n * t` strictly between `A` and `B`. With `n = 1` these are the
slots of the window. -/
def shared_slots (A B n : ℕ) : ℕ :=
  ((Finset.range B).filter
    (fun t => t % 2 ≠ 0 ∧ t % 3 ≠ 0 ∧ A < n * t ∧ n * t < B)).card

/-- The slots the wheel `q` is the first to block: the slots strictly between
`A` and `B` that `q` divides and no smaller wheel divides. -/
def first_blocked (A B q : ℕ) : ℕ :=
  ((Finset.Ioo A B).filter
    (fun m => m % 2 ≠ 0 ∧ m % 3 ≠ 0 ∧ q ∣ m ∧ ∀ r ∈ wheels_below q, ¬ r ∣ m)).card

/-- **The exact count for one wheel.** The slots a wheel `q` is the first to
block number the alternating sum, over the sets `D` of smaller wheels, of the
shared slots of `q` times the product of `D`. Holds for any window. -/
def window_exact_count : Prop :=
  ∀ A B q : ℕ, q.Prime → 5 ≤ q →
    (first_blocked A B q : ℤ) =
      ∑ D ∈ (wheels_below q).powerset,
        (-1 : ℤ) ^ D.card * (shared_slots A B (q * ∏ r ∈ D, r) : ℤ)

/-- **Primes plus first-blocked slots are all the slots.** Between a base
prime's square and `P` squared, where no prime lies strictly between the base
prime `p` and `P`: the primes of the window, plus the slots first blocked by
each wheel up to the base prime, number exactly the slots. -/
def window_prime_count : Prop :=
  ∀ p P : ℕ, p.Prime → 5 ≤ p → (∀ r : ℕ, r.Prime → r < P → r ≤ p) →
    ((Finset.Ioo (p ^ 2) (P ^ 2)).filter Nat.Prime).card
        + ∑ q ∈ wheels_below (p + 1), first_blocked (p ^ 2) (P ^ 2) q
      = shared_slots (p ^ 2) (P ^ 2) 1

/-- The cycling-only count of blocked slots, for base prime `p` and window
length `L`: over the wheels `q` up to `p` and the sets `D` of smaller wheels
whose product with `q` is at most `L`, plus or minus `L` over three times
that product. -/
noncomputable def cycling_blocked (p L : ℕ) : ℝ :=
  ∑ q ∈ wheels_below (p + 1), ∑ D ∈ (wheels_below q).powerset,
    if q * (∏ r ∈ D, r) ≤ L then
      (-1 : ℝ) ^ D.card * ((L : ℝ) / (3 * ((q * ∏ r ∈ D, r : ℕ) : ℝ)))
    else 0

/-- The sum of the reciprocals of the primes above `p` up to `L`. -/
noncomputable def prime_reciprocals (p L : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Ioc p L).filter Nat.Prime, (1 : ℝ) / (r : ℝ)

/-- The Möbius sum over the 6n±1 tracks: over the numbers `n` from 1 to `L`
not divisible by 2 or 3, the Möbius function of `n` over `n`. -/
noncomputable def moebius_sum (L : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 L).filter (fun n => n % 2 ≠ 0 ∧ n % 3 ≠ 0),
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)

/-- **Closed form of the cycling-only count.** When the base `p` is at least
3 and the window length `L` is at least `p` and below `5 * (p + 1)`, the
cycling-only count of blocked slots is a third of `L` times (one, minus the
prime reciprocals above `p` up to `L`, minus the Möbius sum up to `L`). -/
def cycling_blocked_closed_form : Prop :=
  ∀ p L : ℕ, 3 ≤ p → p ≤ L → L < 5 * (p + 1) →
    cycling_blocked p L = (L : ℝ) / 3 * (1 - prime_reciprocals p L - moebius_sum L)

/-- The cycling-only prediction for a twin window with base prime `p`: a
third of the window length `4 * p + 4`, minus one, minus the cycling-only
count of blocked slots. -/
noncomputable def twin_prediction (p : ℕ) : ℝ :=
  ((4 * p + 4 : ℕ) : ℝ) / 3 - 1 - cycling_blocked p (4 * p + 4)

/-- **Closed form of the twin prediction.** For a base at least 5, the twin
prediction is a third of the window length times (the prime reciprocals above
the base up to the window length, plus the Möbius sum up to the window
length), minus one. -/
def twin_prediction_closed_form : Prop :=
  ∀ p : ℕ, 5 ≤ p →
    twin_prediction p =
      ((4 * p + 4 : ℕ) : ℝ) / 3
          * (prime_reciprocals p (4 * p + 4) + moebius_sum (4 * p + 4)) - 1

end RNS.BrocardPrediction
