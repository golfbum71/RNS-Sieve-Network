/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.Nat.Nth                 -- `Nat.nth`, the primes in order
import Mathlib.NumberTheory.Primorial       -- `primorial`, used by the Fortune statement
import Mathlib.NumberTheory.AlmostPrime     -- `Nat.IsSemiprime`

/-!
# FortunateCeiling — what lands on a prime just above the cycle

Add a number greater than 1 to the combined cycle of the wheels. If the sum is
prime, no wheel can divide the number added: a wheel dividing it would also
divide the sum, and the sum is larger than any wheel. So the number added
survives every wheel, and the ceiling argument applies to it: below the next
prime's square it must be prime, and if it is composite it is at least that
square. Below the cube of the next prime a composite one has exactly two prime
factors.

Two open statements in DeepMind's `formal-conjectures` repository are about
exactly these numbers:

* **Fortune's conjecture.** The Fortunate number is the smallest number above
  1 that, added to the primorial, gives a prime. Fortune conjectured it is
  always prime. Here: every Fortunate number is at least the next prime, and it
  is prime whenever it lies below the next prime's square; so Fortune's
  conjecture follows from "every Fortunate number lies below the ceiling".
* **OEIS A038771**, the smallest *composite* number that, added to the product
  of the first wheels, gives a prime. Here: it is never below the next prime's
  square (the "ratio at least 1" half of the Greathouse–Ordowski conjecture
  holds for every wheel count), and it has exactly two prime factors whenever
  it lies below the next prime's cube (a conditional form of Kamenetsky's
  conjecture).

The definitions `fortunate` and `smallest_composite_shift` follow the
`formal-conjectures` files `Wikipedia/FortuneConjecture.lean` and
`OEIS/38771.lean` (same wheels, same indexing; `fortunate` uses `sInf` where
that file uses `Nat.find`, and the two agree since the set is nonempty).

Proof: `RNSSolutions/FortunateCeiling.lean`. The prime-below-the-ceiling claims
rest on `ShieldCertificates.window_prime_iff`. Metadata: `formalization.yaml`.
-/

namespace RNS.FortunateCeiling

/-! ## The general facts, for any set of wheels (all primes below `L`) -/

/-- **No wheel divides the shift.** If a number above 1, added to the cycle of
the wheels below `L`, gives a prime, then no wheel below `L` divides it. -/
def shift_avoids_wheels : Prop :=
  ∀ L m q : Nat, 1 < m → (primorial_modulus L + m).Prime → q.Prime → q < L → ¬ q ∣ m

/-- **Below the ceiling the shift is prime.** If a number above 1, added to
the cycle of the wheels below `L`, gives a prime, and the number lies below
`L` squared, it is prime. -/
def shift_prime_below_ceiling : Prop :=
  ∀ L m : Nat, 1 < m → (primorial_modulus L + m).Prime → m < L * L → m.Prime

/-- **A composite shift reaches the ceiling.** A composite number that, added
to the cycle of the wheels below `L`, gives a prime is at least `L` squared. -/
def composite_shift_at_least_ceiling : Prop :=
  ∀ L m : Nat, 1 < m → ¬ m.Prime → (primorial_modulus L + m).Prime → L * L ≤ m

/-- **Below the cube a composite shift has two prime factors.** A composite
number that, added to the cycle of the wheels below `L`, gives a prime, and
lies below `L` cubed, is a product of exactly two primes. -/
def composite_shift_semiprime_below_cube : Prop :=
  ∀ L m : Nat, 1 < m → ¬ m.Prime → (primorial_modulus L + m).Prime →
    m < L * L * L → m.IsSemiprime

/-- **The first wheels are the wheels below the next prime.** The product of
the first `k` primes is the cycle of the wheels below the `(k+1)`-st prime
(`Nat.nth Nat.Prime k`, counting from 0). -/
def first_primes_eq_cycle : Prop :=
  ∀ k : Nat, (∏ i ∈ Finset.range k, Nat.nth Nat.Prime i) = primorial_modulus (Nat.nth Nat.Prime k)

/-- **The primorial is the cycle of the wheels below the next prime.** The
product of the primes up to the `(n+1)`-st prime is the cycle of the wheels
below the `(n+2)`-nd prime. -/
def primorial_eq_cycle : Prop :=
  ∀ n : Nat, primorial (Nat.nth Nat.Prime n) = primorial_modulus (Nat.nth Nat.Prime (n + 1))

/-! ## Fortune's conjecture -/

/-- The Fortunate number (0-indexed, as in `formal-conjectures`): the smallest
number above 1 that, added to the product of the primes up to the `(n+1)`-st
prime, gives a prime. `fortunate 0 = 3`, `fortunate 1 = 5`, `fortunate 3 = 13`. -/
noncomputable def fortunate (n : Nat) : Nat :=
  sInf {m : Nat | 1 < m ∧ (primorial (Nat.nth Nat.Prime n) + m).Prime}

/-- **The Fortunate number is well defined**: it is above 1 and lands on a
prime. -/
def fortunate_spec : Prop :=
  ∀ n : Nat, 1 < fortunate n ∧ (primorial (Nat.nth Nat.Prime n) + fortunate n).Prime

/-- **The Fortunate number is at least the next prime**: every prime factor of
it lies beyond the wheels. -/
def fortunate_at_least_next_prime : Prop :=
  ∀ n : Nat, Nat.nth Nat.Prime (n + 1) ≤ fortunate n

/-- **A Fortunate number below the ceiling is prime.** -/
def fortunate_prime_below_ceiling : Prop :=
  ∀ n : Nat, fortunate n < Nat.nth Nat.Prime (n + 1) * Nat.nth Nat.Prime (n + 1) →
    (fortunate n).Prime

/-- **Fortune's conjecture from the ceiling.** If every Fortunate number lies
below the next prime's square, every Fortunate number is prime. -/
def fortune_of_ceiling : Prop :=
  (∀ n : Nat, fortunate n < Nat.nth Nat.Prime (n + 1) * Nat.nth Nat.Prime (n + 1)) →
    ∀ n : Nat, (fortunate n).Prime

/-! ## OEIS A038771 -/

/-- OEIS A038771 (as in `formal-conjectures`): the smallest composite number
that, added to the product of the first `n` primes, gives a prime.
Values 4, 9, 25, 49, 121, 221, 289, … -/
noncomputable def smallest_composite_shift (n : Nat) : Nat :=
  sInf {c : Nat | (1 < c ∧ ¬ c.Prime) ∧ ((∏ i ∈ Finset.range n, Nat.nth Nat.Prime i) + c).Prime}

/-- **The sequence is well defined**: the value is composite and lands on a
prime (by Dirichlet's theorem, as in `formal-conjectures`' `a_n_exists`). -/
def smallest_composite_shift_spec : Prop :=
  ∀ n : Nat, (1 < smallest_composite_shift n ∧ ¬ (smallest_composite_shift n).Prime) ∧
    ((∏ i ∈ Finset.range n, Nat.nth Nat.Prime i) + smallest_composite_shift n).Prime

/-- **The ceiling floor.** The value is never below the square of the next
prime (`Nat.nth Nat.Prime n`, the `(n+1)`-st prime). This is the "ratio at
least 1" half of the Greathouse–Ordowski conjecture, for every `n`. -/
def smallest_composite_shift_floor : Prop :=
  ∀ n : Nat, Nat.nth Nat.Prime n * Nat.nth Nat.Prime n ≤ smallest_composite_shift n

/-- **Two prime factors below the cube.** If the value lies below the cube of
the next prime, it is a product of exactly two primes. -/
def smallest_composite_shift_semiprime_below_cube : Prop :=
  ∀ n : Nat, smallest_composite_shift n < Nat.nth Nat.Prime n * Nat.nth Nat.Prime n * Nat.nth Nat.Prime n →
    (smallest_composite_shift n).IsSemiprime

/-- **Kamenetsky's conjecture from the cube.** If every value lies below the
cube of the next prime, every value is a product of exactly two primes. -/
def semiprime_conjecture_of_cube : Prop :=
  (∀ n : Nat, smallest_composite_shift n <
      Nat.nth Nat.Prime n * Nat.nth Nat.Prime n * Nat.nth Nat.Prime n) →
    ∀ n : Nat, (smallest_composite_shift n).IsSemiprime

end RNS.FortunateCeiling
