/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# ColumnStructure — how the two columns multiply

A product of two numbers from the 6n-1 column lands in the 6n+1 column, and
so on for all four combinations; each prime above 3 hits the 6n-1 column at
exactly one position per cycle of that prime; every number in the 6n-1
column has a prime factor from that same column.

Proof: `RNSSolutions/ColumnStructure.lean`. The prime-factor claims assume
`Wheel6.prime_gt_three_is_candidate`. Metadata: `formalization.yaml`.

Source of record: `rns_sieve_6.lean`, Part C and the column lemmas after the
Bonus section.
-/

namespace RNS.ColumnStructure

/-- **How the columns multiply.** (6n-1)·(6n-1) lands in 6n+1; (6n-1)·(6n+1)
and (6n+1)·(6n-1) land in 6n-1; (6n+1)·(6n+1) lands in 6n+1. -/
def columns_multiply : Prop :=
  ∀ a b : Nat,
    (∃ n, col_minus a * col_minus b = col_plus n) ∧
    (∃ n, col_minus a * col_plus b = col_minus n) ∧
    (∃ n, col_plus a * col_minus b = col_minus n) ∧
    (∃ n, col_plus a * col_plus b = col_plus n)

/-- **Each prime hits the 6n-1 column once per cycle.** For a prime other than
2 and 3 there is exactly one position, below the prime, at which it divides
the 6n-1 column: it divides the entry at a position exactly when that
position leaves this remainder on division by the prime. -/
def col_minus_periodicity : Prop :=
  ∀ p : Nat, p.Prime → p ≠ 2 → p ≠ 3 →
    ∃ n_p : Nat, n_p < p ∧ ∀ n : Nat, p ∣ col_minus n ↔ n % p = n_p

/-- **Every 6n-1 number has a 6n-1 prime factor.** -/
def col_minus_has_minus_prime_factor : Prop :=
  ∀ n : Nat, ∃ p, p.Prime ∧ p ∣ col_minus n ∧ p % 6 = 5

/-- **A composite 6n-1 number has a smaller 6n-1 prime factor.** -/
def col_minus_composite_has_proper_minus_factor : Prop :=
  ∀ n : Nat, ¬ (col_minus n).Prime →
    ∃ p, p.Prime ∧ p ∣ col_minus n ∧ p % 6 = 5 ∧ p < col_minus n

end RNS.ColumnStructure
