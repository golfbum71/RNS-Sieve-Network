/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import Mathlib

/-!
# Vocabulary: the shared language of the RNS sieve network

Definitions only. No theorems, no lemmas, no proofs.

Every node in the network states its claims using the words defined here,
so a reader who has read this one short file can read every node's claims.
Each definition is copied unchanged from `rns_sieve_6.lean` (the source of
record) or `rns_open_conjectures.lean`, keeping the original names so the
two can be compared line by line.
-/

namespace RNS

/-! ## The 6n±1 wheel -/

/-- A number passes the mod-6 wheel when its remainder on division by 6 is
1 or 5. Every prime above 3 passes it. -/
def is_candidate (n : Nat) : Bool :=
  (n % 6 == 1) || (n % 6 == 5)

/-- The "6n-1" column, counted from position 0: 5, 11, 17, 23, ...
(written as `6 * n + 5` to avoid truncated subtraction). -/
def col_minus (n : Nat) : Nat := 6 * n + 5

/-- The "6n+1" column, counted from position 0: 1, 7, 13, 19, ... -/
def col_plus (n : Nat) : Nat := 6 * n + 1

/-! ## Wheels and their combined cycle -/

/-- The wheels in use: every prime below `limit`. -/
def active_primes (limit : Nat) : Finset Nat :=
  (Finset.range limit).filter Nat.Prime

/-- The length of the combined cycle of all active wheels: the product of
every prime below `limit` (the primorial). -/
def primorial_modulus (limit : Nat) : Nat :=
  (active_primes limit).prod id

/-- Reading one position of the combined cycle as one position on each
individual wheel: a remainder modulo the primorial is sent to its remainder
modulo each active prime. (The `show … from …` term only records that each
wheel size divides the cycle length, which reducing a remainder needs.) -/
def crt_map (limit : Nat) (n : ZMod (primorial_modulus limit)) :
    ∀ q : active_primes limit, ZMod (q : Nat) :=
  fun q => ZMod.castHom
    (show (q : Nat) ∣ primorial_modulus limit from Finset.dvd_prod_of_mem id q.2)
    (ZMod q) n

/-! ## Offset patterns and admissibility -/

/-- How many distinct positions on the wheel of size `p` the offset pattern
`T` occupies. -/
def w (T : Finset Nat) (p : Nat) : Nat :=
  (T.image (fun t => t % p)).card

/-- An offset pattern is admissible when no wheel is completely covered by
it: at every prime, at least one position is left open. -/
def is_admissible (T : Finset Nat) : Prop :=
  ∀ p, p.Prime → w T p < p

/-- The offset pattern of an evenly spaced run of `k` numbers with spacing
`d`: `{0, d, 2d, ..., (k-1)d}`. -/
def ap_offsets (d k : Nat) : Finset Nat :=
  (Finset.range k).image (· * d)

/-! ## The singular series -/

/-- The correction factor contributed by the wheel of size `p`: how far the
true surviving fraction differs from the naive guess that each offset is
blocked independently. -/
noncomputable def singular_series_factor (T : Finset Nat) (p : Nat) : Real :=
  (p : Real) ^ (T.card - 1) * ((p : Real) - w T p) / ((p : Real) - 1) ^ T.card

/-- The Hardy–Littlewood constant of an offset pattern: the product of every
wheel's correction factor, over all primes. -/
noncomputable def hardy_littlewood_constant (T : Finset Nat) : Real :=
  ∏' p : Nat.Primes, singular_series_factor T p

/-! ## Counting prime patterns -/

/-- How many starting numbers below `N` make every member of the offset
pattern `T` prime. -/
noncomputable def actual_tuple_count (T : Finset Nat) (N : Nat) : Nat :=
  ((Finset.range N).filter (fun n => ∀ t ∈ T, (n + t).Prime)).card

/-- The Hardy–Littlewood prediction for `actual_tuple_count`: the constant
times `N / (log N)^k`, where `k` is the number of offsets. -/
noncomputable def hardy_littlewood_main_term (T : Finset Nat) (N : Nat) : Real :=
  hardy_littlewood_constant T * (N : Real) / (Real.log N) ^ T.card

/-! ## Gaps between primes -/

/-- Two primes with no prime strictly between them. -/
def consecutive_primes (p q : Nat) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r, r.Prime → p < r → r < q → False

/-- A number is blocked by the wheels up to `n` when one of the primes at or
below `n` divides it. -/
def legendre_blocked (n x : Nat) : Prop :=
  ∃ p, p.Prime ∧ p ≤ n ∧ p ∣ x

end RNS
