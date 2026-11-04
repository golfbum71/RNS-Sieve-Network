/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
-- Only the parts of Mathlib these definitions need, rather than all of it:
-- each module below was checked against Mathlib at the pinned commit
-- (see `lake-manifest.json`).
import Mathlib.Data.Nat.Prime.Defs                         -- primes, `Nat.Primes`
import Mathlib.Data.ZMod.Basic                             -- remainders, `ZMod.castHom`
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise -- `Finset.dvd_prod_of_mem`
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset   -- `Finset.prod_ne_zero_iff`
import Mathlib.Topology.Algebra.InfiniteSum.Defs           -- infinite products `∏'`
import Mathlib.Analysis.SpecialFunctions.Log.Basic         -- `Real.log`
import Mathlib.Order.Interval.Finset.Nat                   -- `Finset.Icc` on `Nat`

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

/-- A number passes the last-digit wheel when its last decimal digit is 1, 3,
7 or 9. Every prime above 5 passes it. -/
def digit_ok (n : Nat) : Bool :=
  (n % 10 == 1) || (n % 10 == 3) || (n % 10 == 7) || (n % 10 == 9)

/-- A Sophie Germain prime: a prime whose double plus one is also prime. -/
def sophie_germain (p : Nat) : Prop := p.Prime ∧ (2 * p + 1).Prime

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

/-! ## Survivors of the wheels -/

/-- The positions on the wheel of size `p` left open by the twin pattern:
neither the position nor the position two further on is blocked. -/
def local_survivors (p : Nat) (hp : p.Prime) : Finset (ZMod p) :=
  have : NeZero p := ⟨hp.pos.ne'⟩
  Finset.univ.filter (fun n => n ≠ 0 ∧ n ≠ (-2 : ZMod p))

/-- The positions of the combined cycle left open by the twin pattern on
every active wheel. (The `NeZero` line only records that the cycle length is
not zero, which listing its positions needs.) -/
def wheel_survivors (limit : Nat) : Finset (ZMod (primorial_modulus limit)) :=
  have : NeZero (primorial_modulus limit) := ⟨by
    unfold primorial_modulus
    exact Finset.prod_ne_zero_iff.mpr fun q hq => (Finset.mem_filter.mp hq).2.ne_zero⟩
  Finset.univ.filter (fun n => ∀ q : active_primes limit,
    crt_map limit n q ≠ 0 ∧ crt_map limit n q ≠ (-2 : ZMod (q : ℕ)))

/-- The positions on the wheel of size `p` left open by a general offset
pattern `T`: no offset lands on the blocked position. -/
def local_survivors_gen (T : Finset Nat) (p : Nat) (hp : p.Prime) : Finset (ZMod p) :=
  have : NeZero p := ⟨hp.pos.ne'⟩
  Finset.univ.filter (fun n => ∀ t ∈ T, n + (t : ZMod p) ≠ 0)

/-- The positions of the combined cycle left open by the offset pattern `T`
on every active wheel. -/
def wheel_survivors_gen (T : Finset Nat) (limit : Nat) :
    Finset (ZMod (primorial_modulus limit)) :=
  have : NeZero (primorial_modulus limit) := ⟨by
    unfold primorial_modulus
    exact Finset.prod_ne_zero_iff.mpr fun q hq => (Finset.mem_filter.mp hq).2.ne_zero⟩
  Finset.univ.filter (fun n => ∀ q : active_primes limit,
    ∀ t ∈ T, crt_map limit n q + (t : ZMod (q : ℕ)) ≠ 0)

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

/-! ## Survivors up to a bound -/

/-- The numbers from 1 to `N` that survive every wheel in `W`: none of the
wheel sizes divides them. -/
def survivors_upto (W : Finset Nat) (N : Nat) : Finset Nat :=
  (Finset.Icc 1 N).filter (fun k => ∀ q ∈ W, ¬ q ∣ k)

/-- The survivors from 1 to `N` in one column: those leaving remainder `r` on
division by 6 (5 for the 6n-1 column, 1 for the 6n+1 column). -/
def column_survivors_upto (W : Finset Nat) (r N : Nat) : Finset Nat :=
  (survivors_upto W N).filter (fun k => k % 6 = r)

end RNS
