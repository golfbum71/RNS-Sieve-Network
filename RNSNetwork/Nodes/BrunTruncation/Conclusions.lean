/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic

/-!
# BrunTruncation — stopping inclusion–exclusion early for a product of shares

Brun's sieve, stage 3. Give each wheel a share between zero and one (for the
twin pattern, the share of a wheel's cycle that the pattern hits). The share
that escapes every wheel is the product of one minus each share. Expanding
that product by inclusion–exclusion and stopping after the sets of at most
some number of wheels gives:

* stopping at an even number overestimates and stopping at an odd number
  underestimates (the same alternation as `BrunPureSieve`, now for shares);
* the error is at most the sum, over the sets of one more wheel than the
  stopping point, of the product of their shares (`truncation_error`);
* that sum is at most the total of the shares raised to that number of wheels,
  divided by its factorial (`esymm_power_bound`).

Together, the error of stopping early shrinks like a factorial once the
stopping point passes the total of the shares, which is what makes Brun's
choice of stopping point work.

Proof: `RNSSolutions/BrunTruncation.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.BrunTruncation

/-- Inclusion–exclusion for the product of one minus each share, stopped after
the sets of at most `t` wheels. -/
def trunc_prod (W : Finset Nat) (x : Nat → ℝ) (t : Nat) : ℝ :=
  ∑ D ∈ W.powerset.filter (fun D => D.card ≤ t), (-1 : ℝ) ^ D.card * ∏ p ∈ D, x p

/-- The sum, over the sets of exactly `k` wheels, of the product of their shares. -/
def esymm_k (W : Finset Nat) (x : Nat → ℝ) (k : Nat) : ℝ :=
  ∑ D ∈ W.powerset.filter (fun D => D.card = k), ∏ p ∈ D, x p

/-- **Stopping early, with its sign and size.** With shares between zero and
one, the stopped sum minus the product, times plus or minus one by the parity
of the stopping point, lies between zero and the sum over the sets of one
more wheel. -/
def truncation_error : Prop :=
  ∀ (W : Finset Nat) (x : Nat → ℝ) (t : Nat), (∀ p ∈ W, 0 ≤ x p ∧ x p ≤ 1) →
    0 ≤ (-1 : ℝ) ^ t * (trunc_prod W x t - ∏ p ∈ W, (1 - x p)) ∧
    (-1 : ℝ) ^ t * (trunc_prod W x t - ∏ p ∈ W, (1 - x p)) ≤ esymm_k W x (t + 1)

/-- **The power bound.** With nonnegative shares, the sum over the sets of `k`
wheels of the product of their shares is at most the total share to the `k`,
divided by `k` factorial. -/
def esymm_power_bound : Prop :=
  ∀ (W : Finset Nat) (x : Nat → ℝ) (k : Nat), (∀ p ∈ W, 0 ≤ x p) →
    esymm_k W x k ≤ (∑ p ∈ W, x p) ^ k / (k.factorial : ℝ)

end RNS.BrunTruncation
