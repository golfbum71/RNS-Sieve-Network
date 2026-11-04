/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# UniformSubdivision — equal shares of survivors in equal intervals

Choose one wheel to rotate and freeze the others. The full cycle of all the
wheels splits into as many equal intervals as the rotating wheel's size minus
one, and every interval holds the same number of survivors: one full cycle's
worth of the frozen wheels' survivors.

Split by column, the result depends on which side the rotating wheel sits on.
A wheel on the 6n+1 side gives each column exactly its share in every
interval. A wheel on the 6n-1 side swaps columns when it removes its
multiples, so each interval is off by the difference between the two
columns' survivor counts in the short overhang past one frozen cycle.

Status: planned. The claims are stated here; no proofs yet.

Prior work: G. F. Grob and M. Schmitt, "Cycles and Patterns in the Sieve of
Eratosthenes", arXiv:1905.03117 (2019), Theorems 6-9, prove the whole-count
form. The column forms are new to this network.
-/

namespace RNS.UniformSubdivision

/-- **Frozen wheels repeat.** Survivors of a set of wheels repeat with period
equal to the product of the wheel sizes: up to some number of full cycles
plus a remainder, the count is that many full cycles' worth plus the count up
to the remainder. -/
def frozen_wheels_repeat : Prop :=
  ∀ (W : Finset Nat) (m r : Nat),
    (survivors_upto W (m * W.prod id + r)).card
      = m * (survivors_upto W (W.prod id)).card + (survivors_upto W r).card

/-- **One wheel removed.** Adding a new prime wheel to a set of prime wheels
removes exactly its multiples, and those correspond one-for-one with the old
survivors up to the bound divided by the new prime (Meissel's identity). -/
def one_wheel_removed : Prop :=
  ∀ (W : Finset Nat) (p N : Nat), p.Prime → (∀ q ∈ W, q.Prime) → p ∉ W →
    (survivors_upto (insert p W) N).card
      = (survivors_upto W N).card - (survivors_upto W (N / p)).card

/-- **Uniform subdivision.** With frozen wheels `W` and rotating wheel `p`,
the survivors of all the wheels up to the end of the `K`-th interval (the full
cycle split into `p - 1` equal parts, rounded down) number exactly `K` full
cycles' worth of the frozen wheels' survivors. -/
def uniform_subdivision : Prop :=
  ∀ (W : Finset Nat) (p K : Nat), p.Prime → (∀ q ∈ W, q.Prime) → p ∉ W →
    (survivors_upto (insert p W) (K * (W.prod id * p) / (p - 1))).card
      = K * (survivors_upto W (W.prod id)).card

/-- **Uniform subdivision, rotating wheel on the 6n+1 side.** When the frozen
wheels include 2 and 3 and the rotating wheel leaves remainder 1 on division
by 6, each column gets exactly its share: `K` full frozen cycles' worth of
that column's survivors. -/
def uniform_subdivision_plus_side : Prop :=
  ∀ (W : Finset Nat) (p K r : Nat), p.Prime → (∀ q ∈ W, q.Prime) → p ∉ W →
    2 ∈ W → 3 ∈ W → p % 6 = 1 →
    (column_survivors_upto (insert p W) r (K * (W.prod id * p) / (p - 1))).card
      = K * (column_survivors_upto W r (W.prod id)).card

/-- **Uniform subdivision, rotating wheel on the 6n-1 side.** When the frozen
wheels include 2 and 3 and the rotating wheel leaves remainder 5 on division
by 6, its multiples swap columns. Each column's count then differs from its
share by the difference between the two columns' frozen survivors in the
overhang (up to `K` full frozen cycles divided by `p - 1`). Written with
both sides added, to avoid truncated subtraction. -/
def uniform_subdivision_minus_side : Prop :=
  ∀ (W : Finset Nat) (p K r : Nat), p.Prime → (∀ q ∈ W, q.Prime) → p ∉ W →
    2 ∈ W → 3 ∈ W → p % 6 = 5 →
    (column_survivors_upto (insert p W) r (K * (W.prod id * p) / (p - 1))).card
        + (column_survivors_upto W (6 - r) (K * W.prod id / (p - 1))).card
      = K * (column_survivors_upto W r (W.prod id)).card
        + (column_survivors_upto W r (K * W.prod id / (p - 1))).card

end RNS.UniformSubdivision
