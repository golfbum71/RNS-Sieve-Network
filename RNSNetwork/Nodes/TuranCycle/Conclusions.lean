/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# TuranCycle — Turán's sieve, exactly, on the positions 1 to N

For a set of wheels, count at each position how many wheels divide it (its
number of hits). Over the positions 1 to `N` the hits add up exactly to the
sum, over the wheels, of the number of multiples of that wheel (`N` divided
by the wheel, rounded down), and the squared hits add up exactly to the sum,
over ordered pairs of wheels, of the multiples of their least common
multiple. No estimate is involved.

Turán's sieve is the second-moment (variance) argument: a survivor has no
hits, so it sits as far below the average as possible, and the spread of the
hits limits how many such positions there can be. Written without division:
the survivor count times the total hits squared is at most `N` times (`N`
times the total squared hits minus the total hits squared). The inequality
itself holds for any counting function on any finite set
(`turan_inequality`); with the exact hit counts it becomes Turán's sieve for
the wheels (`turan_wheels`).

For the wheels up to 13 on one cycle (30030 positions) the bound allows about
15,100 survivors against the true 5760: Turán's sieve is weak, but it is the
classical first step from exact counts to bounds, and every quantity here is
exact.

Proof: `RNSSolutions/TuranCycle.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.TuranCycle

/-- The number of wheels in `W` dividing the position `m`. -/
def hits (W : Finset Nat) (m : Nat) : Nat := (W.filter (fun q => q ∣ m)).card

/-- **The hits add up exactly.** Over the positions 1 to `N`, the hits total
the sum over the wheels of `N` divided by the wheel (rounded down). -/
def hits_sum : Prop :=
  ∀ (W : Finset Nat) (N : Nat), ∑ m ∈ Finset.Ioc 0 N, hits W m = ∑ q ∈ W, N / q

/-- **The squared hits add up exactly.** Over the positions 1 to `N`, the
squared hits total the sum over ordered pairs of wheels of `N` divided by
their least common multiple (rounded down). -/
def hits_sq_sum : Prop :=
  ∀ (W : Finset Nat) (N : Nat),
    ∑ m ∈ Finset.Ioc 0 N, (hits W m) ^ 2 = ∑ q ∈ W, ∑ r ∈ W, N / Nat.lcm q r

/-- **Turán's inequality** (the second-moment bound), for any counting
function `f` on a finite set `s`: the number of points where `f` is zero, times
the total of `f` squared, is at most the size of `s` times (the size of `s`
times the total of `f` squared pointwise, minus the total of `f` squared). -/
def turan_inequality : Prop :=
  ∀ (s : Finset Nat) (f : Nat → Nat),
    ((s.filter (fun m => f m = 0)).card : ℤ) * (∑ m ∈ s, (f m : ℤ)) ^ 2 ≤
      (s.card : ℤ) * ((s.card : ℤ) * (∑ m ∈ s, (f m : ℤ) ^ 2) - (∑ m ∈ s, (f m : ℤ)) ^ 2)

/-- **Turán's sieve for the wheels.** The survivors of the wheels among the
positions 1 to `N`, times the total hits squared, are at most `N` times (`N`
times the total squared hits minus the total hits squared), with both totals
given exactly by `hits_sum` and `hits_sq_sum`. -/
def turan_wheels : Prop :=
  ∀ (W : Finset Nat) (N : Nat),
    ((survivors_upto W N).card : ℤ) * (∑ q ∈ W, ((N / q : Nat) : ℤ)) ^ 2 ≤
      (N : ℤ) * ((N : ℤ) * (∑ q ∈ W, ∑ r ∈ W, ((N / Nat.lcm q r : Nat) : ℤ)) -
        (∑ q ∈ W, ((N / q : Nat) : ℤ)) ^ 2)

end RNS.TuranCycle
