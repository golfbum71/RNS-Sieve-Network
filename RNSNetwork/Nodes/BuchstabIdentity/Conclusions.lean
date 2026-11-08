/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# BuchstabIdentity — adding wheels, counted by the first wheel that blocks

Legendre's recurrence for `phi(x, a)`: bringing one more prime wheel into a
set of prime wheels removes exactly the survivors of the earlier wheels among
the multiples of the new prime, and those multiples, divided by the new prime,
are the survivors of the earlier wheels up to the bound divided by the prime.

Buchstab's identity adds several wheels at once: the survivors of the old and
new wheels together are the survivors of the old wheels, minus, for each new
wheel, the positions it is the first new wheel to block. Those are the
multiples of that wheel which no old wheel and no smaller new wheel blocks,
counted as survivors up to the bound divided by that wheel.

The product form is the same bookkeeping for shares: the share escaping every
new wheel is one minus, over each new wheel, its share times the share
escaping the smaller new wheels.

Proof: `RNSSolutions/BuchstabIdentity.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.BuchstabIdentity

/-- **Legendre's recurrence.** For prime wheels `W` and a new prime wheel `q`
not among them, the survivors of `W` and `q` up to `N`, plus the survivors of
`W` up to `N / q`, are the survivors of `W` up to `N`. -/
def legendre_phi_recurrence : Prop :=
  ∀ (W : Finset Nat) (q N : Nat), (∀ r ∈ W, r.Prime) → q.Prime → q ∉ W →
    (survivors_upto (insert q W) N).card + (survivors_upto W (N / q)).card =
      (survivors_upto W N).card

/-- **Buchstab's identity.** For prime wheels `W` and further prime wheels `E`
(none of them in `W`), the survivors of all of them up to `N` are the
survivors of `W` up to `N`, minus, for each new wheel `q` in `E`, the
survivors up to `N / q` of `W` together with the new wheels smaller than `q`
(the positions `q` is the first new wheel to block). -/
def buchstab_identity : Prop :=
  ∀ (W E : Finset Nat) (N : Nat), (∀ r ∈ W, r.Prime) → (∀ r ∈ E, r.Prime) → Disjoint W E →
    ((survivors_upto (W ∪ E) N).card : ℤ) =
      ((survivors_upto W N).card : ℤ) -
        ∑ q ∈ E, ((survivors_upto (W ∪ E.filter (fun r => r < q)) (N / q)).card : ℤ)

/-- **The product form.** For any shares `x` of the wheels in `E`, the
product of one minus each share is one minus, over each wheel `q`, its share
times the product of one minus the shares of the wheels smaller than `q`. -/
def buchstab_product_identity : Prop :=
  ∀ (E : Finset Nat) (x : Nat → ℝ),
    ∏ q ∈ E, (1 - x q) = 1 - ∑ q ∈ E, x q * ∏ r ∈ E.filter (fun r => r < q), (1 - x r)

end RNS.BuchstabIdentity
