/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# SophieGermainPowers — on the wheel of size 2p+1, p-th powers have three positions

Let `p` be a Sophie Germain prime, so `2p + 1` is prime too, and take the
wheel of size `2p + 1`. Raising any number to the `p`-th power lands it on
only three of the wheel's positions: 0 (when the wheel blocks the number),
1, or the last position (one less than the wheel size, written -1). The
reason is Fermat's little theorem: a number the wheel does not block, raised
to the power `2p`, is back at position 1, so its `p`-th power squares to 1.

Consequence: three `p`-th powers whose sum the wheel blocks cannot all sit at
1 or -1, since the sums of three of those are 3, 1, -1 or -3, and the wheel
(of size at least 5) blocks none of them. So the wheel blocks one of the
three numbers themselves.

These are the two wheel facts behind Sophie Germain's theorem (node
`SophieGermainTheorem`), where they are used twice: once on a solution of
x^p + y^p + z^p = 0, and once on the p-th roots of its pairwise sums.

Proof: `RNSSolutions/SophieGermainPowers.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.SophieGermainPowers

/-- **Three positions for p-th powers.** For a prime `p` with `2p + 1` prime,
every integer's `p`-th power sits at position 0, 1 or -1 on the wheel of size
`2p + 1`. -/
def pth_power_positions : Prop :=
  ∀ p : Nat, p.Prime → (2 * p + 1).Prime → ∀ t : Int,
    ((t ^ p : Int) : ZMod (2 * p + 1)) = 0 ∨ ((t ^ p : Int) : ZMod (2 * p + 1)) = 1 ∨
      ((t ^ p : Int) : ZMod (2 * p + 1)) = -1

/-- **Three p-th powers: the wheel blocks one.** For a prime `p` with `2p + 1`
prime, if the wheel of size `2p + 1` divides `x^p + y^p + z^p`, it divides one
of `x`, `y`, `z`. -/
def three_powers_blocked : Prop :=
  ∀ p : Nat, p.Prime → (2 * p + 1).Prime → ∀ x y z : Int,
    ((2 * p + 1 : Nat) : Int) ∣ x ^ p + y ^ p + z ^ p →
      ((2 * p + 1 : Nat) : Int) ∣ x ∨ ((2 * p + 1 : Nat) : Int) ∣ y ∨
        ((2 * p + 1 : Nat) : Int) ∣ z

end RNS.SophieGermainPowers
