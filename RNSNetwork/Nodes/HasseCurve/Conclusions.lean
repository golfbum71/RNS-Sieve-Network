/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# HasseCurve — three consecutive positions, and Hasse's bound for y² = x³ − x

On the wheel of an odd prime `p`, multiply three consecutive positions
together and ask whether the product is a square. Shifted by one, the product
of three consecutive positions is x³ − x, so the points of the elliptic curve
y² = x³ − x on the wheel are counted by the quadratic character of that
product.

When the wheel size leaves remainder 3 on dividing by 4, the character sum is
exactly 0 and the curve has exactly `p` points with both coordinates on the
wheel (the supersingular case). For every odd prime wheel, the square of the
character sum is at most 4 times the wheel size: Hasse's bound (1933), here
taken from Weil's bound for three offsets (node `StepanovWeil`).

Proof: `RNSSolutions/HasseCurve.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.HasseCurve

/-- **The supersingular sum.** On a prime wheel whose size leaves remainder 3
on dividing by 4, the quadratic character of the product of three consecutive
positions adds up to 0. -/
def three_consecutive_sum_zero : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 →
    ∑ x : ZMod p, quadraticChar (ZMod p) (x * (x + 1) * (x + 2)) = 0

/-- **The supersingular count.** On a prime wheel whose size leaves remainder 3
on dividing by 4, the pairs of positions with the second squared equal to the
product of three consecutive positions starting at the first number exactly the
wheel size. -/
def three_consecutive_point_count : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 →
    (Finset.univ.filter (fun q : ZMod p × ZMod p =>
      q.2 ^ 2 = q.1 * (q.1 + 1) * (q.1 + 2))).card = p

/-- **Hasse's bound.** On every odd prime wheel, the square of the character
sum of the product of three consecutive positions is at most 4 times the wheel
size. -/
def hasse_bound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    (∑ x : ZMod p, quadraticChar (ZMod p) (x * (x + 1) * (x + 2))) ^ 2 ≤ 4 * (p : ℤ)

end RNS.HasseCurve

/-! ## Hasse's bound without Weil: Jacobsthal's sums (added 2026-11-22)

Jacobsthal (1907) twisted the curve: for each position `n` of the wheel, add up
the character of the cube of a position minus `n` times the position. Turning
the wheel by a nonzero factor multiplies `n` by a square and the sum by a
sign; adding the squares of all the twisted sums uses only the two-offset sums
of `QuadraticCharSum`. That bounds the untwisted sum by the square root of four
times the wheel size, with no input from Weil. -/

namespace RNS.HasseCurve

/-- **Jacobsthal's sum** for the twisted curve y² = x³ − n·x: the quadratic
character of the cube of a position minus `n` times the position, added around
the wheel. -/
def jacobsthal_sum (p : ℕ) [Fact p.Prime] (n : ZMod p) : ℤ :=
  ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - n * x)

/-- **Twisting by a square.** Multiplying the twist by the square of a nonzero
position multiplies Jacobsthal's sum by that position's character. -/
def jacobsthal_twist : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ n t : ZMod p, t ≠ 0 →
    jacobsthal_sum p (n * t ^ 2) = quadraticChar (ZMod p) t * jacobsthal_sum p n

/-- **The second moment.** On an odd prime wheel, the squares of Jacobsthal's
sums over all twists add up to the wheel size times the wheel size minus 1
times (1 plus the character of −1). -/
def jacobsthal_second_moment : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∑ n : ZMod p, jacobsthal_sum p n ^ 2 =
      (p : ℤ) * ((p : ℤ) - 1) * (1 + quadraticChar (ZMod p) (-1))

end RNS.HasseCurve
