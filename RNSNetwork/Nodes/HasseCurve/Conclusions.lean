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
