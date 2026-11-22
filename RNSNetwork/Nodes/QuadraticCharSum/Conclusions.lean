/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# QuadraticCharSum — on one wheel, the residue character of a pair pattern adds up to −1

On the wheel of a prime `p`, give each position the value +1 if it is a
nonzero square, −1 if it is not a square, and 0 at 0 (the quadratic
character). Take two offsets and multiply the distances of a position from
them. Adding the character of that product around the whole wheel gives −1
when the offsets are different positions on the wheel, and one less than the
wheel size when they coincide. The same −1 holds for any quadratic whose
discriminant is not 0. This is the exact case, degree two, of the bounds of
Hasse and Weil.

Proof: `RNSSolutions/QuadraticCharSum.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.QuadraticCharSum

/-- **Two different offsets.** On an odd prime wheel, the quadratic character
of the product of the distances to two different offsets adds up to −1. -/
def pair_char_sum_distinct : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ a b : ZMod p, a ≠ b →
    ∑ x : ZMod p, quadraticChar (ZMod p) ((x + a) * (x + b)) = -1

/-- **Two equal offsets.** On any prime wheel, the quadratic character of the
square of the distance to one offset adds up to the wheel size minus 1. -/
def pair_char_sum_equal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ a : ZMod p,
    ∑ x : ZMod p, quadraticChar (ZMod p) ((x + a) * (x + a)) = (p : ℤ) - 1

/-- **Any quadratic with nonzero discriminant.** On an odd prime wheel, the
quadratic character of a square plus a multiple plus a constant adds up to −1
whenever the discriminant is not 0, whether or not the quadratic splits. -/
def quadratic_char_sum : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ b c : ZMod p, b ^ 2 - 4 * c ≠ 0 →
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 2 + b * x + c) = -1

end RNS.QuadraticCharSum
