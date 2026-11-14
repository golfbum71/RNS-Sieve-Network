/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# BrocardWindow — where every wheel's marks fall between two prime squares

The window is the numbers strictly between a base prime's square and the next
prime's square. A wheel (a prime up to the base prime) marks the window
numbers it divides; the number it is multiplied by is the mark's row.

Letters used in the statements:

* `q` — the wheel;
* `d` — how far the wheel is below the base prime, so the base prime is `q + d`;
* `i` — the step, a whole number;
* `g` — the gap from the base prime to the next prime;
* the row is `q + 2 * d + 2 * i` (base prime plus distance plus twice the step);
* the center is `q + d + i` (base prime plus step) and the half-gap is `d + i`.

The mark formula says the mark is the center's square minus the half-gap's
square. The collision rule says when two wheels share a slot. The row rules
say what a large or middle wheel's row can be.

Proof: `RNSSolutions/BrocardWindow.lean`. Rests on no other node.
Metadata: `formalization.yaml`. Notes: `docs/BROCARD_NOTES.md`.
-/

namespace RNS.BrocardWindow

/-- **Mark formula.** The wheel times its row, plus the half-gap's square, is
the center's square. -/
def mark_formula : Prop :=
  ∀ q d i : Nat, q * (q + 2 * d + 2 * i) + (d + i) ^ 2 = (q + d + i) ^ 2

/-- **The mark is inside the window** (above the base prime's square and below
the next prime's square) exactly when twice the step times the wheel lies
strictly between the distance squared and the distance squared plus the
window length. -/
def mark_in_window_iff : Prop :=
  ∀ q d i g : Nat,
    ((q + d) ^ 2 < q * (q + 2 * d + 2 * i) ∧ q * (q + 2 * d + 2 * i) < (q + d + g) ^ 2) ↔
      (d ^ 2 < 2 * i * q ∧ 2 * i * q < d ^ 2 + 2 * (q + d) * g + g ^ 2)

/-- **Collision rule, the product.** A slot marked by two different wheels is
a multiple of their product. -/
def collision_product : Prop :=
  ∀ q₁ q₂ n : Nat, q₁.Prime → q₂.Prime → q₁ ≠ q₂ → q₁ ∣ n → q₂ ∣ n → q₁ * q₂ ∣ n

/-- **Collision rule, the cofactor.** If the product of two wheels is below
the base prime's square and the slot `q₁ * q₂ * t` is above it, with `t` on
the 6n±1 tracks (not divisible by 2 or 3), then `t` is at least 5. -/
def collision_cofactor : Prop :=
  ∀ p q₁ q₂ t : Nat, q₁ * q₂ < p ^ 2 → p ^ 2 < q₁ * q₂ * t →
    t % 2 ≠ 0 → t % 3 ≠ 0 → 5 ≤ t

/-- **No collision for a large product.** If five times the product of two
wheels is at least `N` (the next prime's square), every slot they share above
the base prime's square is at least `N`, so they share none in the window. -/
def no_collision_large_product : Prop :=
  ∀ p N q₁ q₂ t : Nat, N ≤ 5 * (q₁ * q₂) → q₁ * q₂ < p ^ 2 → p ^ 2 < q₁ * q₂ * t →
    t % 2 ≠ 0 → t % 3 ≠ 0 → N ≤ q₁ * q₂ * t

/-- **Large-wheel row rule.** If the wheel's cube is at least `N` (the next
prime's square), a row that is a product of two numbers each at least the
wheel puts the mark at or beyond `N`. So inside the window such a wheel's
mark is new only when its row is prime. -/
def large_wheel_row : Prop :=
  ∀ q a b N : Nat, N ≤ q * q * q → q ≤ a → q ≤ b → N ≤ q * (a * b)

/-- **Middle-wheel row rule.** If the wheel's fourth power is at least `N`, a
row that is a product of three numbers each at least the wheel puts the mark
at or beyond `N`. -/
def middle_wheel_row : Prop :=
  ∀ q a b e N : Nat, N ≤ q * q * q * q → q ≤ a → q ≤ b → q ≤ e → N ≤ q * (a * b * e)

end RNS.BrocardWindow
