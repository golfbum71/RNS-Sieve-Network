/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.LinearForms.Conclusions
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# BadWheels — which wheels block fewer positions for linear forms

A pattern of linear forms is a finite set of pairs `(a, b)`, each meaning the
form `a·n + b` (the same encoding as `LinearForms`). On the wheel of size `p`
a form blocks the positions where it is divisible by `p`. When `a` and `b`
share no factor, a form blocks at most one position, so the pattern blocks at
most as many positions as it has forms. It blocks exactly that many unless
the wheel divides the *bad product*: the product of the leading coefficients
times the product of all cross differences `a·b' − a'·b` (over ordered pairs
of distinct forms; the sign does not matter for divisibility). A wheel
dividing a leading coefficient blocks nothing for that form; a wheel dividing
a cross difference makes two forms block the same position.

For the two columns 6n−1 and 6n+1, written as the forms `6n + 5` and `6n + 7`,
the bad product is −5184 = −2^6·3^4, so the wheels 2 and 3 are exactly the
exceptions: removing the bad wheels is the 6n±1 wheel.

Ford's Lemma 7.7: numbers dividing the forms at the same position, each
sharing no factor with the bad product, share no factor with one another.

Proof: `RNSSolutions/BadWheels.lean`. Uses the definitions of `LinearForms`
(the encoding of a form); takes none of its claims.
Metadata: `formalization.yaml`.
-/

namespace RNS.BadWheels

/-- The positions (remainders below `p`) blocked by the form `ℓ`: those where
`ℓ.1 · r + ℓ.2` is divisible by `p` (`LinearForms.form_blocked_at`). -/
def form_roots (ℓ : Nat × Nat) (p : Nat) : Finset Nat :=
  (Finset.range p).filter (fun r => (ℓ.1 * r + ℓ.2) % p = 0)

/-- The positions on the wheel of size `p` blocked by some form of `L`. -/
def blocked (L : Finset (Nat × Nat)) (p : Nat) : Finset Nat :=
  (Finset.range p).filter (fun r => ∃ ℓ ∈ L, (ℓ.1 * r + ℓ.2) % p = 0)

/-- The cross difference `a·b' − a'·b` of two forms. -/
def cross (ℓ ℓ' : Nat × Nat) : ℤ := (ℓ.1 : ℤ) * ℓ'.2 - (ℓ'.1 : ℤ) * ℓ.2

/-- The bad product: the leading coefficients times the cross differences of
all ordered pairs of distinct forms. -/
def bad_product (L : Finset (Nat × Nat)) : ℤ :=
  (∏ ℓ ∈ L, (ℓ.1 : ℤ)) * ∏ e ∈ L.offDiag, cross e.1 e.2

/-- **At most one position per form.** -/
def blocked_le_card : Prop :=
  ∀ (L : Finset (Nat × Nat)) (p : Nat), p.Prime → (∀ ℓ ∈ L, Nat.Coprime ℓ.1 ℓ.2) →
    (blocked L p).card ≤ L.card

/-- **Exactly one per form unless the wheel divides the bad product.** -/
def blocked_eq_card_iff : Prop :=
  ∀ (L : Finset (Nat × Nat)) (p : Nat), p.Prime → (∀ ℓ ∈ L, Nat.Coprime ℓ.1 ℓ.2) →
    ((blocked L p).card = L.card ↔ ¬ (p : ℤ) ∣ bad_product L)

/-- **The two columns: the bad wheels are 2 and 3.** The forms `6n + 5` and
`6n + 7` block fewer than two positions on a prime wheel exactly when the
wheel is 2 or 3. -/
def twin_columns_bad_wheels : Prop :=
  ∀ p : Nat, p.Prime → ((blocked {(6, 5), (6, 7)} p).card < 2 ↔ p = 2 ∨ p = 3)

/-- **Ford's Lemma 7.7.** If at the position `n` each form `ℓ` is divisible by
`d ℓ`, and each `d ℓ` shares no factor with the bad product, then the `d ℓ`
of different forms share no factor. -/
def divisors_pairwise_coprime : Prop :=
  ∀ (L : Finset (Nat × Nat)) (n : Nat) (d : Nat × Nat → Nat),
    (∀ ℓ ∈ L, d ℓ ∣ ℓ.1 * n + ℓ.2) → (∀ ℓ ∈ L, Nat.Coprime (d ℓ) (bad_product L).natAbs) →
    ∀ ℓ ∈ L, ∀ ℓ' ∈ L, ℓ ≠ ℓ' → Nat.Coprime (d ℓ) (d ℓ')

end RNS.BadWheels
