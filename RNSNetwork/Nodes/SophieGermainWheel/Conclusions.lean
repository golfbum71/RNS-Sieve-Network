/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# SophieGermainWheel — where Sophie Germain primes can sit

Every Sophie Germain prime above 3 lies in the 6n-1 column; none ends in the
digit 7; so above 5 its last digit is 1, 3 or 9. These narrow where to look;
they say nothing about whether there are infinitely many (that is
`LinearForms`).

Proof: `RNSSolutions/SophieGermainWheel.lean`. The column claim assumes
`Wheel6.prime_gt_three_is_candidate`; the last-digit claim assumes
`WheelOrder.prime_gt_five_digit_ok`. Metadata: `formalization.yaml`.

Source of record: `sophie_germain_wheel.lean`.
-/

namespace RNS.SophieGermainWheel

/-- **Sophie Germain primes sit in the 6n-1 column.** Every Sophie Germain
prime above 3 leaves remainder 5 on division by 6. -/
def sophie_germain_mod_six : Prop :=
  ∀ p : Nat, sophie_germain p → 3 < p → p % 6 = 5

/-- **No Sophie Germain prime ends in 7.** (Its double plus one would end in
5.) -/
def sophie_germain_not_ends_in_seven : Prop :=
  ∀ p : Nat, sophie_germain p → p % 10 ≠ 7

/-- **The last digit of a Sophie Germain prime above 5 is 1, 3 or 9.** -/
def sophie_germain_last_digit : Prop :=
  ∀ p : Nat, sophie_germain p → 5 < p → p % 10 = 1 ∨ p % 10 = 3 ∨ p % 10 = 9

end RNS.SophieGermainWheel
