/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# WheelOrder — what each wheel adds when wheels arrive in order

Bringing wheels in one at a time, the positions a wheel blocks for the first
time equal the open positions left by every earlier wheel times the full size
of every later wheel. Separately, every prime above 5 ends in 1, 3, 7 or 9,
and from any 6n±1 position the next number with a chosen last digit is
reached in the raw digit distance or at most one further step of 10.

Proof: `RNSSolutions/WheelOrder.lean`; rests on no other node. Metadata:
`formalization.yaml`.

Source of record: `rns_sieve_6.lean`, Part F (`wheel_marginal_new_formula`)
and Part G (`prime_gt_five_digit_ok`, `digit_gap`, `wheel_gap_floor`). Part F's
count `new_wheel_count` is written out here as the set it counts.
-/

namespace RNS.WheelOrder

/-- **The marginal contribution of one wheel.** For distinct primes `before`
brought in first, then the prime `p`, then any further moduli `after`: the
positions of the full cycle that `p` blocks while every earlier wheel leaves
them open number exactly the product of (each earlier wheel size minus one),
times the product of the later moduli. -/
def wheel_marginal_new_formula : Prop :=
  ∀ (before : List Nat) (p : Nat) (after : List Nat),
    p.Prime → (∀ q ∈ before, q.Prime) → before.Nodup → p ∉ before →
      ((Finset.range ((before ++ p :: after).prod)).filter
          (fun x => p ∣ x ∧ ∀ q ∈ before, ¬ q ∣ x)).card
        = (before.map (· - 1)).prod * after.prod

/-- **Every prime above 5 passes the last-digit wheel.** -/
def prime_gt_five_digit_ok : Prop :=
  ∀ p : Nat, p.Prime → p > 5 → digit_ok p = true

/-- The forward distance, from 1 to 10, from a number ending in digit `a` to
the next number ending in digit `b` (a full lap of 10 when `a = b`). Defined
here because only this node uses it. -/
def digit_gap (a b : Nat) : Nat :=
  let r := (b + 10 - a % 10) % 10
  if r = 0 then 10 else r

/-- **The wheel-gap floor.** From any number on the 6n±1 wheel, stepping
forward by the raw last-digit distance to a target digit 1, 3, 7 or 9 lands
on the wheel again, or does after exactly one further step of 10. -/
def wheel_gap_floor : Prop :=
  ∀ n b : Nat, is_candidate n = true → (b = 1 ∨ b = 3 ∨ b = 7 ∨ b = 9) →
    is_candidate (n + digit_gap (n % 10) b) = true ∨
      is_candidate (n + digit_gap (n % 10) b + 10) = true

end RNS.WheelOrder
