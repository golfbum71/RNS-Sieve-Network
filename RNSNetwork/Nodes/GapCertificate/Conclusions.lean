/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# GapCertificate — the Lacampagne-Selfridge counterexample

Freeze the wheels below a bound. A survivor is a number sharing no factor
with their combined cycle; a survivor gap is the distance from one survivor to
the next, every number strictly between being blocked by some wheel.

For the wheels up to 13 (cycle 30030) the survivor gaps take every even value
up to the largest gap, 22, except 20. This settles two historical guesses at
this cycle:

* **de Polignac (1849)** guessed that, for two neighbouring wheels, every even
  number up to twice the smaller one is a survivor gap of the cycle of wheels
  up to the larger. For the neighbouring wheels 11 and 13 that predicts every
  even gap up to 22, and 20 is missing, so the guess is false
  (`de_polignac_gap_guess_false`).
* **Erdős** (Oberwolfach, c. 1986; Erdős Problem 854) first expected every
  even value up to the largest gap to appear; Lacampagne and Selfridge found
  it fails for the wheels up to 13 (`erdos_first_guess_fails_at_13`). Erdős
  asked it for large enough cycles, so that eventual form stays open; this
  node does not claim it.

Every survivor gap is even once the wheel 2 is in (`survivor_gaps_even`).

Proof: `RNSSolutions/GapCertificate.lean`. Rests on no other node.
Metadata: `formalization.yaml`.
-/

namespace RNS.GapCertificate

/-- `survivor_gap limit g`: the distance `g` occurs between two consecutive
survivors of the wheels below `limit`. Some survivor `x` is followed by the
survivor `x + g`, and every number strictly between them is blocked. -/
def survivor_gap (limit g : Nat) : Prop :=
  ∃ x : Nat, Nat.gcd x (primorial_modulus limit) = 1 ∧
    Nat.gcd (x + g) (primorial_modulus limit) = 1 ∧
    ∀ j : Nat, 0 < j → j < g → Nat.gcd (x + j) (primorial_modulus limit) ≠ 1

/-- **Every survivor gap is even** once the wheel 2 is in (bound at least 3). -/
def survivor_gaps_even : Prop :=
  ∀ limit g : Nat, 3 ≤ limit → survivor_gap limit g → 2 ∣ g

/-- **The gap 20 never occurs** for the wheels up to 13 (cycle 30030). -/
def survivor_gaps_30030_miss_20 : Prop :=
  ¬ survivor_gap 14 20

/-- **Every other even gap up to 22 does occur** for the wheels up to 13. -/
def survivor_gaps_30030_present : Prop :=
  ∀ g ∈ ({2, 4, 6, 8, 10, 12, 14, 16, 18, 22} : Finset Nat), survivor_gap 14 g

/-- de Polignac's guess (1849), as recorded by Ziller (2020): for neighbouring
wheels, the smaller `r` and the larger `q`, every positive even number up to
twice `r` is a survivor gap of the wheels up to `q` (bound `q + 1`). Stated
here only to be refuted. -/
def de_polignac_gap_guess : Prop :=
  ∀ r q : Nat, consecutive_primes r q → ∀ g : Nat, 0 < g → 2 ∣ g → g ≤ 2 * r →
    survivor_gap (q + 1) g

/-- **de Polignac's guess is false**: it fails for the neighbouring wheels 11
and 13. -/
def de_polignac_gap_guess_false : Prop :=
  ¬ de_polignac_gap_guess

/-- **Erdős's first guess fails for the wheels up to 13**: the gap 22 occurs,
the smaller even number 20 does not. -/
def erdos_first_guess_fails_at_13 : Prop :=
  survivor_gap 14 22 ∧ ¬ survivor_gap 14 20

end RNS.GapCertificate
