/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.Real.Basic

/-!
# RandomRotation — rotating every wheel at random

Turn each wheel to a position chosen uniformly at random, independently. By
the Chinese Remainder Theorem every choice of rotations is exactly one shift
of the combined cycle, so choosing the rotations at random is the same as
choosing a shift of the cycle at random. The chance that every member of an
offset pattern survives is then the number of surviving shifts over the cycle
length, and that is the product, over the wheels, of one minus the number of
distinct positions the pattern occupies on that wheel over the wheel size:
exactly the pattern's survivor share.

This is the random-sieve model of Banks, Ford and Tao (survivors of one random
remainder per prime) and the starting point of the large-gap construction
(Ford Lemma 8.4), stated for the frozen wheels below `limit`.

Proof: `RNSSolutions/RandomRotation.lean`. Rests on `CRT`
(`crt_map_bijective`) and `SurvivorCount` (`general_survivor_count`).
Metadata: `formalization.yaml`.
-/

namespace RNS.RandomRotation

/-- **A setting of the wheels is a shift of the cycle.** For every choice of
a position on each active wheel there is exactly one position of the combined
cycle reading as that choice. -/
def rotation_is_shift : Prop :=
  ∀ (limit : Nat) (s : ∀ q : active_primes limit, ZMod (q : Nat)),
    ∃! n : ZMod (primorial_modulus limit), crt_map limit n = s

/-- **The survival chance under random rotations.** The shifts of the cycle
under which every member of the pattern `T` survives every active wheel, as a
share of the cycle length, equal the product over the active wheels of one
minus `w T q` over `q`. -/
def random_rotation_survival : Prop :=
  ∀ (T : Finset Nat) (limit : Nat),
    ((wheel_survivors_gen T limit).card : ℝ) / (primorial_modulus limit : ℝ) =
      ∏ q ∈ active_primes limit, (1 - (w T q : ℝ) / (q : ℝ))

end RNS.RandomRotation
