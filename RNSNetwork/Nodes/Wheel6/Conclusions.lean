/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# Wheel6 — the 6n±1 wheel

Every prime above 3 leaves remainder 1 or 5 on division by 6, so it sits in
one of the two columns 6n-1 and 6n+1.

This file states the claim only. The proof lives in
`RNSSolutions/Wheel6.lean`; what the claim rests on and how it is justified
is recorded in `formalization.yaml` beside this file.

Source of record: `rns_sieve_6.lean`, Part A, Step 1
(`prime_gt_three_is_candidate`).
-/

namespace RNS.Wheel6

/-- **Every prime above 3 passes the mod-6 wheel.** For every prime number
greater than 3, `is_candidate` returns `true`: its remainder on division by 6
is 1 or 5. -/
def prime_gt_three_is_candidate : Prop :=
  ∀ p : Nat, p.Prime → p > 3 → is_candidate p = true

end RNS.Wheel6
