/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary

/-!
# ColumnAction — how a wheel moves the columns

Multiplying by a number that leaves remainder 1 on division by 6 keeps every
number in its column (its remainder on division by 6 is unchanged).
Multiplying by one that leaves remainder 5 swaps the two columns: the 6n+1
column goes to the 6n-1 column and back. This is the lemma behind every
column form in the network; a prime wheel above 3 always leaves remainder 1
or 5.

Proof: `RNSSolutions/ColumnAction.lean`. Metadata: `formalization.yaml`.
-/

namespace RNS.ColumnAction

/-- **How a wheel moves the columns.** For a multiplier `p` and any number
`n`: if `p` leaves remainder 1 on division by 6, then `p * n` leaves the same
remainder as `n`; if `p` leaves remainder 5, then `p * n` lands in the 6n-1
column when `n` is in the 6n+1 column, and in the 6n+1 column when `n` is in
the 6n-1 column. (No primality is needed.) -/
def column_action : Prop :=
  ∀ (p n : Nat),
    (p % 6 = 1 → (p * n) % 6 = n % 6) ∧
    (p % 6 = 5 → (n % 6 = 1 → (p * n) % 6 = 5) ∧ (n % 6 = 5 → (p * n) % 6 = 1))

end RNS.ColumnAction
