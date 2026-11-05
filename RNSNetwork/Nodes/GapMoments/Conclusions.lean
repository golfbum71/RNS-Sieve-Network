/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Vocabulary
import Mathlib.Data.Finset.Sort                    -- `Finset.sort`
import Mathlib.Analysis.SpecialFunctions.Pow.Real  -- real powers

/-!
# GapMoments — the survivor gaps are spread as evenly as their average allows

List the survivors of one combined cycle in order. Raise each gap between
consecutive survivors to a fixed power and add them up. Montgomery and
Vaughan (1986) proved Erdős's conjecture that this is at most a constant
(depending only on the power) times the cycle length times the survivor
share raised to one minus the power. That is the size it would have if every
gap were the average gap, so the gaps cannot bunch up to make the total much
larger. Hooley had proved it for powers below 2.

Stated here for the cycle of a set of prime wheels, without the wrap-around
gap from the last survivor to the first survivor of the next cycle; dropping
that one term only makes the sum smaller, so this follows from their theorem.

Cited, not proved in Lean. Its proof needs exponential-sum estimates for the
survivor pattern (node `RamanujanSums` holds the basic evaluation).
Checked numerically on 2026-11-05 for every set of wheels from the primes up
to 13 at powers 1/2, 1, 2 and 3 (constant at most 2.1 there).

Metadata: `formalization.yaml`.
-/

namespace RNS.GapMoments

/-- **The gap-moment bound** (cited). For every positive power `e` there is a
constant `C` such that, for every set of prime wheels, the gaps between
consecutive survivors of one cycle, each raised to the power `e`, add up to
at most `C` times the cycle length times the survivor share to the power
`1 - e`. -/
def gap_moment_bound : Prop :=
  ∀ e : ℝ, 0 < e → ∃ C : ℝ, 0 < C ∧ ∀ W : Finset Nat, (∀ q ∈ W, q.Prime) →
    let L := (survivors_upto W (W.prod id)).sort (· ≤ ·)
    ∑ i ∈ Finset.range (L.length - 1), ((L.getD (i + 1) 0 - L.getD i 0 : Nat) : ℝ) ^ e
      ≤ C * (W.prod id : ℝ)
          * (((survivors_upto W (W.prod id)).card : ℝ) / (W.prod id : ℝ)) ^ (1 - e)

end RNS.GapMoments
