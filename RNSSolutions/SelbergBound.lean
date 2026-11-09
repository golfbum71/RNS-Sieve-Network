/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSNetwork.Nodes.SelbergBound.Conclusions
import RNSSolutions.SelbergBound.Selberg

/-!
# Proofs for SelbergBound

Built clean by `lake build RNSSolutions` on 2026-11-09; `#print axioms` shows only
the standard three.

Rests on no other node. The work is in `RNSSolutions/SelbergBound/` (`Aux`,
`Basic`, `Selberg`): Arend Mellendijk's Selberg sieve from PrimeNumberTheoremAnd
(commit 127b50e), ported here so this repository's build checks it. Besides imports and one namespace
name, three proof steps needed small changes for current Mathlib; each is noted in
its file's header.

The bridge: PrimeNumberTheoremAnd writes the Selberg terms with `1 / (1 - ν p)`
where Mathlib writes `(1 - ν p)⁻¹`; the two bounding sums agree term by term.
-/

namespace RNS.SelbergBound

open BoundingSieve

/-- The node's bounding sum is PrimeNumberTheoremAnd's `selbergBoundingSum`. -/
private theorem bounding_sum_eq (s : SelbergSieve) :
    bounding_sum s = SelbergSieve.selbergBoundingSum s := by
  unfold bounding_sum
  rw [SelbergSieve.selbergBoundingSum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hg : s.toBoundingSieve.selbergTerms l =
      SelbergSieve.selbergTerms s.toBoundingSieve l := by
    simp only [BoundingSieve.selbergTerms_apply, SelbergSieve.selbergTerms_apply, one_div]
  rw [hg]
  first | done | rfl | simp only [Nat.cast_pow]

theorem bounding_sum_pos_holds : bounding_sum_pos := by
  intro s
  rw [bounding_sum_eq]
  exact s.selbergBoundingSum_pos

theorem selberg_bound_holds : selberg_bound := by
  intro s
  rw [bounding_sum_eq]
  exact s.selberg_bound_simple

end RNS.SelbergBound

#print axioms RNS.SelbergBound.bounding_sum_pos_holds
#print axioms RNS.SelbergBound.selberg_bound_holds
