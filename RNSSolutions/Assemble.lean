/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSSolutions.CRT
import RNSSolutions.SurvivorCount
import RNSSolutions.SingularSeries
import RNSSolutions.TwinConstant

/-!
# Assembling the network

Every proof file under `RNSSolutions/` imports claims only. A conclusion that
rests on another node is proved there as a `…_step`, taking that node's
claim as a named hypothesis: one Lean-checked arrow of the graph each.

This file is where the arrows are joined up. Each theorem below plugs
finished proofs into a step's hypotheses, giving the conclusion outright.
Each is one line, because all the mathematics is already in the step and in
the upstream proof.
-/

/-- `CRT` → `SurvivorCount` (twin pattern). -/
theorem RNS.SurvivorCount.twin_survivor_count_holds : RNS.SurvivorCount.twin_survivor_count :=
  RNS.SurvivorCount.twin_survivor_count_step RNS.CRT.crt_map_bijective_holds

/-- `CRT` → `SurvivorCount` (any pattern). -/
theorem RNS.SurvivorCount.general_survivor_count_holds :
    RNS.SurvivorCount.general_survivor_count :=
  RNS.SurvivorCount.general_survivor_count_step RNS.CRT.crt_map_bijective_holds

/-- `SurvivorCount` → `SingularSeries` (local density). -/
theorem RNS.SingularSeries.local_density_factorization_holds :
    RNS.SingularSeries.local_density_factorization :=
  RNS.SingularSeries.local_density_factorization_step
    RNS.SurvivorCount.general_survivor_count_holds

/-- `SingularSeries` → `TwinConstant`. -/
theorem RNS.TwinConstant.twin_prime_constant_eq_classical_holds :
    RNS.TwinConstant.twin_prime_constant_eq_classical :=
  RNS.TwinConstant.twin_prime_constant_eq_classical_step
    RNS.SingularSeries.factor_multipliable_holds

#print axioms RNS.SurvivorCount.twin_survivor_count_holds
#print axioms RNS.SurvivorCount.general_survivor_count_holds
#print axioms RNS.SingularSeries.local_density_factorization_holds
#print axioms RNS.TwinConstant.twin_prime_constant_eq_classical_holds
