/-
Copyright (c) 2026 Geoffrey Fischer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Fischer
-/
import RNSSolutions.Wheel6
import RNSSolutions.CRT
import RNSSolutions.SquareRootShield
import RNSSolutions.Admissibility
import RNSSolutions.SurvivorCount
import RNSSolutions.SingularSeries
import RNSSolutions.TwinConstant
import RNSSolutions.Pruning
import RNSSolutions.WheelOrder
import RNSSolutions.ShieldCertificates
import RNSSolutions.Infinitude
import RNSSolutions.ColumnStructure
import RNSSolutions.DirichletColumns
import RNSSolutions.HardyLittlewood
import RNSSolutions.HensleyRichards
import RNSSolutions.LinearForms
import RNSSolutions.GapConjectures
import RNSSolutions.SophieGermainWheel
import RNSSolutions.GapTracks
import RNSSolutions.UniformSubdivision
import RNSSolutions.LehmerSplit
import RNSSolutions.Sawtooth
import RNSSolutions.SpreadBounds
import RNSSolutions.TwinShare
import RNSSolutions.LehmerExcess
import RNSSolutions.ShareBounds

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

/-- `SurvivorCount` → `Pruning`. -/
theorem RNS.Pruning.valid_starting_residues_card_formula_holds : RNS.Pruning.valid_starting_residues_card_formula :=
  RNS.Pruning.valid_starting_residues_card_formula_step RNS.SurvivorCount.general_survivor_count_holds

/-- `SquareRootShield` → `ShieldCertificates`. -/
theorem RNS.ShieldCertificates.prime_of_shield_cover_holds : RNS.ShieldCertificates.prime_of_shield_cover :=
  RNS.ShieldCertificates.prime_of_shield_cover_step RNS.SquareRootShield.square_root_shield_holds

/-- `SquareRootShield` → `ShieldCertificates`. -/
theorem RNS.ShieldCertificates.family_prime_of_shield_cover_holds : RNS.ShieldCertificates.family_prime_of_shield_cover :=
  RNS.ShieldCertificates.family_prime_of_shield_cover_step RNS.SquareRootShield.square_root_shield_holds

/-- `SquareRootShield` → `ShieldCertificates`. -/
theorem RNS.ShieldCertificates.forward_ap_prime_of_active_shield_holds : RNS.ShieldCertificates.forward_ap_prime_of_active_shield :=
  RNS.ShieldCertificates.forward_ap_prime_of_active_shield_step RNS.SquareRootShield.square_root_shield_holds

/-- `SquareRootShield` → `ShieldCertificates`. -/
theorem RNS.ShieldCertificates.backward_ap_prime_of_active_shield_holds : RNS.ShieldCertificates.backward_ap_prime_of_active_shield :=
  RNS.ShieldCertificates.backward_ap_prime_of_active_shield_step RNS.SquareRootShield.square_root_shield_holds

/-- `SquareRootShield` → `ShieldCertificates`. -/
theorem RNS.ShieldCertificates.tuple_prime_of_active_shield_holds : RNS.ShieldCertificates.tuple_prime_of_active_shield :=
  RNS.ShieldCertificates.tuple_prime_of_active_shield_step RNS.SquareRootShield.square_root_shield_holds

/-- `SquareRootShield` → `ShieldCertificates`. -/
theorem RNS.ShieldCertificates.window_prime_iff_holds : RNS.ShieldCertificates.window_prime_iff :=
  RNS.ShieldCertificates.window_prime_iff_step RNS.SquareRootShield.square_root_shield_holds

/-- `SquareRootShield` → `ShieldCertificates`. -/
theorem RNS.ShieldCertificates.window_twin_iff_holds : RNS.ShieldCertificates.window_twin_iff :=
  RNS.ShieldCertificates.window_twin_iff_step RNS.SquareRootShield.square_root_shield_holds

/-- `Wheel6` → `ColumnStructure`. -/
theorem RNS.ColumnStructure.col_minus_has_minus_prime_factor_holds : RNS.ColumnStructure.col_minus_has_minus_prime_factor :=
  RNS.ColumnStructure.col_minus_has_minus_prime_factor_step RNS.Wheel6.prime_gt_three_is_candidate_holds

/-- `Wheel6` → `ColumnStructure`. -/
theorem RNS.ColumnStructure.col_minus_composite_has_proper_minus_factor_holds : RNS.ColumnStructure.col_minus_composite_has_proper_minus_factor :=
  RNS.ColumnStructure.col_minus_composite_has_proper_minus_factor_step RNS.Wheel6.prime_gt_three_is_candidate_holds

/-- `SingularSeries`, `Admissibility` → `HardyLittlewood`. -/
theorem RNS.HardyLittlewood.twin_prime_conjecture_implies_infinite_twin_primes_holds : RNS.HardyLittlewood.twin_prime_conjecture_implies_infinite_twin_primes :=
  RNS.HardyLittlewood.twin_prime_conjecture_implies_infinite_twin_primes_step RNS.SingularSeries.hardy_littlewood_constant_pos_holds RNS.Admissibility.zero_two_admissible_holds

/-- `Wheel6` → `SophieGermainWheel`. -/
theorem RNS.SophieGermainWheel.sophie_germain_mod_six_holds : RNS.SophieGermainWheel.sophie_germain_mod_six :=
  RNS.SophieGermainWheel.sophie_germain_mod_six_step RNS.Wheel6.prime_gt_three_is_candidate_holds

/-- `WheelOrder` → `SophieGermainWheel`. -/
theorem RNS.SophieGermainWheel.sophie_germain_last_digit_holds : RNS.SophieGermainWheel.sophie_germain_last_digit :=
  RNS.SophieGermainWheel.sophie_germain_last_digit_step RNS.WheelOrder.prime_gt_five_digit_ok_holds

/-- `Wheel6` → `GapTracks`. -/
theorem RNS.GapTracks.twin_prime_mod_six_holds : RNS.GapTracks.twin_prime_mod_six :=
  RNS.GapTracks.twin_prime_mod_six_step RNS.Wheel6.prime_gt_three_is_candidate_holds

/-- `Wheel6` → `GapTracks`. -/
theorem RNS.GapTracks.cousin_prime_mod_six_holds : RNS.GapTracks.cousin_prime_mod_six :=
  RNS.GapTracks.cousin_prime_mod_six_step RNS.Wheel6.prime_gt_three_is_candidate_holds

/-- `Wheel6` → `GapTracks`. -/
theorem RNS.GapTracks.prime_gap_forbidden_four_from_six_minus_one_holds : RNS.GapTracks.prime_gap_forbidden_four_from_six_minus_one :=
  RNS.GapTracks.prime_gap_forbidden_four_from_six_minus_one_step RNS.Wheel6.prime_gt_three_is_candidate_holds

/-- `Wheel6` → `GapTracks`. -/
theorem RNS.GapTracks.prime_gap_forbidden_two_from_six_plus_one_holds : RNS.GapTracks.prime_gap_forbidden_two_from_six_plus_one :=
  RNS.GapTracks.prime_gap_forbidden_two_from_six_plus_one_step RNS.Wheel6.prime_gt_three_is_candidate_holds

/-- `Wheel6` → `GapTracks`. -/
theorem RNS.GapTracks.prime_gap_same_track_of_six_dvd_holds : RNS.GapTracks.prime_gap_same_track_of_six_dvd :=
  RNS.GapTracks.prime_gap_same_track_of_six_dvd_step RNS.Wheel6.prime_gt_three_is_candidate_holds

#print axioms RNS.SurvivorCount.twin_survivor_count_holds
#print axioms RNS.SurvivorCount.general_survivor_count_holds
#print axioms RNS.SingularSeries.local_density_factorization_holds
#print axioms RNS.TwinConstant.twin_prime_constant_eq_classical_holds
#print axioms RNS.Pruning.valid_starting_residues_card_formula_holds
#print axioms RNS.ShieldCertificates.prime_of_shield_cover_holds
#print axioms RNS.ShieldCertificates.family_prime_of_shield_cover_holds
#print axioms RNS.ShieldCertificates.forward_ap_prime_of_active_shield_holds
#print axioms RNS.ShieldCertificates.backward_ap_prime_of_active_shield_holds
#print axioms RNS.ShieldCertificates.tuple_prime_of_active_shield_holds
#print axioms RNS.ShieldCertificates.window_prime_iff_holds
#print axioms RNS.ShieldCertificates.window_twin_iff_holds
#print axioms RNS.ColumnStructure.col_minus_has_minus_prime_factor_holds
#print axioms RNS.ColumnStructure.col_minus_composite_has_proper_minus_factor_holds
#print axioms RNS.HardyLittlewood.twin_prime_conjecture_implies_infinite_twin_primes_holds
#print axioms RNS.SophieGermainWheel.sophie_germain_mod_six_holds
#print axioms RNS.SophieGermainWheel.sophie_germain_last_digit_holds
#print axioms RNS.GapTracks.twin_prime_mod_six_holds
#print axioms RNS.GapTracks.cousin_prime_mod_six_holds
#print axioms RNS.GapTracks.prime_gap_forbidden_four_from_six_minus_one_holds
#print axioms RNS.GapTracks.prime_gap_forbidden_two_from_six_plus_one_holds
#print axioms RNS.GapTracks.prime_gap_same_track_of_six_dvd_holds

/-- `UniformSubdivision` → `LehmerSplit` (whole count). -/
theorem RNS.LehmerSplit.lehmer_even_split_holds : RNS.LehmerSplit.lehmer_even_split :=
  RNS.LehmerSplit.lehmer_even_split_step RNS.UniformSubdivision.frozen_wheels_repeat_holds
    RNS.UniformSubdivision.one_wheel_removed_holds

/-- `UniformSubdivision` → `LehmerSplit` (each column). -/
theorem RNS.LehmerSplit.lehmer_even_split_column_holds :
    RNS.LehmerSplit.lehmer_even_split_column :=
  RNS.LehmerSplit.lehmer_even_split_column_step
    RNS.UniformSubdivision.column_frozen_repeat_holds
    RNS.UniformSubdivision.column_one_wheel_removed_holds

#print axioms RNS.LehmerSplit.lehmer_even_split_holds
#print axioms RNS.LehmerSplit.lehmer_even_split_column_holds

/-- `Sawtooth` → `SpreadBounds`. -/
theorem RNS.SpreadBounds.interval_spread_bound_holds : RNS.SpreadBounds.interval_spread_bound :=
  RNS.SpreadBounds.interval_spread_bound_step RNS.Sawtooth.legendre_count_holds

#print axioms RNS.SpreadBounds.interval_spread_bound_holds

/-- `SurvivorCount` → `TwinShare`. -/
theorem RNS.TwinShare.twin_share_eq_prod_holds : RNS.TwinShare.twin_share_eq_prod :=
  RNS.TwinShare.twin_share_eq_prod_step RNS.SurvivorCount.twin_survivor_count_holds
    RNS.SurvivorCount.general_survivor_count_holds

#print axioms RNS.TwinShare.twin_share_eq_prod_holds

/-- `Sawtooth` → `SpreadBounds` (columns). -/
theorem RNS.SpreadBounds.column_imbalance_bound_holds :
    RNS.SpreadBounds.column_imbalance_bound :=
  RNS.SpreadBounds.column_imbalance_bound_step RNS.Sawtooth.column_legendre_count_holds

#print axioms RNS.SpreadBounds.column_imbalance_bound_holds

/-- `Sawtooth` → `LehmerExcess`. -/
theorem RNS.LehmerExcess.lehmer_excess_closed_form_holds :
    RNS.LehmerExcess.lehmer_excess_closed_form :=
  RNS.LehmerExcess.lehmer_excess_closed_form_step RNS.Sawtooth.sawtooth_identity_holds

#print axioms RNS.LehmerExcess.lehmer_excess_closed_form_holds

/-- `SurvivorCount` → `ShareBounds` (plain share). -/
theorem RNS.ShareBounds.survivor_share_le_inv_log_holds : RNS.ShareBounds.survivor_share_le_inv_log :=
  RNS.ShareBounds.survivor_share_le_inv_log_step RNS.SurvivorCount.general_survivor_count_holds

/-- `SurvivorCount` → `ShareBounds` (twin share). -/
theorem RNS.ShareBounds.twin_share_le_two_inv_log_sq_holds :
    RNS.ShareBounds.twin_share_le_two_inv_log_sq :=
  RNS.ShareBounds.twin_share_le_two_inv_log_sq_step RNS.SurvivorCount.twin_survivor_count_holds
    RNS.SurvivorCount.general_survivor_count_holds

#print axioms RNS.ShareBounds.survivor_share_le_inv_log_holds
#print axioms RNS.ShareBounds.twin_share_le_two_inv_log_sq_holds
