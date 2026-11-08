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
import RNSSolutions.SurvivorSymmetry
import RNSSolutions.SpreadBounds
import RNSSolutions.TwinShare
import RNSSolutions.LehmerExcess
import RNSSolutions.ShareBounds
import RNSSolutions.BlockingRuns
import RNSSolutions.SophieGermainPowers
import RNSSolutions.SophieGermainTheorem
import RNSSolutions.GermainAuxiliary
import RNSSolutions.BonseCeiling
import RNSSolutions.Schatunowsky
import RNSSolutions.GermainCriterion
import RNSSolutions.HurwitzZetaZero
import RNSSolutions.FortunateCeiling
import RNSSolutions.BrunPureSieve
import RNSSolutions.BrunTwinCount
import RNSSolutions.BrunTruncation
import RNSSolutions.BrunTwinBound
import RNSSolutions.MertensSecond
import RNSSolutions.BrunAnalytic
import RNSSolutions.BrunTheorem
import RNSSolutions.BrunTwinSum
import RNSSolutions.RandomRotation

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

/-- `CRT` → `BlockingRuns` (settings are shifts). -/
theorem RNS.BlockingRuns.blocked_run_is_shift_holds : RNS.BlockingRuns.blocked_run_is_shift :=
  RNS.BlockingRuns.blocked_run_is_shift_step RNS.CRT.crt_map_bijective_holds

/-- `BlockingRuns`: the longest blocked run, from settings being shifts. -/
theorem RNS.BlockingRuns.longest_blocked_run_eq_max_gap_sub_one_holds :
    RNS.BlockingRuns.longest_blocked_run_eq_max_gap_sub_one :=
  RNS.BlockingRuns.longest_blocked_run_eq_max_gap_sub_one_step
    RNS.BlockingRuns.blocked_run_is_shift_holds

#print axioms RNS.BlockingRuns.blocked_run_is_shift_holds
#print axioms RNS.BlockingRuns.longest_blocked_run_eq_max_gap_sub_one_holds

/-- `SophieGermainPowers` → `SophieGermainTheorem`. -/
theorem RNS.SophieGermainTheorem.sophie_germain_theorem_holds :
    RNS.SophieGermainTheorem.sophie_germain_theorem :=
  RNS.SophieGermainTheorem.sophie_germain_theorem_step
    RNS.SophieGermainPowers.pth_power_positions_holds
    RNS.SophieGermainPowers.three_powers_blocked_holds

/-- `SophieGermainTheorem`: Fermat's first case, from Sophie Germain's theorem. -/
theorem RNS.SophieGermainTheorem.fermat_first_case_holds :
    RNS.SophieGermainTheorem.fermat_first_case :=
  RNS.SophieGermainTheorem.fermat_first_case_step
    RNS.SophieGermainTheorem.sophie_germain_theorem_holds

#print axioms RNS.SophieGermainTheorem.sophie_germain_theorem_holds
#print axioms RNS.SophieGermainTheorem.fermat_first_case_holds

/-- `SophieGermainPowers` → `GermainAuxiliary` (Sophie Germain wheels are auxiliary). -/
theorem RNS.GermainAuxiliary.sophie_germain_wheel_auxiliary_holds :
    RNS.GermainAuxiliary.sophie_germain_wheel_auxiliary :=
  RNS.GermainAuxiliary.sophie_germain_wheel_auxiliary_step
    RNS.SophieGermainPowers.pth_power_positions_holds

/-- `GermainAuxiliary`: Fermat's first case for 7, from the wheel of size 29. -/
theorem RNS.GermainAuxiliary.fermat_first_case_seven_holds :
    RNS.GermainAuxiliary.fermat_first_case_seven :=
  RNS.GermainAuxiliary.fermat_first_case_seven_step
    RNS.GermainAuxiliary.auxiliary_prime_theorem_holds RNS.GermainAuxiliary.auxiliary_seven_holds

/-- `GermainAuxiliary`: Fermat's first case for 13, from the wheel of size 53. -/
theorem RNS.GermainAuxiliary.fermat_first_case_thirteen_holds :
    RNS.GermainAuxiliary.fermat_first_case_thirteen :=
  RNS.GermainAuxiliary.fermat_first_case_thirteen_step
    RNS.GermainAuxiliary.auxiliary_prime_theorem_holds RNS.GermainAuxiliary.auxiliary_thirteen_holds

#print axioms RNS.GermainAuxiliary.sophie_germain_wheel_auxiliary_holds
#print axioms RNS.GermainAuxiliary.fermat_first_case_seven_holds
#print axioms RNS.GermainAuxiliary.fermat_first_case_thirteen_holds

/-- `SurvivorSymmetry`: the counting form of the mirror, from the position form. -/
theorem RNS.SurvivorSymmetry.survivor_count_reflection_holds :
    RNS.SurvivorSymmetry.survivor_count_reflection :=
  RNS.SurvivorSymmetry.survivor_count_reflection_step
    RNS.SurvivorSymmetry.survivor_reflection_holds

#print axioms RNS.SurvivorSymmetry.survivor_count_reflection_holds

/-- `BonseCeiling` → `Schatunowsky`: 30 is the largest number whose survivors are all prime. -/
theorem RNS.Schatunowsky.schatunowsky_bound_holds : RNS.Schatunowsky.schatunowsky_bound :=
  RNS.Schatunowsky.schatunowsky_bound_step RNS.BonseCeiling.ceiling_inside_cycle_holds

#print axioms RNS.Schatunowsky.schatunowsky_bound_holds

/-- `Sawtooth` → `GermainCriterion`: the two-wheel even split, sufficient direction. -/
theorem RNS.GermainCriterion.two_wheel_split_of_remainders_holds :
    RNS.GermainCriterion.two_wheel_split_of_remainders :=
  RNS.GermainCriterion.two_wheel_split_of_remainders_step
    RNS.Sawtooth.even_split_iff_remainders_cancel_holds

#print axioms RNS.GermainCriterion.two_wheel_split_of_remainders_holds

/-- `HurwitzZetaZero` → `GermainCriterion`: the weighted residue sum of an odd primitive character is not zero. -/
theorem RNS.GermainCriterion.odd_primitive_weighted_sum_ne_zero_holds :
    RNS.GermainCriterion.odd_primitive_weighted_sum_ne_zero :=
  RNS.GermainCriterion.odd_primitive_weighted_sum_ne_zero_step
    RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_holds

/-- `HurwitzZetaZero` → `GermainCriterion`: the weighted residue sum is a value of the L-function at 0. -/
theorem RNS.GermainCriterion.weighted_sum_eq_LFunction_zero_holds :
    RNS.GermainCriterion.weighted_sum_eq_LFunction_zero :=
  RNS.GermainCriterion.weighted_sum_eq_LFunction_zero_step
    RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_holds

/-- `HurwitzZetaZero` → `GermainCriterion`: Germain's (3.2). -/
theorem RNS.GermainCriterion.odd_weighted_sum_ne_zero_iff_holds :
    RNS.GermainCriterion.odd_weighted_sum_ne_zero_iff :=
  RNS.GermainCriterion.odd_weighted_sum_ne_zero_iff_step
    RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_holds

/-- `HurwitzZetaZero` → `GermainCriterion`: Germain's Proposition 3.1. -/
theorem RNS.GermainCriterion.coprime_split_iff_characters_holds :
    RNS.GermainCriterion.coprime_split_iff_characters :=
  RNS.GermainCriterion.coprime_split_iff_characters_step
    RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_holds

/-- `HurwitzZetaZero` → `GermainCriterion`: Germain's Corollary 3.2. -/
theorem RNS.GermainCriterion.all_residues_split_iff_wheels_holds :
    RNS.GermainCriterion.all_residues_split_iff_wheels :=
  RNS.GermainCriterion.all_residues_split_iff_wheels_step
    RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_holds

/-- `Sawtooth` and `HurwitzZetaZero` → `GermainCriterion`: Germain's Theorem 1.1. -/
theorem RNS.GermainCriterion.germain_theorem_holds :
    RNS.GermainCriterion.germain_theorem :=
  RNS.GermainCriterion.germain_theorem_step
    RNS.Sawtooth.even_split_iff_remainders_cancel_holds
    RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_holds

/-- `Sawtooth` and `HurwitzZetaZero` → `GermainCriterion`: Erdős's conjecture on Lehmer's even split. -/
theorem RNS.GermainCriterion.two_wheel_remainders_of_split_holds :
    RNS.GermainCriterion.two_wheel_remainders_of_split :=
  RNS.GermainCriterion.two_wheel_remainders_of_split_step
    RNS.Sawtooth.even_split_iff_remainders_cancel_holds
    RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_holds

/-- `Sawtooth` and `HurwitzZetaZero` → `GermainCriterion`: Germain's Corollary 1.4. -/
theorem RNS.GermainCriterion.two_wheel_split_iff_holds :
    RNS.GermainCriterion.two_wheel_split_iff :=
  RNS.GermainCriterion.two_wheel_split_iff_step
    RNS.Sawtooth.even_split_iff_remainders_cancel_holds
    RNS.HurwitzZetaZero.hurwitz_zeta_at_zero_holds

#print axioms RNS.GermainCriterion.odd_primitive_weighted_sum_ne_zero_holds
#print axioms RNS.GermainCriterion.weighted_sum_eq_LFunction_zero_holds
#print axioms RNS.GermainCriterion.odd_weighted_sum_ne_zero_iff_holds
#print axioms RNS.GermainCriterion.coprime_split_iff_characters_holds
#print axioms RNS.GermainCriterion.all_residues_split_iff_wheels_holds
#print axioms RNS.GermainCriterion.germain_theorem_holds
#print axioms RNS.GermainCriterion.two_wheel_remainders_of_split_holds
#print axioms RNS.GermainCriterion.two_wheel_split_iff_holds

/-- `ShieldCertificates` → `FortunateCeiling`: below the ceiling, a shift that lands on a prime is prime. -/
theorem RNS.FortunateCeiling.shift_prime_below_ceiling_holds :
    RNS.FortunateCeiling.shift_prime_below_ceiling :=
  RNS.FortunateCeiling.shift_prime_below_ceiling_step RNS.ShieldCertificates.window_prime_iff_holds

/-- `ShieldCertificates` → `FortunateCeiling`: a Fortunate number below the ceiling is prime. -/
theorem RNS.FortunateCeiling.fortunate_prime_below_ceiling_holds :
    RNS.FortunateCeiling.fortunate_prime_below_ceiling :=
  RNS.FortunateCeiling.fortunate_prime_below_ceiling_step RNS.ShieldCertificates.window_prime_iff_holds

/-- `ShieldCertificates` → `FortunateCeiling`: Fortune's conjecture from the ceiling. -/
theorem RNS.FortunateCeiling.fortune_of_ceiling_holds : RNS.FortunateCeiling.fortune_of_ceiling :=
  RNS.FortunateCeiling.fortune_of_ceiling_step RNS.ShieldCertificates.window_prime_iff_holds

#print axioms RNS.FortunateCeiling.shift_prime_below_ceiling_holds
#print axioms RNS.FortunateCeiling.fortunate_prime_below_ceiling_holds
#print axioms RNS.FortunateCeiling.fortune_of_ceiling_holds

/-- `BrunPureSieve`, `BrunTwinCount`, `BrunTruncation` → `BrunTwinBound`: Brun's twin bound with
its error terms. -/
theorem RNS.BrunTwinBound.twin_sifted_bound_holds : RNS.BrunTwinBound.twin_sifted_bound :=
  RNS.BrunTwinBound.twin_sifted_bound_step RNS.BrunPureSieve.twin_bonferroni_upper_holds
    RNS.BrunTwinCount.twin_multiples_count_holds RNS.BrunTruncation.truncation_error_holds

#print axioms RNS.BrunTwinBound.twin_sifted_bound_holds

/-- `SurvivorCount`, `ShareBounds` → `BrunAnalytic`: the twin product for the wheels below `L`. -/
theorem RNS.BrunAnalytic.twin_product_bound_holds : RNS.BrunAnalytic.twin_product_bound :=
  RNS.BrunAnalytic.twin_product_bound_step RNS.SurvivorCount.twin_survivor_count_holds
    RNS.ShareBounds.twin_share_le_two_inv_log_sq_holds

/-- `BrunTwinBound`, `BrunTruncation`, `MertensSecond` → `BrunAnalytic`: Brun's bound on the twin
primes, with every arrow inside the network joined. The one remaining hypothesis is the outside claim
`MertensSecond.mertens_second_remainder` (from PNT+). -/
theorem RNS.BrunAnalytic.twin_prime_count_bound_of_mertens_second
    (h : RNS.MertensSecond.mertens_second_remainder) : RNS.BrunAnalytic.twin_prime_count_bound :=
  RNS.BrunAnalytic.twin_prime_count_bound_step RNS.BrunTwinBound.twin_sifted_bound_holds
    RNS.BrunTwinBound.twin_count_le_sifted_holds RNS.BrunTruncation.esymm_power_bound_holds
    RNS.BrunAnalytic.twin_product_bound_holds (RNS.MertensSecond.prime_reciprocal_upper_step h)

#print axioms RNS.BrunAnalytic.twin_product_bound_holds
#print axioms RNS.BrunAnalytic.twin_prime_count_bound_of_mertens_second

/-- `BrunAnalytic` → `BrunTheorem`: Brun's theorem, with every arrow inside the network joined. The
one remaining hypothesis is the outside claim `MertensSecond.mertens_second_remainder` (from PNT+). -/
theorem RNS.BrunTheorem.brun_theorem_of_mertens_second
    (h : RNS.MertensSecond.mertens_second_remainder) : RNS.BrunTheorem.brun_theorem :=
  RNS.BrunTheorem.brun_theorem_step (RNS.BrunAnalytic.twin_prime_count_bound_of_mertens_second h)

#print axioms RNS.BrunTheorem.brun_theorem_of_mertens_second

/-- `BrunTheorem` → `BrunTwinSum`: the cited claim, now proved inside the network from the one outside
claim `MertensSecond.mertens_second_remainder` (from PNT+). -/
theorem RNS.BrunTwinSum.brun_sum_finite_of_mertens_second
    (h : RNS.MertensSecond.mertens_second_remainder) : RNS.BrunTwinSum.brun_sum_finite :=
  RNS.BrunTwinSum.brun_sum_finite_step (RNS.BrunTheorem.brun_theorem_of_mertens_second h)

#print axioms RNS.BrunTwinSum.brun_sum_finite_of_mertens_second

/-- `CRT` → `RandomRotation`: a setting of the wheels is a shift of the cycle. -/
theorem RNS.RandomRotation.rotation_is_shift_holds : RNS.RandomRotation.rotation_is_shift :=
  RNS.RandomRotation.rotation_is_shift_step RNS.CRT.crt_map_bijective_holds

#print axioms RNS.RandomRotation.rotation_is_shift_holds

/-- `SurvivorCount` → `RandomRotation`: the survival chance under random rotations. -/
theorem RNS.RandomRotation.random_rotation_survival_holds :
    RNS.RandomRotation.random_rotation_survival :=
  RNS.RandomRotation.random_rotation_survival_step RNS.SurvivorCount.general_survivor_count_holds

#print axioms RNS.RandomRotation.random_rotation_survival_holds
