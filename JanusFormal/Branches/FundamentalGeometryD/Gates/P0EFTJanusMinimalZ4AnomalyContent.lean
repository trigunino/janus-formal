import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusPeriodicQuarterCompetition

namespace JanusFormal
namespace P0EFTJanusMinimalZ4AnomalyContent

set_option autoImplicit false

open P0EFTJanusPeriodicQuarterCompetition

/-- Doubled effective Chern--Simons level on the positive fold. -/
def positiveFoldDoubledLevel
    (bareLevel fermionMultiplicity : ℤ) : ℤ :=
  2 * bareLevel + fermionMultiplicity

/-- PT-related negative fold: opposite bare level and opposite anomaly shift. -/
def negativeFoldDoubledLevel
    (bareLevel fermionMultiplicity : ℤ) : ℤ :=
  -2 * bareLevel - fermionMultiplicity

/-- PT-related fold levels cancel identically. -/
theorem pt_fold_doubled_levels_cancel
    (bareLevel fermionMultiplicity : ℤ) :
    positiveFoldDoubledLevel bareLevel fermionMultiplicity +
      negativeFoldDoubledLevel bareLevel fermionMultiplicity = 0 := by
  unfold positiveFoldDoubledLevel negativeFoldDoubledLevel
  ring

/-- An odd fermion multiplicity cannot give zero effective level on one fold. -/
theorem odd_multiplicity_obstructs_single_fold_zero_level
    (bareLevel fermionMultiplicity : ℤ)
    (hOdd : fermionMultiplicity % 2 = 1) :
    positiveFoldDoubledLevel bareLevel fermionMultiplicity ≠ 0 := by
  intro hZero
  unfold positiveFoldDoubledLevel at hZero
  omega

/-- Five quarter-holonomy modes with bare level `-2` give the minimal positive half-level. -/
@[simp] theorem five_mode_positive_fold_level :
    positiveFoldDoubledLevel (-2) 5 = 1 := by
  norm_num [positiveFoldDoubledLevel]

/-- The PT-related fold carries the opposite minimal half-level. -/
@[simp] theorem five_mode_negative_fold_level :
    negativeFoldDoubledLevel (-2) 5 = -1 := by
  norm_num [negativeFoldDoubledLevel]

/-- The two minimal half-level anomalies cancel globally. -/
theorem five_mode_pt_pair_is_globally_level_zero :
    positiveFoldDoubledLevel (-2) 5 +
      negativeFoldDoubledLevel (-2) 5 = 0 := by
  norm_num

/-- Doubling both determinant weights preserves the stationary polynomial up to scale. -/
theorem doubled_weights_scale_stationarity_polynomial
    (periodicWeight quarterWeight radial : ℝ) :
    stationarityPolynomial
      (2 * periodicWeight) (2 * quarterWeight) radial =
      2 * stationarityPolynomial periodicWeight quarterWeight radial := by
  unfold stationarityPolynomial
  ring

/-- The per-fold `1:5` content and total PT-paired `2:10` content have the same roots. -/
theorem one_five_and_two_ten_stationarity_equivalent
    (radial : ℝ) :
    stationarityPolynomial 2 10 radial = 0 ↔
      stationarityPolynomial 1 5 radial = 0 := by
  rw [show (2 : ℝ) = 2 * 1 by norm_num,
    show (10 : ℝ) = 2 * 5 by norm_num,
    doubled_weights_scale_stationarity_polynomial]
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    norm_num

/-- No quarter multiplicity `0,1,2,3,4` stabilizes one periodic unit. -/
theorem below_five_modes_cannot_stabilize
    (quarterMultiplicity : ℕ)
    (hBelow : quarterMultiplicity < 5)
    (radial : ℝ) :
    stationarityPolynomial 1 (quarterMultiplicity : ℝ) radial ≠ 0 := by
  exact one_periodic_at_most_four_quarter_has_no_stationary
    quarterMultiplicity (by omega) radial

/-- Five modes are the first positive integer content admitting stationary roots. -/
theorem five_is_first_stabilizing_quarter_multiplicity :
    (∀ quarterMultiplicity : ℕ,
      quarterMultiplicity < 5 →
        ∀ radial : ℝ,
          stationarityPolynomial 1
            (quarterMultiplicity : ℝ) radial ≠ 0) /\
    stationarityPolynomial 1 5 (1 / 3) = 0 := by
  constructor
  · intro quarterMultiplicity hBelow radial
    exact below_five_modes_cannot_stabilize
      quarterMultiplicity hBelow radial
  · exact third_is_one_to_five_stationary

/-- Five is odd, so the minimal stabilizing content is necessarily parity anomalous per fold. -/
@[simp] theorem five_mode_content_is_odd :
    (5 : ℤ) % 2 = 1 := by
  norm_num

/--
The same discrete number five is therefore selected twice in the toy model:

1. it is the least quarter-sector multiplicity able to compete with one
   periodic determinant unit;
2. it is odd, so each fold carries a nonzero half-integral parity anomaly,
   while the PT pair cancels globally.

This is a sharp arithmetic candidate, not yet a derivation of five geometric
fermion species or five independent determinant towers.
-/
structure MinimalFiveModePhysicalStatus where
  onePeriodicUnitDerived : Prop
  fiveQuarterModesDerivedFromGeometry : Prop
  commonMassApproximationControlled : Prop
  determinantSignsDerived : Prop
  stableOneThirdRootDerived : Prop
  bareLevelsMinusTwoAndPlusTwoDerived : Prop
  foldParityAnomaliesComputed : Prop
  globalPTAnomalyCancellationProved : Prop
  noExtraLightModesProved : Prop


def minimalFiveModePhysicalClosure
    (s : MinimalFiveModePhysicalStatus) : Prop :=
  s.onePeriodicUnitDerived /\
  s.fiveQuarterModesDerivedFromGeometry /\
  s.commonMassApproximationControlled /\
  s.determinantSignsDerived /\
  s.stableOneThirdRootDerived /\
  s.bareLevelsMinusTwoAndPlusTwoDerived /\
  s.foldParityAnomaliesComputed /\
  s.globalPTAnomalyCancellationProved /\
  s.noExtraLightModesProved

end P0EFTJanusMinimalZ4AnomalyContent
end JanusFormal
