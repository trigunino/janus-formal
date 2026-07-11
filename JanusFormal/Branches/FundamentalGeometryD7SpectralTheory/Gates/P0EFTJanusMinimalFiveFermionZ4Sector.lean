import Mathlib
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusZ4StatisticsSelection
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusMinimalZ4AnomalyContent

namespace JanusFormal
namespace P0EFTJanusMinimalFiveFermionZ4Sector

set_option autoImplicit false

open P0EFTJanusZ4StatisticsSelection
open P0EFTJanusMinimalZ4AnomalyContent
open P0EFTJanusPeriodicQuarterCompetition

/-- Five identical fermionic quarter-holonomy towers. -/
def fiveFermionStatistics (_index : Fin 5) : FieldStatistics :=
  FieldStatistics.fermion

/-- Every member of the five-mode sector obeys `g^2=(-1)^F`. -/
theorem five_fermion_quarter_sector_is_statistics_compatible :
    ∀ index : Fin 5,
      PinZ4Compatible (fiveFermionStatistics index) quarterPhase := by
  intro index
  exact quarter_phase_is_fermionic

/-- The one-to-five determinant candidate has its stable radial root at `1/3`. -/
@[simp] theorem minimal_five_fermion_stationary_root :
    stationarityPolynomial 1 5 (1 / 3) = 0 := by
  exact third_is_one_to_five_stationary

/-- Four or fewer quarter fermions cannot compete with one periodic determinant unit. -/
theorem fewer_than_five_fermions_cannot_stabilize
    (multiplicity : ℕ)
    (hBelow : multiplicity < 5)
    (radial : ℝ) :
    stationarityPolynomial 1 (multiplicity : ℝ) radial ≠ 0 := by
  exact below_five_modes_cannot_stabilize multiplicity hBelow radial

/-- Five fermions with bare level `-2` leave the minimal positive half-level on one fold. -/
@[simp] theorem five_fermion_positive_fold_doubled_level :
    positiveFoldDoubledLevel (-2) 5 = 1 := by
  exact five_mode_positive_fold_level

/-- The PT-related fold carries the opposite half-level. -/
@[simp] theorem five_fermion_negative_fold_doubled_level :
    negativeFoldDoubledLevel (-2) 5 = -1 := by
  exact five_mode_negative_fold_level

/-- The full PT pair is anomaly-level neutral. -/
theorem five_fermion_pt_pair_level_cancels :
    positiveFoldDoubledLevel (-2) 5 +
      negativeFoldDoubledLevel (-2) 5 = 0 := by
  exact five_mode_pt_pair_is_globally_level_zero

/--
The minimal candidate simultaneously satisfies statistics, stabilization and
global PT anomaly cancellation.
-/
theorem minimal_five_fermion_candidate_matrix :
    (∀ index : Fin 5,
      PinZ4Compatible (fiveFermionStatistics index) quarterPhase) /\
    stationarityPolynomial 1 5 (1 / 3) = 0 /\
    positiveFoldDoubledLevel (-2) 5 = 1 /\
    negativeFoldDoubledLevel (-2) 5 = -1 /\
    positiveFoldDoubledLevel (-2) 5 +
      negativeFoldDoubledLevel (-2) 5 = 0 := by
  exact ⟨five_fermion_quarter_sector_is_statistics_compatible,
    minimal_five_fermion_stationary_root,
    five_fermion_positive_fold_doubled_level,
    five_fermion_negative_fold_doubled_level,
    five_fermion_pt_pair_level_cancels⟩

/-- Two PT folds double the per-fold determinant weights from `1:5` to `2:10`. -/
theorem pt_doubled_five_fermion_polynomial
    (radial : ℝ) :
    stationarityPolynomial 2 10 radial =
      2 * stationarityPolynomial 1 5 radial := by
  exact doubled_weights_scale_stationarity_polynomial 1 5 radial

/-- The stable root survives the PT doubling. -/
@[simp] theorem pt_doubled_five_fermion_stationary_root :
    stationarityPolynomial 2 10 (1 / 3) = 0 := by
  rw [pt_doubled_five_fermion_polynomial,
    minimal_five_fermion_stationary_root]
  norm_num

/--
This is the first statistics-consistent realization of the arithmetic ratio
`1:5`.  The missing theorem is geometric: derive exactly five light fermionic
quarter-holonomy towers, their common mass and determinant signs, rather than
borrowing the number five from bosonic massive-spin-two polarizations.
-/
structure MinimalFiveFermionPhysicalStatus where
  fiveFermionBundlesDerivedFromGeometry : Prop
  quarterHolonomyDerivedFromPinLift : Prop
  commonGeneratedMassDerived : Prop
  onePeriodicBosonicUnitDerived : Prop
  determinantStatisticsSignsDerived : Prop
  gaugeGhostContributionsIncluded : Prop
  bareFoldLevelsDerived : Prop
  fullPTAnomalyCancellationProved : Prop
  higherModesControlled : Prop
  stableOneThirdRootDerived : Prop
  finiteCountertermsFixedMicroscopically : Prop


def minimalFiveFermionPhysicalClosure
    (s : MinimalFiveFermionPhysicalStatus) : Prop :=
  s.fiveFermionBundlesDerivedFromGeometry /\
  s.quarterHolonomyDerivedFromPinLift /\
  s.commonGeneratedMassDerived /\
  s.onePeriodicBosonicUnitDerived /\
  s.determinantStatisticsSignsDerived /\
  s.gaugeGhostContributionsIncluded /\
  s.bareFoldLevelsDerived /\
  s.fullPTAnomalyCancellationProved /\
  s.higherModesControlled /\
  s.stableOneThirdRootDerived /\
  s.finiteCountertermsFixedMicroscopically

end P0EFTJanusMinimalFiveFermionZ4Sector
end JanusFormal
