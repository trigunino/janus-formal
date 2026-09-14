import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeContinuity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D

/-!
# Smoothness of throat SpinC third-jet coordinate changes

The seven coefficients of the actual SpinC third-order semidirect change
are `C∞` on every double atlas overlap.  Hence its continuous-linear
coordinate changes are smooth there.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeSmoothness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatSpinCTransitionThirdDerivative4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeContinuity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)
variable (choice : NormalRootChoice)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCModel := D9DoubledMatterFiber

private abbrev SpinCThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates SpinCModel

private abbrev BaseTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates

local instance baseTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup BaseTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance baseTransitionFirstDerivativeNormedSpace :
    NormedSpace Real BaseTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev BaseTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] BaseTransitionFirstDerivative

local instance baseTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup BaseTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance baseTransitionSecondDerivativeNormedSpace :
    NormedSpace Real BaseTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev SpinCEnd := SpinCModel →L[Real] SpinCModel

local instance spinCEndNormedAddCommGroup : NormedAddCommGroup SpinCEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCEndNormedSpace : NormedSpace Real SpinCEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev SpinCTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCEnd

local instance spinCTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCTransitionFirstDerivativeNormedSpace :
    NormedSpace Real SpinCTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev SpinCTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCTransitionFirstDerivative

local instance spinCTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCTransitionSecondDerivativeNormedSpace :
    NormedSpace Real SpinCTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

private abbrev bundleOverlap
    (first second : BundleIndex period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
    throatSpinCSecondOrderJetBundleBaseSet period hPeriod second

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Identity coefficients used to totalize the third-order change away from
its double overlap. -/
def identitySpinCFramedThirdOrderJetSemidirectChange :
    FramedThirdOrderJetSemidirectChange
      ThroatCoverCoordinates SpinCModel where
  toFramedSecondOrderJetSemidirectChange :=
    identitySpinCFramedSecondOrderJetSemidirectChange
  baseThird := 0
  baseThird_swap_first_second := by simp
  baseThird_swap_second_third := by simp
  fiberThird := 0
  fiberThird_swap_first_second := by simp
  fiberThird_swap_second_third := by simp

/-- Globally defined coefficient family whose overlap branch is the SpinC
third-order semidirect change. -/
def throatSpinCThirdOrderJetBundleTotalChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    FramedThirdOrderJetSemidirectChange
      ThroatCoverCoordinates SpinCModel := by
  classical
  exact if hCurrent : current ∈ bundleOverlap period hPeriod first second then
      throatSpinCThirdOrderJetBundleChangeOnOverlap period hPeriod choice
        first second ⟨current, hCurrent⟩
    else
      identitySpinCFramedThirdOrderJetSemidirectChange

private theorem totalChange_baseFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, BaseTransitionFirstDerivative) ∞
      (fun current ↦
        (throatSpinCThirdOrderJetBundleTotalChange period hPeriod choice
          first second current).baseFirst)
      (bundleOverlap period hPeriod first second) := by
  apply
    (P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D.throatSpinCSecondOrderJetBundleTotalChange_baseFirst_contMDiffOn
      period hPeriod choice first second).congr
  intro current hCurrent
  rw [throatSpinCThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatSpinCThirdOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCThirdOrderJetSemidirectChangeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

private theorem totalChange_baseSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, BaseTransitionSecondDerivative) ∞
      (fun current ↦
        (throatSpinCThirdOrderJetBundleTotalChange period hPeriod choice
          first second current).baseSecond)
      (bundleOverlap period hPeriod first second) := by
  apply
    (P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D.throatSpinCSecondOrderJetBundleTotalChange_baseSecond_contMDiffOn
      period hPeriod choice first second).congr
  intro current hCurrent
  rw [throatSpinCThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatSpinCThirdOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCThirdOrderJetSemidirectChangeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

private theorem totalChange_baseThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        BaseTransitionSecondDerivative) ∞
      (fun current ↦
        (throatSpinCThirdOrderJetBundleTotalChange period hPeriod choice
          first second current).baseThird)
      (bundleOverlap period hPeriod first second) := by
  apply
    (throatSpinCThirdOrderJet_baseThird_contMDiffOn period hPeriod
      first second).congr
  intro current hCurrent
  have hOverlap : current ∈ bundleOverlap period hPeriod first second := by
    simpa only [bundleOverlap, throatSpinCSecondOrderJetBundleOverlap] using
      hCurrent
  rw [throatSpinCThirdOrderJetBundleTotalChange, dif_pos hOverlap]
  simp [throatSpinCThirdOrderJetBundleChangeOnOverlap,
    throatSpinCThirdOrderJetSemidirectChangeAt,
    actualThroatConstantFiberThirdOrderJetBaseChangeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

private theorem totalChange_fiberValue_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, SpinCEnd) ∞
      (fun current ↦
        (throatSpinCThirdOrderJetBundleTotalChange period hPeriod choice
          first second current).fiberValue)
      (bundleOverlap period hPeriod first second) := by
  apply
    (P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D.throatSpinCSecondOrderJetBundleTotalChange_fiberValue_contMDiffOn
      period hPeriod choice first second).congr
  intro current hCurrent
  rw [throatSpinCThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatSpinCThirdOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCThirdOrderJetSemidirectChangeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

private theorem totalChange_fiberFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCTransitionFirstDerivative) ∞
      (fun current ↦
        (throatSpinCThirdOrderJetBundleTotalChange period hPeriod choice
          first second current).fiberFirst)
      (bundleOverlap period hPeriod first second) := by
  apply
    (P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D.throatSpinCSecondOrderJetBundleTotalChange_fiberFirst_contMDiffOn
      period hPeriod choice first second).congr
  intro current hCurrent
  rw [throatSpinCThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatSpinCThirdOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCThirdOrderJetSemidirectChangeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

private theorem totalChange_fiberSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCTransitionSecondDerivative) ∞
      (fun current ↦
        (throatSpinCThirdOrderJetBundleTotalChange period hPeriod choice
          first second current).fiberSecond)
      (bundleOverlap period hPeriod first second) := by
  apply
    (P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D.throatSpinCSecondOrderJetBundleTotalChange_fiberSecond_contMDiffOn
      period hPeriod choice first second).congr
  intro current hCurrent
  rw [throatSpinCThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatSpinCThirdOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCThirdOrderJetSemidirectChangeAt,
    throatSpinCTargetTrivializationTransitionSecondDerivativeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

private theorem totalChange_fiberThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        SpinCTransitionSecondDerivative) ∞
      (fun current ↦
        (throatSpinCThirdOrderJetBundleTotalChange period hPeriod choice
          first second current).fiberThird)
      (bundleOverlap period hPeriod first second) := by
  apply
    (throatSpinCThirdOrderJet_fiberThird_contMDiffOn period hPeriod
      choice first second).congr
  intro current hCurrent
  have hOverlap : current ∈ bundleOverlap period hPeriod first second := by
    simpa only [bundleOverlap, throatSpinCSecondOrderJetBundleOverlap] using
      hCurrent
  rw [throatSpinCThirdOrderJetBundleTotalChange, dif_pos hOverlap]
  simp [throatSpinCThirdOrderJetBundleChangeOnOverlap,
    throatSpinCThirdOrderJetSemidirectChangeAt,
    throatSpinCTargetTrivializationTransitionThirdDerivativeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

/-- The totalized SpinC third-order semidirect transport is smooth on the
double overlap. -/
theorem throatSpinCThirdOrderJetBundleTotalTransport_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCThirdJet →L[Real] SpinCThirdJet) ∞
      (fun current ↦
        (throatSpinCThirdOrderJetBundleTotalChange period hPeriod choice
          first second current).toContinuousLinearMap)
      (bundleOverlap period hPeriod first second) :=
  P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D.contMDiffOn_semidirectTransport
    (throatSpinCThirdOrderJetBundleTotalChange period hPeriod choice first second)
    (totalChange_baseFirst_contMDiffOn period hPeriod choice first second)
    (totalChange_baseSecond_contMDiffOn period hPeriod choice first second)
    (totalChange_baseThird_contMDiffOn period hPeriod choice first second)
    (totalChange_fiberValue_contMDiffOn period hPeriod choice first second)
    (totalChange_fiberFirst_contMDiffOn period hPeriod choice first second)
    (totalChange_fiberSecond_contMDiffOn period hPeriod choice first second)
    (totalChange_fiberThird_contMDiffOn period hPeriod choice first second)

/-- Concrete SpinC third-jet coordinate changes are smooth on every double
overlap. -/
theorem throatSpinCThirdOrderJetBundleContinuousCoordChange_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCThirdJet →L[Real] SpinCThirdJet) ∞
      (throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
        first second)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) := by
  apply
    (throatSpinCThirdOrderJetBundleTotalTransport_contMDiffOn
      period hPeriod choice first second).congr
  intro current hCurrent
  rw [throatSpinCThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  apply ContinuousLinearMap.ext
  intro jet
  rw [throatSpinCThirdOrderJetBundleContinuousCoordChange_apply]
  rw [throatSpinCThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod choice first second current hCurrent]
  rfl

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeSmoothness4D
end JanusFormal
