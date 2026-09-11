import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeContinuity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D

/-!
# Smoothness of throat metric third-jet coordinate changes

The seven coefficients of the actual metric third-order semidirect change
are `C∞` on every double atlas overlap.  Hence its continuous-linear
coordinate changes are smooth there.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeSmoothness4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdDerivative4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeContinuity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev MetricThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates TensorModel

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

private abbrev TensorEnd := TensorModel →L[Real] TensorModel

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedSpace

local instance tensorEndNormedAddCommGroup : NormedAddCommGroup TensorEnd :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorEndNormedAddCommGroup

local instance tensorEndNormedSpace : NormedSpace Real TensorEnd :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorEndNormedSpace

private abbrev TensorTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] TensorEnd

local instance tensorTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup TensorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorTransitionFirstDerivativeNormedSpace :
    NormedSpace Real TensorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev TensorTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] TensorTransitionFirstDerivative

local instance tensorTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup TensorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorTransitionSecondDerivativeNormedSpace :
    NormedSpace Real TensorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev BundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Identity coefficients used to totalize the third-order change away from
its double overlap. -/
def identityMetricFramedThirdOrderJetSemidirectChange :
    FramedThirdOrderJetSemidirectChange ThroatCoverCoordinates TensorModel where
  toFramedSecondOrderJetSemidirectChange :=
    identityMetricFramedSecondOrderJetSemidirectChange
  baseThird := 0
  baseThird_swap_first_second := by simp
  baseThird_swap_second_third := by simp
  fiberThird := 0
  fiberThird_swap_first_second := by simp
  fiberThird_swap_second_third := by simp

/-- Globally defined coefficient family whose overlap branch is the metric
third-order semidirect change. -/
def throatMetricThirdOrderJetBundleTotalChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    FramedThirdOrderJetSemidirectChange ThroatCoverCoordinates TensorModel := by
  classical
  exact if hCurrent : current ∈ bundleOverlap period hPeriod first second then
      throatMetricThirdOrderJetBundleChangeOnOverlap period hPeriod
        first second ⟨current, hCurrent⟩
    else
      identityMetricFramedThirdOrderJetSemidirectChange

private theorem totalChange_baseFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, BaseTransitionFirstDerivative) ∞
      (fun current ↦
        (throatMetricThirdOrderJetBundleTotalChange period hPeriod
          first second current).baseFirst)
      (bundleOverlap period hPeriod first second) := by
  apply
    (P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D.baseFirst_contMDiffOn
      period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatMetricThirdOrderJetBundleChangeOnOverlap,
    throatMetricThirdOrderJetSemidirectChangeAt,
    throatMetricSecondOrderJetFrameChartAt]

private theorem totalChange_baseSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, BaseTransitionSecondDerivative) ∞
      (fun current ↦
        (throatMetricThirdOrderJetBundleTotalChange period hPeriod
          first second current).baseSecond)
      (bundleOverlap period hPeriod first second) := by
  apply
    (P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D.baseSecond_contMDiffOn
      period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatMetricThirdOrderJetBundleChangeOnOverlap,
    throatMetricThirdOrderJetSemidirectChangeAt,
    throatMetricSecondOrderJetFrameChartAt]

private theorem totalChange_baseThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        BaseTransitionSecondDerivative) ∞
      (fun current ↦
        (throatMetricThirdOrderJetBundleTotalChange period hPeriod
          first second current).baseThird)
      (bundleOverlap period hPeriod first second) := by
  apply
    (throatMetricThirdOrderJet_baseThird_contMDiffOn period hPeriod
      first second).congr
  intro current hCurrent
  have hOverlap : current ∈ bundleOverlap period hPeriod first second := by
    simpa only [bundleOverlap, throatMetricSecondOrderJetBundleOverlap] using
      hCurrent
  rw [throatMetricThirdOrderJetBundleTotalChange, dif_pos hOverlap]
  simp [throatMetricThirdOrderJetBundleChangeOnOverlap,
    throatMetricThirdOrderJetSemidirectChangeAt,
    actualThroatConstantFiberThirdOrderJetBaseChangeAt,
    throatMetricSecondOrderJetFrameChartAt]

private theorem totalChange_fiberValue_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, TensorEnd) ∞
      (fun current ↦
        (throatMetricThirdOrderJetBundleTotalChange period hPeriod
          first second current).fiberValue)
      (bundleOverlap period hPeriod first second) := by
  apply
    (P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D.fiberValue_contMDiffOn
      period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatMetricThirdOrderJetBundleChangeOnOverlap,
    throatMetricThirdOrderJetSemidirectChangeAt,
    throatMetricSecondOrderJetFrameChartAt]

private theorem totalChange_fiberFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, TensorTransitionFirstDerivative) ∞
      (fun current ↦
        (throatMetricThirdOrderJetBundleTotalChange period hPeriod
          first second current).fiberFirst)
      (bundleOverlap period hPeriod first second) := by
  apply
    (P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D.fiberFirst_contMDiffOn
      period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatMetricThirdOrderJetBundleChangeOnOverlap,
    throatMetricThirdOrderJetSemidirectChangeAt,
    throatMetricSecondOrderJetFrameChartAt]

private theorem totalChange_fiberSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, TensorTransitionSecondDerivative) ∞
      (fun current ↦
        (throatMetricThirdOrderJetBundleTotalChange period hPeriod
          first second current).fiberSecond)
      (bundleOverlap period hPeriod first second) := by
  apply
    (P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D.fiberSecond_contMDiffOn
      period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatMetricThirdOrderJetBundleChangeOnOverlap,
    throatMetricThirdOrderJetSemidirectChangeAt,
    throatMetricTargetFrameTransitionSecondDerivativeAt,
    throatMetricSecondOrderJetFrameChartAt]

private theorem totalChange_fiberThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        TensorTransitionSecondDerivative) ∞
      (fun current ↦
        (throatMetricThirdOrderJetBundleTotalChange period hPeriod
          first second current).fiberThird)
      (bundleOverlap period hPeriod first second) := by
  apply
    (throatMetricThirdOrderJet_fiberThird_contMDiffOn period hPeriod
      first second).congr
  intro current hCurrent
  have hOverlap : current ∈ bundleOverlap period hPeriod first second := by
    simpa only [bundleOverlap, throatMetricSecondOrderJetBundleOverlap] using
      hCurrent
  rw [throatMetricThirdOrderJetBundleTotalChange, dif_pos hOverlap]
  simp [throatMetricThirdOrderJetBundleChangeOnOverlap,
    throatMetricThirdOrderJetSemidirectChangeAt,
    throatMetricTargetFrameTransitionThirdDerivativeAt,
    throatMetricSecondOrderJetFrameChartAt]

/-- The totalized metric third-order semidirect transport is smooth on the
double overlap. -/
theorem throatMetricThirdOrderJetBundleTotalTransport_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, MetricThirdJet →L[Real] MetricThirdJet) ∞
      (fun current ↦
        (throatMetricThirdOrderJetBundleTotalChange period hPeriod
          first second current).toContinuousLinearMap)
      (bundleOverlap period hPeriod first second) :=
  P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D.contMDiffOn_semidirectTransport
    (throatMetricThirdOrderJetBundleTotalChange period hPeriod first second)
    (totalChange_baseFirst_contMDiffOn period hPeriod first second)
    (totalChange_baseSecond_contMDiffOn period hPeriod first second)
    (totalChange_baseThird_contMDiffOn period hPeriod first second)
    (totalChange_fiberValue_contMDiffOn period hPeriod first second)
    (totalChange_fiberFirst_contMDiffOn period hPeriod first second)
    (totalChange_fiberSecond_contMDiffOn period hPeriod first second)
    (totalChange_fiberThird_contMDiffOn period hPeriod first second)

/-- Concrete metric third-jet coordinate changes are smooth on every double
overlap. -/
theorem throatMetricThirdOrderJetBundleContinuousCoordChange_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, MetricThirdJet →L[Real] MetricThirdJet) ∞
      (throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
        first second)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) := by
  apply
    (throatMetricThirdOrderJetBundleTotalTransport_contMDiffOn
      period hPeriod first second).congr
  intro current hCurrent
  rw [throatMetricThirdOrderJetBundleTotalChange, dif_pos hCurrent]
  apply ContinuousLinearMap.ext
  intro jet
  rw [throatMetricThirdOrderJetBundleContinuousCoordChange_apply]
  rw [throatMetricThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  rfl

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeSmoothness4D
end JanusFormal
