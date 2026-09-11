import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetContinuousLinearCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportContinuity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetTransitionSmoothRegularity4D

/-!
# Continuity of throat metric third-jet coordinate changes

The seven coefficient fields of the actual semidirect third-jet change vary
continuously on every double metric atlas overlap.  Hence the
continuous-linear third-jet coordinate maps are continuous there.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeContinuity4D

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
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdDerivative4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetTransitionSmoothRegularity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedSpace

private abbrev TensorEnd := TensorModel →L[Real] TensorModel

local instance tensorEndNormedAddCommGroup : NormedAddCommGroup TensorEnd :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorEndNormedAddCommGroup

local instance tensorEndNormedSpace : NormedSpace Real TensorEnd :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorEndNormedSpace

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

/-- Frozen third-order semidirect coefficients on a double metric atlas
overlap. -/
def throatMetricThirdOrderJetBundleChangeOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatMetricThirdOrderJetBundleOverlap period hPeriod
      first second) :
    FramedThirdOrderJetSemidirectChange ThroatCoverCoordinates TensorModel :=
  throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
    (throatMetricSecondOrderJetFrameChartAt period hPeriod first point
      point.property.1)
    (throatMetricSecondOrderJetFrameChartAt period hPeriod second point
      point.property.2)

private theorem bundleChangeOnOverlap_baseFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseFirst) := by
  change Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseFirst)
  exact
    P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D.bundleChangeOnOverlap_baseFirst_continuous
      period hPeriod first second

private theorem bundleChangeOnOverlap_baseSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseSecond) := by
  change Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseSecond)
  exact
    P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D.bundleChangeOnOverlap_baseSecond_continuous
      period hPeriod first second

private theorem bundleChangeOnOverlap_baseThird_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseThird) := by
  have hContinuous :=
    (throatMetricThirdOrderJet_baseThird_contMDiffOn period hPeriod
      first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
      ThroatMetricThirdOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D.throatGaugeBaseChartTransition
                period hPeriod second.2 first.2)))
          (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatMetricThirdOrderJetBundleChangeOnOverlap,
    throatMetricThirdOrderJetSemidirectChangeAt,
    actualThroatConstantFiberThirdOrderJetBaseChangeAt,
    throatMetricSecondOrderJetFrameChartAt] using hContinuous

private theorem bundleChangeOnOverlap_fiberValue_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberValue) := by
  change Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberValue)
  exact
    P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D.bundleChangeOnOverlap_fiberValue_continuous
      period hPeriod first second

private theorem bundleChangeOnOverlap_fiberFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberFirst) := by
  change Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberFirst)
  exact
    P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D.bundleChangeOnOverlap_fiberFirst_continuous
      period hPeriod first second

private theorem bundleChangeOnOverlap_fiberSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberSecond) := by
  change Continuous (fun point :
      ThroatMetricSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberSecond)
  exact
    P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D.bundleChangeOnOverlap_fiberSecond_continuous
      period hPeriod first second

private theorem bundleChangeOnOverlap_fiberThird_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatMetricThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberThird) := by
  have hContinuous :=
    (throatMetricThirdOrderJet_fiberThird_contMDiffOn period hPeriod
      first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
      ThroatMetricThirdOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
                first.1 second.1 second.2)))
          (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatMetricThirdOrderJetBundleChangeOnOverlap,
    throatMetricThirdOrderJetSemidirectChangeAt,
    throatMetricTargetFrameTransitionThirdDerivativeAt,
    throatMetricSecondOrderJetFrameChartAt] using hContinuous

/-- The continuous-linear metric J3 coordinate change is continuous after
restriction to a double atlas overlap. -/
theorem throatMetricThirdOrderJetBundleContinuousCoordChangeOnOverlap_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatMetricThirdOrderJetBundleOverlap period hPeriod first second ↦
        throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
          first second point) := by
  have hContinuous :=
    P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportContinuity4D.continuous_semidirectTransport
      (throatMetricThirdOrderJetBundleChangeOnOverlap period hPeriod
        first second)
      (bundleChangeOnOverlap_baseFirst_continuous period hPeriod first second)
      (bundleChangeOnOverlap_baseSecond_continuous period hPeriod first second)
      (bundleChangeOnOverlap_baseThird_continuous period hPeriod first second)
      (bundleChangeOnOverlap_fiberValue_continuous period hPeriod first second)
      (bundleChangeOnOverlap_fiberFirst_continuous period hPeriod first second)
      (bundleChangeOnOverlap_fiberSecond_continuous period hPeriod first second)
      (bundleChangeOnOverlap_fiberThird_continuous period hPeriod first second)
  convert hContinuous using 1
  funext point
  apply ContinuousLinearMap.ext
  intro jet
  rw [throatMetricThirdOrderJetBundleContinuousCoordChange_apply]
  rw [throatMetricThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second point point.property]
  rfl

/-- The totalized metric J3 coordinate change is continuous on the double
overlap used by the bundle atlas. -/
theorem throatMetricThirdOrderJetBundleContinuousCoordChange_continuousOn
    (first second : BundleIndex period hPeriod) :
    ContinuousOn
      (throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
        first second)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) := by
  rw [continuousOn_iff_continuous_restrict]
  exact
    throatMetricThirdOrderJetBundleContinuousCoordChangeOnOverlap_continuous
      period hPeriod first second

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeContinuity4D
end JanusFormal
