import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetContinuousLinearCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportContinuity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D

/-!
# Continuity of throat gauge third-jet coordinate changes

The seven coefficient fields of the actual semidirect third-jet change vary
continuously on every double atlas overlap.  Hence the continuous-linear
third-jet coordinate maps are continuous there.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeContinuity4D

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
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatGaugeCovectorTransitionThirdDerivative4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D

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

private abbrev CovectorEnd :=
  FramedCovector ThroatCoverCoordinates →L[Real]
    FramedCovector ThroatCoverCoordinates

local instance covectorEndNormedAddCommGroup :
    NormedAddCommGroup CovectorEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorEndNormedSpace : NormedSpace Real CovectorEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev CovectorTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] CovectorEnd

local instance covectorTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup CovectorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorTransitionFirstDerivativeNormedSpace :
    NormedSpace Real CovectorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev CovectorTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] CovectorTransitionFirstDerivative

local instance covectorTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup CovectorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorTransitionSecondDerivativeNormedSpace :
    NormedSpace Real CovectorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev BundleIndex :=
  ThroatGaugeSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Frozen third-order semidirect coefficients on a double atlas overlap. -/
def throatGaugeThirdOrderJetBundleChangeOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatGaugeThirdOrderJetBundleOverlap period hPeriod
      first second) :
    FramedThirdOrderJetSemidirectChange ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) :=
  throatGaugeThirdOrderJetSemidirectChangeAt period hPeriod
    (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
      point point.property.1)
    (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod second
      point point.property.2)

private theorem bundleChangeOnOverlap_baseFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseFirst) := by
  change Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseFirst)
  exact
    P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D.bundleChangeOnOverlap_baseFirst_continuous
      period hPeriod first second

private theorem bundleChangeOnOverlap_baseSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseSecond) := by
  change Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseSecond)
  exact
    P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D.bundleChangeOnOverlap_baseSecond_continuous
      period hPeriod first second

private theorem bundleChangeOnOverlap_baseThird_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).baseThird) := by
  have hContinuous : Continuous (fun point :
      ThroatGaugeThirdOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                second.2 first.2)))
          (extChartAt throatCoverModelWithCorners second.2 point)) := by
    apply continuous_iff_continuousAt.mpr
    intro point
    have hEffective : ContinuousAt (fun current :
        EffectiveThroat period hPeriod ↦
          fderiv Real
            (fderiv Real
              (fderiv Real
                (throatGaugeBaseChartTransition period hPeriod
                  second.2 first.2)))
            (extChartAt throatCoverModelWithCorners second.2 current)) point :=
      (throatGaugeBaseChartTransition_thirdFDeriv_contDiffAt_infty
        period hPeriod second.2 first.2 point point.property.2.2
          point.property.1.2).continuousAt.comp
        (continuousAt_extChartAt' point.property.2.2)
    convert hEffective.comp continuousAt_subtype_val using 1
    rfl
  simpa [throatGaugeThirdOrderJetBundleChangeOnOverlap,
    throatGaugeThirdOrderJetSemidirectChangeAt,
    actualThroatConstantFiberThirdOrderJetBaseChangeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt] using hContinuous

private theorem bundleChangeOnOverlap_fiberValue_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberValue) := by
  change Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberValue)
  exact
    P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D.bundleChangeOnOverlap_fiberValue_continuous
      period hPeriod first second

private theorem bundleChangeOnOverlap_fiberFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberFirst) := by
  change Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberFirst)
  exact
    P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D.bundleChangeOnOverlap_fiberFirst_continuous
      period hPeriod first second

private theorem bundleChangeOnOverlap_fiberSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberSecond) := by
  change Continuous (fun point :
      ThroatGaugeSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeSecondOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberSecond)
  exact
    P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D.bundleChangeOnOverlap_fiberSecond_continuous
      period hPeriod first second

private theorem bundleChangeOnOverlap_fiberThird_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatGaugeThirdOrderJetBundleChangeOnOverlap period hPeriod
          first second point).fiberThird) := by
  have hContinuous : Continuous (fun point :
      ThroatGaugeThirdOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatGaugeCovectorTransitionCenteredChart period hPeriod
                first.1 second.1 second.2)))
          (extChartAt throatCoverModelWithCorners second.2 point)) := by
    apply continuous_iff_continuousAt.mpr
    intro point
    have hEffective : ContinuousAt (fun current :
        EffectiveThroat period hPeriod ↦
          fderiv Real
            (fderiv Real
              (fderiv Real
                (throatGaugeCovectorTransitionCenteredChart period hPeriod
                  first.1 second.1 second.2)))
            (extChartAt throatCoverModelWithCorners second.2 current)) point :=
      (throatGaugeCovectorTransitionCenteredChart_thirdFDeriv_contDiffAt_infty
        period hPeriod first.1 second.1 second.2 point
          ⟨point.property.1.1, point.property.2.1⟩
          point.property.2.2).continuousAt.comp
        (continuousAt_extChartAt' point.property.2.2)
    convert hEffective.comp continuousAt_subtype_val using 1
    rfl
  simpa [throatGaugeThirdOrderJetBundleChangeOnOverlap,
    throatGaugeThirdOrderJetSemidirectChangeAt,
    throatGaugeCovectorTargetTransitionThirdDerivativeAt,
    zeroThroatGaugeSecondOrderJetPresentationAt] using hContinuous

/-- The continuous-linear J3 coordinate change is continuous after restriction
to a double atlas overlap. -/
theorem throatGaugeThirdOrderJetBundleContinuousCoordChangeOnOverlap_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatGaugeThirdOrderJetBundleOverlap period hPeriod first second ↦
        throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
          first second point) := by
  have hContinuous :=
    P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportContinuity4D.continuous_semidirectTransport
      (throatGaugeThirdOrderJetBundleChangeOnOverlap period hPeriod
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
  rw [throatGaugeThirdOrderJetBundleContinuousCoordChange_apply]
  rw [throatGaugeThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second point point.property]
  rfl

/-- The totalized J3 coordinate change is continuous on the double overlap
used by the bundle atlas. -/
theorem throatGaugeThirdOrderJetBundleContinuousCoordChange_continuousOn
    (first second : BundleIndex period hPeriod) :
    ContinuousOn
      (throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
        first second)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) := by
  rw [continuousOn_iff_continuous_restrict]
  exact
    throatGaugeThirdOrderJetBundleContinuousCoordChangeOnOverlap_continuous
      period hPeriod first second

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeContinuity4D
end JanusFormal
