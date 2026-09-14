import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetContinuousLinearCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportContinuity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetTransitionSmoothRegularity4D

/-!
# Continuity of throat SpinC third-jet coordinate changes

The seven coefficient fields of the actual semidirect third-jet change vary
continuously on every double SpinC atlas overlap.  Hence the
continuous-linear third-jet coordinate maps are continuous there.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeContinuity4D

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
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatSpinCTransitionThirdDerivative4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetTransitionSmoothRegularity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)
variable (choice : NormalRootChoice)

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

private abbrev SpinCEnd :=
  D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber

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

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Frozen third-order semidirect coefficients on a double SpinC atlas
overlap. -/
def throatSpinCThirdOrderJetBundleChangeOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatSpinCThirdOrderJetBundleOverlap period hPeriod
      first second) :
    FramedThirdOrderJetSemidirectChange
      ThroatCoverCoordinates D9DoubledMatterFiber :=
  throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod first point
      point.property.1)
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod second point
      point.property.2)

private theorem bundleChangeOnOverlap_baseFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCThirdOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).baseFirst) := by
  change Continuous (fun point :
      ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).baseFirst)
  have hContinuous :=
    (throatSpinCSecondOrderJet_baseFirst_contMDiffOn
      period hPeriod first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
    ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
      fderiv Real
        (P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D.throatGaugeBaseChartTransition
          period hPeriod second.2 first.2)
        (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectChangeAt_baseFirst,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor] using
      hContinuous

private theorem bundleChangeOnOverlap_baseSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCThirdOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).baseSecond) := by
  change Continuous (fun point :
      ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).baseSecond)
  have hContinuous :=
    (throatSpinCSecondOrderJet_baseSecond_contMDiffOn
      period hPeriod first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
    ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
      fderiv Real
        (fderiv Real
          (P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D.throatGaugeBaseChartTransition
            period hPeriod second.2 first.2))
        (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectChangeAt_baseSecond,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor] using
      hContinuous

private theorem bundleChangeOnOverlap_baseThird_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCThirdOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).baseThird) := by
  have hContinuous :=
    (throatSpinCThirdOrderJet_baseThird_contMDiffOn period hPeriod
      first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
      ThroatSpinCThirdOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D.throatGaugeBaseChartTransition
                period hPeriod second.2 first.2)))
          (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatSpinCThirdOrderJetBundleChangeOnOverlap,
    throatSpinCThirdOrderJetSemidirectChangeAt,
    actualThroatConstantFiberThirdOrderJetBaseChangeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt] using hContinuous

private theorem bundleChangeOnOverlap_fiberValue_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCThirdOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).fiberValue) := by
  change Continuous (fun point :
      ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).fiberValue)
  have hContinuous :=
    (throatSpinCSecondOrderJet_fiberValue_contMDiffOn
      period hPeriod choice first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
    ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
      d9PrimitiveSpinCCoordChange period hPeriod choice first.1 second.1
        point) at hContinuous
  simpa only [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_trivializationIndex]
      using hContinuous

private theorem bundleChangeOnOverlap_fiberFirst_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCThirdOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).fiberFirst) := by
  change Continuous (fun point :
      ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).fiberFirst)
  have hContinuous :=
    (throatSpinCSecondOrderJet_fiberFirst_contMDiffOn
      period hPeriod choice first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
    ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
      fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          first.1 second.1 second.2)
        (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberFirst,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_trivializationIndex,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor] using
      hContinuous

private theorem bundleChangeOnOverlap_fiberSecond_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCThirdOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).fiberSecond) := by
  change Continuous (fun point :
      ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).fiberSecond)
  have hContinuous : ContinuousOn
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              first.1 second.1 second.2))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (throatSpinCSecondOrderJetBundleOverlap period hPeriod first second) :=
    (throatSpinCSecondOrderJet_fiberSecond_contMDiffOn
      period hPeriod choice first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
    ThroatSpinCSecondOrderJetBundleOverlap period hPeriod first second ↦
      fderiv Real
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            first.1 second.1 second.2))
        (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberSecond,
    throatSpinCTargetTrivializationTransitionSecondDerivativeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_trivializationIndex,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor] using
      hContinuous

private theorem bundleChangeOnOverlap_fiberThird_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCThirdOrderJetBundleOverlap period hPeriod first second ↦
        (throatSpinCThirdOrderJetBundleChangeOnOverlap period hPeriod choice
          first second point).fiberThird) := by
  have hContinuous :=
    (throatSpinCThirdOrderJet_fiberThird_contMDiffOn period hPeriod
      choice first second).continuousOn
  rw [continuousOn_iff_continuous_restrict] at hContinuous
  change Continuous (fun point :
      ThroatSpinCThirdOrderJetBundleOverlap period hPeriod first second ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
                first.1 second.1 second.2)))
          (extChartAt throatCoverModelWithCorners second.2 point)) at hContinuous
  simpa only [throatSpinCThirdOrderJetBundleChangeOnOverlap,
    throatSpinCThirdOrderJetSemidirectChangeAt,
    throatSpinCTargetTrivializationTransitionThirdDerivativeAt,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt] using hContinuous

/-- The continuous-linear SpinC J3 coordinate change is continuous after
restriction to a double atlas overlap. -/
theorem throatSpinCThirdOrderJetBundleContinuousCoordChangeOnOverlap_continuous
    (first second : BundleIndex period hPeriod) :
    Continuous (fun point :
      ThroatSpinCThirdOrderJetBundleOverlap period hPeriod first second ↦
        throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
          first second point) := by
  have hContinuous :=
    P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportContinuity4D.continuous_semidirectTransport
      (throatSpinCThirdOrderJetBundleChangeOnOverlap period hPeriod choice
        first second)
      (bundleChangeOnOverlap_baseFirst_continuous period hPeriod choice first second)
      (bundleChangeOnOverlap_baseSecond_continuous period hPeriod choice first second)
      (bundleChangeOnOverlap_baseThird_continuous period hPeriod choice first second)
      (bundleChangeOnOverlap_fiberValue_continuous period hPeriod choice first second)
      (bundleChangeOnOverlap_fiberFirst_continuous period hPeriod choice first second)
      (bundleChangeOnOverlap_fiberSecond_continuous period hPeriod choice first second)
      (bundleChangeOnOverlap_fiberThird_continuous period hPeriod choice first second)
  convert hContinuous using 1
  funext point
  apply ContinuousLinearMap.ext
  intro jet
  rw [throatSpinCThirdOrderJetBundleContinuousCoordChange_apply]
  rw [throatSpinCThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod choice first second point point.property]
  rfl

/-- The totalized SpinC J3 coordinate change is continuous on the double
overlap used by the bundle atlas. -/
theorem throatSpinCThirdOrderJetBundleContinuousCoordChange_continuousOn
    (first second : BundleIndex period hPeriod) :
    ContinuousOn
      (throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
        first second)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) := by
  rw [continuousOn_iff_continuous_restrict]
  exact
    throatSpinCThirdOrderJetBundleContinuousCoordChangeOnOverlap_continuous
      period hPeriod choice first second

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeContinuity4D
end JanusFormal
