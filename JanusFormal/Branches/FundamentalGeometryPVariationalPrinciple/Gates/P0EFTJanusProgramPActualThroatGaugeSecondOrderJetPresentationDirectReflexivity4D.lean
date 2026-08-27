import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

/-!
# Reflexivity of direct throat gauge second-jet compatibility

The identity laws for frame and base-chart changes show that every arbitrary
local second-jet presentation is directly compatible with itself.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectReflexivity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeCombinedFrameBaseChartSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Direct compatibility is reflexive already, before taking its generated
equivalence closure. -/
theorem directTransitionCompatible_refl
    {current : EffectiveThroat period hPeriod}
    (presentation :
      ThroatGaugeSecondOrderJetPresentationAt period hPeriod current) :
    DirectTransitionCompatible period hPeriod presentation presentation := by
  have hFrameValue :
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          presentation.frameAnchor presentation.frameAnchor current :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates) =
        ContinuousLinearMap.id Real
          (FramedCovector ThroatCoverCoordinates) := by
    simpa only [throatGaugeCovectorTransitionCenteredChart,
      (extChartAt throatCoverModelWithCorners presentation.chartAnchor).left_inv
        presentation.chart_mem] using
      throatGaugeCovectorTransitionCenteredChart_self period hPeriod
        presentation.frameAnchor presentation.chartAnchor current
          presentation.frame_mem presentation.chart_mem
  have hBaseFirst :
      fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            presentation.chartAnchor presentation.chartAnchor)
          (extChartAt throatCoverModelWithCorners presentation.chartAnchor
            current) =
        ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
        period hPeriod presentation.chartAnchor current presentation.chart_mem
  have hBaseSecond :
      fderiv Real
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              presentation.chartAnchor presentation.chartAnchor))
          (extChartAt throatCoverModelWithCorners presentation.chartAnchor
            current) = 0 := by
    simpa only [
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
        period hPeriod presentation.chartAnchor current presentation.chart_mem
  have hFrameValue_apply
      (covector : FramedCovector ThroatCoverCoordinates) :
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
          presentation.frameAnchor presentation.frameAnchor current covector =
        covector := by
    change
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          presentation.frameAnchor presentation.frameAnchor current :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates) covector = covector
    rw [hFrameValue]
    simp
  constructor
  · exact (hFrameValue_apply presentation.jet.value).symm
  · rw [hBaseFirst, hFrameValue,
      throatGaugeCovectorTransitionCenteredChart_self_firstDerivative
        period hPeriod presentation.frameAnchor presentation.chartAnchor
          current presentation.frame_mem presentation.chart_mem]
    simp
  · intro firstDirection secondDirection
    rw [hBaseFirst, hBaseSecond, hFrameValue_apply,
      throatGaugeCovectorTransitionCenteredChart_self_firstDerivative
        period hPeriod presentation.frameAnchor presentation.chartAnchor
          current presentation.frame_mem presentation.chart_mem,
      throatGaugeCovectorTransitionCenteredChart_self_secondDerivative
        period hPeriod presentation.frameAnchor presentation.chartAnchor
          current presentation.frame_mem presentation.chart_mem secondDirection]
    simp

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectReflexivity4D
end JanusFormal
