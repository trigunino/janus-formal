import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D

/-!
# Smooth regularity of throat metric third-jet transition coefficients

The third Frechet derivative fields of the reverse base-chart transition and
the forward covariant rank-two frame transition are locally `C∞` on every
double metric atlas overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetTransitionSmoothRegularity4D

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
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev BundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod

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

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Double overlap of two metric second-jet atlas patches. -/
def throatMetricSecondOrderJetBundleOverlap
    (first second : BundleIndex period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
    throatMetricSecondOrderJetBundleBaseSet period hPeriod second

/-- The third derivative field of the centered covariant rank-two transition
is locally `C∞`. -/
theorem
    throatCovariantTwoTensorTransitionCenteredChart_thirdFDeriv_contDiffAt_infty
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (fderiv Real
        (fderiv Real
          (fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              firstAnchor secondAnchor chartAnchor))))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  exact
    (throatCovariantTwoTensorTransitionCenteredChart_secondFDeriv_contDiffAt_infty
      period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent
        hChart).fderiv_right (by simp)

/-- The reverse base-chart third derivative is `C∞` on every double metric
atlas overlap. -/
theorem throatMetricThirdOrderJet_baseThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        BaseTransitionSecondDerivative) ∞
      (fun current : EffectiveThroat period hPeriod =>
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                second.2 first.2)))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (throatMetricSecondOrderJetBundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatGaugeBaseChartTransition_thirdFDeriv_contDiffAt_infty
      period hPeriod second.2 first.2 current hCurrent.2.2
        hCurrent.1.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

set_option maxHeartbeats 1200000 in
/-- The third derivative of the metric frame transition is `C∞` on every
double metric atlas overlap. -/
theorem throatMetricThirdOrderJet_fiberThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        TensorTransitionSecondDerivative) ∞
      (fun current : EffectiveThroat period hPeriod =>
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
                first.1 second.1 second.2)))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (throatMetricSecondOrderJetBundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatCovariantTwoTensorTransitionCenteredChart_thirdFDeriv_contDiffAt_infty
      period hPeriod first.1 second.1 second.2 current
        ⟨hCurrent.1.1, hCurrent.2.1⟩ hCurrent.2.2).contMDiffAt.comp
          current (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetTransitionSmoothRegularity4D
end JanusFormal
