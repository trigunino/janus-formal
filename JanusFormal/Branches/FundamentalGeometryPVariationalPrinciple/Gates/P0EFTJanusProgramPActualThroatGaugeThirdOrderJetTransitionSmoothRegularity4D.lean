import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

/-!
# Smooth regularity of throat gauge third-jet transition coefficients

The third Frechet derivative fields of the genuine base-chart transition and
the varying contragredient frame transition remain locally `C∞` on every
valid overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D

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
open P0EFTJanusProgramPActualThroatGaugeDifferentiatedOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

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

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The third derivative field of a genuine extended-chart transition is
locally `C∞`. -/
theorem throatGaugeBaseChartTransition_thirdFDeriv_contDiffAt_infty
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ContDiffAt Real ∞
      (fderiv Real
        (fderiv Real
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter))))
      (extChartAt throatCoverModelWithCorners firstCenter current) := by
  exact
    (throatGaugeBaseChartTransition_secondFDeriv_contDiffAt_infty
      period hPeriod firstCenter secondCenter current hFirst hSecond).fderiv_right
        (by simp)

/-- The third derivative field of the varying covector-frame transition is
locally `C∞`. -/
theorem
    throatGaugeCovectorTransitionCenteredChart_thirdFDeriv_contDiffAt_infty
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (fderiv Real
        (fderiv Real
          (fderiv Real
            (throatGaugeCovectorTransitionCenteredChart period hPeriod
              firstAnchor secondAnchor chartAnchor))))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  exact
    (throatGaugeCovectorTransitionCenteredChart_secondFDeriv_contDiffAt_infty
      period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent
        hChart).fderiv_right (by simp)

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D
end JanusFormal
