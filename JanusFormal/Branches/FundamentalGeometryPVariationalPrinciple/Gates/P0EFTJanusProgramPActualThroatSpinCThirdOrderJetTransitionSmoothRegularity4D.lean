import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D

/-!
# Smooth regularity of throat SpinC third-jet transition coefficients

The third Frechet derivative fields of the reverse base-chart transition and
the forward SpinC fiber transition are locally `C∞` on every double atlas
overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetTransitionSmoothRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

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

local instance spinCEndNormedAddCommGroup :
    NormedAddCommGroup SpinCEnd :=
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

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance primitiveSpinCCoreIsContMDiff (choice : NormalRootChoice) :
    (d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).IsContMDiff throatCoverModelWithCorners ∞ :=
  d9PrimitiveSpinCVectorBundleCore_isContMDiff period hPeriod choice

/-- The third derivative field of the centered SpinC transition is locally
`C∞`. -/
theorem d9PrimitiveSpinCTransitionCenteredChart_thirdFDeriv_contDiffAt_infty
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (fderiv Real
        (fderiv Real
          (fderiv Real
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              first second chartAnchor))))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  exact
    (d9PrimitiveSpinCTransitionCenteredChart_secondFDeriv_contDiffAt_infty
      period hPeriod choice first second chartAnchor current hCurrent
        hChart).fderiv_right (by simp)

/-- The reverse base-chart third derivative is `C∞` on every double SpinC
atlas overlap. -/
theorem throatSpinCThirdOrderJet_baseThird_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        BaseTransitionSecondDerivative) ∞
      (fun current : ThroatBase period hPeriod =>
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                second.2 first.2)))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (throatSpinCSecondOrderJetBundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatGaugeBaseChartTransition_thirdFDeriv_contDiffAt_infty
      period hPeriod second.2 first.2 current hCurrent.2.2
        hCurrent.1.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

/-- The third derivative of the SpinC fiber transition is `C∞` on every
double atlas overlap. -/
theorem throatSpinCThirdOrderJet_fiberThird_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        SpinCTransitionSecondDerivative) ∞
      (fun current : ThroatBase period hPeriod =>
        fderiv Real
          (fderiv Real
            (fderiv Real
              (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
                first.1 second.1 second.2)))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (throatSpinCSecondOrderJetBundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈
      (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((d9PrimitiveSpinCTransitionCenteredChart_thirdFDeriv_contDiffAt_infty
      period hPeriod choice first.1 second.1 second.2 current
        ⟨hCurrent.1.1, hCurrent.2.1⟩ hCurrent.2.2).contMDiffAt.comp
          current (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetTransitionSmoothRegularity4D
end JanusFormal
