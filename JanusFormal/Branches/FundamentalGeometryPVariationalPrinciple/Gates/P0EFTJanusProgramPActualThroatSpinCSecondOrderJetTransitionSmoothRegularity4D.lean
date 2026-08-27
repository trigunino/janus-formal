import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

/-!
# Smooth coefficients for actual throat SpinC second-jet transitions

The reverse base-chart derivatives and the forward SpinC transition and its
first two derivatives are `C∞` on every double SpinC second-jet atlas overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D

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
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

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

/-- Double overlap of two SpinC second-jet atlas patches. -/
def throatSpinCSecondOrderJetBundleOverlap
    (first second : BundleIndex period hPeriod) :
    Set (ThroatBase period hPeriod) :=
  throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
    throatSpinCSecondOrderJetBundleBaseSet period hPeriod second

/-! ## Local SpinC transition regularity -/

/-- The centered SpinC fiber transition is `C∞` at every valid overlap
point in the selected extended chart. -/
theorem d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty_of_mem_source
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        first second chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty period hPeriod
    choice first second chartAnchor current hCurrent hChart

/-- The first derivative field of the centered SpinC transition is locally
`C∞`. -/
theorem d9PrimitiveSpinCTransitionCenteredChart_fderiv_contDiffAt_infty
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
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          first second chartAnchor))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  exact
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod choice first second chartAnchor current hCurrent
        hChart).fderiv_right (by simp)

/-- The second derivative field of the centered SpinC transition is locally
`C∞`. -/
theorem d9PrimitiveSpinCTransitionCenteredChart_secondFDeriv_contDiffAt_infty
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
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            first second chartAnchor)))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  exact
    (d9PrimitiveSpinCTransitionCenteredChart_fderiv_contDiffAt_infty
      period hPeriod choice first second chartAnchor current hCurrent
        hChart).fderiv_right (by simp)

/-! ## Five semidirect coefficient families on atlas overlaps -/

/-- The reverse base-chart Jacobian coefficient is `C∞` on each double
atlas overlap. -/
theorem throatSpinCSecondOrderJet_baseFirst_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current : ThroatBase period hPeriod =>
        fderiv Real
          (throatGaugeBaseChartTransition period hPeriod second.2 first.2)
          (extChartAt throatCoverModelWithCorners second.2 current))
      (throatSpinCSecondOrderJetBundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈ (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatGaugeBaseChartTransition_fderiv_contDiffAt_infty period hPeriod
      second.2 first.2 current hCurrent.2.2 hCurrent.1.2).contMDiffAt.comp
        current (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

/-- The reverse base-chart Hessian coefficient is `C∞` on each double
atlas overlap. -/
theorem throatSpinCSecondOrderJet_baseSecond_contMDiffOn
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current : ThroatBase period hPeriod =>
        fderiv Real
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod second.2 first.2))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (throatSpinCSecondOrderJetBundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈ (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((throatGaugeBaseChartTransition_secondFDeriv_contDiffAt_infty
      period hPeriod second.2 first.2 current hCurrent.2.2
        hCurrent.1.2).contMDiffAt.comp current
          (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

/-- The SpinC fiber-value transition coefficient is `C∞` on each double
atlas overlap. -/
theorem throatSpinCSecondOrderJet_fiberValue_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, SpinCEnd) ∞
      (fun current : ThroatBase period hPeriod =>
        d9PrimitiveSpinCCoordChange period hPeriod choice first.1 second.1
          current)
      (throatSpinCSecondOrderJetBundleOverlap period hPeriod first second) :=
  ((d9PrimitiveSpinCVectorBundleCore period hPeriod choice)
    |>.contMDiffOn_coordChange throatCoverModelWithCorners first.1 second.1).mono
      (by
        intro current hCurrent
        exact ⟨hCurrent.1.1, hCurrent.2.1⟩)

/-- The first derivative of the SpinC fiber transition is `C∞` on each
double atlas overlap. -/
theorem throatSpinCSecondOrderJet_fiberFirst_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCTransitionFirstDerivative) ∞
      (fun current : ThroatBase period hPeriod =>
        fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            first.1 second.1 second.2)
          (extChartAt throatCoverModelWithCorners second.2 current))
      (throatSpinCSecondOrderJetBundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈ (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((d9PrimitiveSpinCTransitionCenteredChart_fderiv_contDiffAt_infty
      period hPeriod choice first.1 second.1 second.2 current
        ⟨hCurrent.1.1, hCurrent.2.1⟩ hCurrent.2.2).contMDiffAt.comp
          current (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

/-- The second derivative of the SpinC fiber transition is `C∞` on each
double atlas overlap. -/
theorem throatSpinCSecondOrderJet_fiberSecond_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        SpinCTransitionFirstDerivative) ∞
      (fun current : ThroatBase period hPeriod =>
        fderiv Real
          (fderiv Real
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              first.1 second.1 second.2))
          (extChartAt throatCoverModelWithCorners second.2 current))
      (throatSpinCSecondOrderJetBundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈ (chartAt ThroatCoverModel second.2).source := by
    simpa only [extChartAt_source] using hCurrent.2.2
  exact
    ((d9PrimitiveSpinCTransitionCenteredChart_secondFDeriv_contDiffAt_infty
      period hPeriod choice first.1 second.1 second.2 current
        ⟨hCurrent.1.1, hCurrent.2.1⟩ hCurrent.2.2).contMDiffAt.comp
          current (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D
end JanusFormal
