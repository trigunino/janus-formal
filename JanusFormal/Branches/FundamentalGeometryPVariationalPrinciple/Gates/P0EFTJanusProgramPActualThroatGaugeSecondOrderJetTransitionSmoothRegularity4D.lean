import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeFrameTransitionInBaseChartSecondOrderJetOverlap4D

/-!
# Smooth regularity of throat gauge second-jet transition coefficients

The genuine base-chart transition and varying contragredient frame transition
are `C∞` at every valid overlap point.  Their first and second Fréchet
derivative fields are locally `C∞` as well.  These are coefficient regularity
statements for a later smooth second-jet transition action; no jet-bundle or
quotient smoothness is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
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
open P0EFTJanusProgramPActualThroatGaugeFrameTransitionInBaseChartSecondOrderJetOverlap4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

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

/-! ## Base-chart coefficients -/

/-- A genuine extended-chart transition is `C∞` at every point represented
by both charts. -/
theorem throatGaugeBaseChartTransition_contDiffAt_infty
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ContDiffAt Real ∞
      (throatGaugeBaseChartTransition period hPeriod
        firstCenter secondCenter)
      (extChartAt throatCoverModelWithCorners firstCenter current) := by
  change ContDiffAt Real ∞
    ((extChartAt throatCoverModelWithCorners secondCenter) ∘
      (extChartAt throatCoverModelWithCorners firstCenter).symm)
    (extChartAt throatCoverModelWithCorners firstCenter current)
  have hFirstTarget :
      extChartAt throatCoverModelWithCorners firstCenter current ∈
        (extChartAt throatCoverModelWithCorners firstCenter).target :=
    (extChartAt throatCoverModelWithCorners firstCenter).map_source hFirst
  have hFirstInverse :
      ContMDiffAt
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
        (extChartAt throatCoverModelWithCorners firstCenter).symm
        (extChartAt throatCoverModelWithCorners firstCenter current) :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) firstCenter).contMDiffAt
        (extChartAt_target_mem_nhds' hFirstTarget)
  have hSecondChart :
      ContMDiffAt throatCoverModelWithCorners
        (modelWithCornersSelf Real ThroatCoverCoordinates) ∞
        (extChartAt throatCoverModelWithCorners secondCenter) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hSecond
  have hTransition :
      ContMDiffAt
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        (modelWithCornersSelf Real ThroatCoverCoordinates) ∞
        ((extChartAt throatCoverModelWithCorners secondCenter) ∘
          (extChartAt throatCoverModelWithCorners firstCenter).symm)
        (extChartAt throatCoverModelWithCorners firstCenter current) :=
    hSecondChart.comp_of_eq hFirstInverse
      ((extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst)
  exact hTransition.contDiffAt

/-- The chart-transition Jacobian field is locally `C∞`. -/
theorem throatGaugeBaseChartTransition_fderiv_contDiffAt_infty
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ContDiffAt Real ∞
      (fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter))
      (extChartAt throatCoverModelWithCorners firstCenter current) := by
  exact
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).fderiv_right (by simp)

/-- The chart-transition Hessian field is locally `C∞`. -/
theorem throatGaugeBaseChartTransition_secondFDeriv_contDiffAt_infty
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ContDiffAt Real ∞
      (fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter)))
      (extChartAt throatCoverModelWithCorners firstCenter current) := by
  exact
    (throatGaugeBaseChartTransition_fderiv_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).fderiv_right (by simp)

/-! ## Frame-transition coefficients -/

/-- The varying contragredient frame transition is `C∞` in every valid
extended base chart. -/
theorem throatGaugeCovectorTransitionCenteredChart_contDiffAt_infty_of_mem_source
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  let firstTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor
  let secondTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondAnchor
  let chartCoordinate :=
    extChartAt throatCoverModelWithCorners chartAnchor current
  change ContDiffAt Real ∞
    (fun coordinate =>
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor
        ((extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate) :
          FramedCovector ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates)) chartCoordinate
  have hOverlapOpen : IsOpen
      (throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor) :=
    firstTrivialization.open_baseSet.inter secondTrivialization.open_baseSet
  have hOverlapNhds :
      throatGaugeCenteredTrivializationOverlap period hPeriod
          firstAnchor secondAnchor ∈ 𝓝 current :=
    hOverlapOpen.mem_nhds hCurrent
  have hChartTarget : chartCoordinate ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).target :=
    (extChartAt throatCoverModelWithCorners chartAnchor).map_source hChart
  have hChartInverse :
      ContMDiffAt (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
        (extChartAt throatCoverModelWithCorners chartAnchor).symm
        chartCoordinate :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) chartAnchor).contMDiffAt
        (extChartAt_target_mem_nhds' hChartTarget)
  have hTransitionAt :
      ContMDiffAt throatCoverModelWithCorners
        (modelWithCornersSelf Real
          (FramedCovector ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates)) ∞
        (fun point : EffectiveThroat period hPeriod =>
          (throatGaugeCovectorTrivializationTransitionAt period hPeriod
            firstAnchor secondAnchor point :
              FramedCovector ThroatCoverCoordinates →L[Real]
                FramedCovector ThroatCoverCoordinates)) current :=
    (throatGaugeCovectorTrivializationTransitionAt_contMDiffOn
      period hPeriod firstAnchor secondAnchor).contMDiffAt hOverlapNhds
  have hComposed := hTransitionAt.comp_of_eq hChartInverse
    ((extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart)
  exact hComposed.contDiffAt

/-- The first derivative of the varying frame-transition field is locally
`C∞`. -/
theorem throatGaugeCovectorTransitionCenteredChart_fderiv_contDiffAt_infty
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor chartAnchor))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  exact
    (throatGaugeCovectorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent
        hChart).fderiv_right (by simp)

/-- The second derivative of the varying frame-transition field is locally
`C∞`. -/
theorem throatGaugeCovectorTransitionCenteredChart_secondFDeriv_contDiffAt_infty
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
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor chartAnchor)))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  exact
    (throatGaugeCovectorTransitionCenteredChart_fderiv_contDiffAt_infty
      period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent
        hChart).fderiv_right (by simp)

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
end JanusFormal
