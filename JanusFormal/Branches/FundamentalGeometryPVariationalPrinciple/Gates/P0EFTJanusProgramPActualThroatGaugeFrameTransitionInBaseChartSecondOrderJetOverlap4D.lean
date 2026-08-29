import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeCombinedFrameBaseChartSecondOrderJetOverlap4D

/-!
# Frame overlap law in an arbitrary throat base chart

The varying tangent-frame transition and both gauge representatives are read
in any extended base chart whose source contains the evaluation point.  Their
exact germ gives the first- and second-order Leibniz laws directly in the
three-parameter jet carrier.

No global descent or arbitrary-pair cocycle is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeFrameTransitionInBaseChartSecondOrderJetOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeDifferentiatedOverlap4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D

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

/-! ## Arbitrary-chart regularity and germ -/

/-- The varying contragredient frame transition is `C²` in any extended base
chart containing the common point. -/
theorem throatGaugeCovectorTransitionCenteredChart_contDiffAt_two_of_mem_source
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real 2
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
  change ContDiffAt Real 2
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
  exact hComposed.contDiffAt.of_le (by
    show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top)

/-- In an arbitrary common base chart, the transported first-frame
representative and the second-frame representative agree as germs. -/
theorem throatGaugeCovectorCenteredChart_frameTransition_eventuallyEq_of_mem_source
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (fun coordinate =>
      throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor chartAnchor coordinate
        (throatGaugeCovectorCenteredChart period hPeriod potential component
          firstAnchor chartAnchor coordinate)) =ᶠ[𝓝
            (extChartAt throatCoverModelWithCorners chartAnchor current)]
      throatGaugeCovectorCenteredChart period hPeriod potential component
        secondAnchor chartAnchor := by
  let firstTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor
  let secondTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondAnchor
  have hOverlapOpen : IsOpen
      (throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor) :=
    firstTrivialization.open_baseSet.inter secondTrivialization.open_baseSet
  have hOverlapNhds :
      throatGaugeCenteredTrivializationOverlap period hPeriod
          firstAnchor secondAnchor ∈ 𝓝 current :=
    hOverlapOpen.mem_nhds hCurrent
  have hChartInverse : ContinuousAt
      (extChartAt throatCoverModelWithCorners chartAnchor).symm
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    continuousAt_extChartAt_symm' hChart
  have hInverseEventually :
      (extChartAt throatCoverModelWithCorners chartAnchor).symm ⁻¹'
          throatGaugeCenteredTrivializationOverlap period hPeriod
            firstAnchor secondAnchor ∈
        𝓝 (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    hChartInverse.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart]
      exact hOverlapNhds)
  filter_upwards [hInverseEventually] with coordinate hCoordinate
  simpa only [throatGaugeCovectorTransitionCenteredChart,
    throatGaugeCovectorCenteredChart,
    throatGaugeCovectorCoordinatesTransported,
    throatGaugeCovectorTrivializationTransitionAt,
    ContinuousLinearEquiv.coe_coe] using
    (throatGaugeCovectorCoordinatesTransported_eq period hPeriod potential
      component firstAnchor secondAnchor
        ((extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate)
        hCoordinate)

/-! ## Frame laws in the three-parameter carrier -/

/-- First-order varying-frame Leibniz law in an arbitrary base chart. -/
theorem throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative_frame_transition
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component secondAnchor chartAnchor current hCurrent.2 hChart).firstDerivative =
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates).comp
        (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor chartAnchor current hCurrent.1 hChart).firstDerivative +
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current)).flip
          (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
            component firstAnchor chartAnchor current hCurrent.1 hChart).value := by
  let transition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor chartAnchor
  let firstRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      firstAnchor chartAnchor
  let secondRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      secondAnchor chartAnchor
  let coordinate :=
    extChartAt throatCoverModelWithCorners chartAnchor current
  have hTransition : ContDiffAt Real 2 transition coordinate := by
    simpa only [transition, coordinate] using
      throatGaugeCovectorTransitionCenteredChart_contDiffAt_two_of_mem_source
        period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent hChart
  have hFirst : ContDiffAt Real 2 firstRepresentative coordinate := by
    simpa only [firstRepresentative, coordinate] using
      throatGaugeCovectorCenteredChart_contDiffAt_two_of_mem_source period hPeriod
        potential component firstAnchor chartAnchor current hCurrent.1 hChart
  have hGerm :
      (fun point => transition point (firstRepresentative point)) =ᶠ[𝓝 coordinate]
        secondRepresentative := by
    simpa only [transition, firstRepresentative, secondRepresentative,
      coordinate] using
      throatGaugeCovectorCenteredChart_frameTransition_eventuallyEq_of_mem_source
        period hPeriod potential component firstAnchor secondAnchor chartAnchor
          current hCurrent hChart
  have hProduct := fderiv_clm_apply
    (hTransition.differentiableAt (by norm_num))
    (hFirst.differentiableAt (by norm_num))
  rw [throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative,
    throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative,
    throatGaugeCovectorSecondOrderJetInBaseChartAt_value]
  rw [show fderiv Real secondRepresentative coordinate =
      fderiv Real (fun point => transition point (firstRepresentative point))
        coordinate by exact hGerm.fderiv_eq.symm]
  simpa only [transition, firstRepresentative, coordinate,
    throatGaugeCovectorTransitionCenteredChart,
    throatGaugeCovectorCenteredChart,
    (extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart,
    ContinuousLinearEquiv.coe_coe] using hProduct

/-- Full four-term second-order varying-frame law in an arbitrary base chart. -/
theorem throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative_frame_transition_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source)
    (first second : ThroatCoverCoordinates) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component secondAnchor chartAnchor current hCurrent.2 hChart).secondDerivative
        first second =
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current
        ((throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor chartAnchor current hCurrent.1 hChart).secondDerivative
            first second) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor chartAnchor)
          (extChartAt throatCoverModelWithCorners chartAnchor current) first
        ((throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor chartAnchor current hCurrent.1 hChart).firstDerivative
            second) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor chartAnchor)
          (extChartAt throatCoverModelWithCorners chartAnchor current) second
        ((throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor chartAnchor current hCurrent.1 hChart).firstDerivative
            first) +
      fderiv Real
          (fun coordinate =>
            fderiv Real
              (throatGaugeCovectorTransitionCenteredChart period hPeriod
                firstAnchor secondAnchor chartAnchor) coordinate second)
          (extChartAt throatCoverModelWithCorners chartAnchor current) first
        ((throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor chartAnchor current hCurrent.1 hChart).value) := by
  let transition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor chartAnchor
  let firstRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      firstAnchor chartAnchor
  let secondRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      secondAnchor chartAnchor
  let coordinate :=
    extChartAt throatCoverModelWithCorners chartAnchor current
  have hTransition : ContDiffAt Real 2 transition coordinate := by
    simpa only [transition, coordinate] using
      throatGaugeCovectorTransitionCenteredChart_contDiffAt_two_of_mem_source
        period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent hChart
  have hFirst : ContDiffAt Real 2 firstRepresentative coordinate := by
    simpa only [firstRepresentative, coordinate] using
      throatGaugeCovectorCenteredChart_contDiffAt_two_of_mem_source period hPeriod
        potential component firstAnchor chartAnchor current hCurrent.1 hChart
  have hGerm :
      (fun point => transition point (firstRepresentative point)) =ᶠ[𝓝 coordinate]
        secondRepresentative := by
    simpa only [transition, firstRepresentative, secondRepresentative,
      coordinate] using
      throatGaugeCovectorCenteredChart_frameTransition_eventuallyEq_of_mem_source
        period hPeriod potential component firstAnchor secondAnchor chartAnchor
          current hCurrent hChart
  have hSecondDerivative :
      fderiv Real (fderiv Real
          (fun point => transition point (firstRepresentative point))) coordinate =
        fderiv Real (fderiv Real secondRepresentative) coordinate :=
    (hGerm.fderiv).fderiv_eq
  have hLeibniz := second_fderiv_clm_apply_apply transition
    firstRepresentative coordinate first second hTransition hFirst
  rw [throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative,
    throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative,
    throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative,
    throatGaugeCovectorSecondOrderJetInBaseChartAt_value]
  rw [show fderiv Real (fderiv Real secondRepresentative) coordinate
      first second =
    fderiv Real (fderiv Real
      (fun point => transition point (firstRepresentative point))) coordinate
        first second by
    exact congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates =>
        derivative first second) hSecondDerivative.symm]
  simpa only [transition, firstRepresentative, coordinate,
    throatGaugeCovectorTransitionCenteredChart,
    throatGaugeCovectorCenteredChart,
    (extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart,
    ContinuousLinearEquiv.coe_coe] using hLeibniz

end
end P0EFTJanusProgramPActualThroatGaugeFrameTransitionInBaseChartSecondOrderJetOverlap4D
end JanusFormal
