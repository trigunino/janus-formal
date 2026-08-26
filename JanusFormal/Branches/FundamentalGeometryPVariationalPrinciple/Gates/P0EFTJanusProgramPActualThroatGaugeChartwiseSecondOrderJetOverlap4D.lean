import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderJetOverlap4D

/-!
# Chartwise second-order overlap law for the actual throat gauge jet

The exact frame-overlap germ and a generic second-order Leibniz identity give
the four-term transformation law for the `secondDerivative` field of the
actual local gauge jet carrier.

The result is evaluated in two directions in one fixed extended base chart.
It does not assert chart-independent jet descent, a gauge transformation,
normal geometry or a global connection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeChartwiseSecondOrderJetOverlap4D

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

/-! ## Regularity and the exact fixed-chart germ -/

/-- The contragredient frame transition is `C²` in the extended chart centered
at every point of the double overlap. -/
theorem throatGaugeCovectorTransitionCenteredChart_contDiffAt_two
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor) :
    ContDiffAt Real 2
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor current)
      (extChartAt throatCoverModelWithCorners current current) := by
  change ContDiffAt Real 2
    (fun coordinate =>
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor
        ((extChartAt throatCoverModelWithCorners current).symm coordinate) :
          FramedCovector ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates))
    (extChartAt throatCoverModelWithCorners current current)
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
  have hTransition : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real
        (FramedCovector ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates)) 2
      (fun point : EffectiveThroat period hPeriod =>
        (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor point :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates)) current := by
    apply
      ((throatGaugeCovectorTrivializationTransitionAt_contMDiffOn
        period hPeriod firstAnchor secondAnchor).contMDiffAt
          (hOverlapOpen.mem_nhds hCurrent)).of_le
    show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hSource := (contMDiffAt_iff_source).mp hTransition
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext coordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  exact hSource.contDiffAt

/-- In the chart centered at `current`, the transitioned first representative
and the second representative agree as germs, not merely at the center. -/
theorem throatGaugeCovectorCenteredChart_transition_eventuallyEq
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor) :
    (fun coordinate =>
      throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor current coordinate
        (throatGaugeCovectorCenteredChart period hPeriod potential component
          firstAnchor current coordinate)) =ᶠ[𝓝
            (extChartAt throatCoverModelWithCorners current current)]
      throatGaugeCovectorCenteredChart period hPeriod potential component
        secondAnchor current := by
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
  have hChartInverse :
      ContMDiffAt (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
        (extChartAt throatCoverModelWithCorners current).symm
        (extChartAt throatCoverModelWithCorners current current) :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) current).contMDiffAt
      (extChartAt_target_mem_nhds current)
  have hInverseEventually :
      (extChartAt throatCoverModelWithCorners current).symm ⁻¹'
          throatGaugeCenteredTrivializationOverlap period hPeriod
            firstAnchor secondAnchor ∈
        𝓝 (extChartAt throatCoverModelWithCorners current current) := by
    apply hChartInverse.continuousAt.preimage_mem_nhds
    simpa only [extChartAt_to_inv] using hOverlapNhds
  filter_upwards [hInverseEventually] with coordinate hCoordinate
  simpa only [throatGaugeCovectorTransitionCenteredChart,
    throatGaugeCovectorCenteredChart,
    throatGaugeCovectorCoordinatesTransported,
    throatGaugeCovectorTrivializationTransitionAt,
    ContinuousLinearEquiv.coe_coe] using
    (throatGaugeCovectorCoordinatesTransported_eq period hPeriod potential
      component firstAnchor secondAnchor
      ((extChartAt throatCoverModelWithCorners current).symm coordinate)
      hCoordinate)

/-! ## Four-term second-order law in the actual jet carrier -/

/-- The second-derivative slots obey the exact four-term Leibniz law in the
fixed chart: transported second derivative, two mixed terms, and the second
derivative of the varying transition acting on the first value. -/
theorem throatGaugeCovectorSecondOrderJetInFrameAt_secondDerivative_transition_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (first second : ThroatCoverCoordinates) :
    (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
      component secondAnchor current hCurrent.2).secondDerivative first second =
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current)
        ((throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).secondDerivative
            first second) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor current)
          (extChartAt throatCoverModelWithCorners current current) first
        ((throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).firstDerivative second) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor current)
          (extChartAt throatCoverModelWithCorners current current) second
        ((throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).firstDerivative first) +
      fderiv Real
          (fun coordinate =>
            fderiv Real
              (throatGaugeCovectorTransitionCenteredChart period hPeriod
                firstAnchor secondAnchor current) coordinate second)
          (extChartAt throatCoverModelWithCorners current current) first
        ((throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).value) := by
  let transition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor current
  let firstRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      firstAnchor current
  let secondRepresentative :=
    throatGaugeCovectorCenteredChart period hPeriod potential component
      secondAnchor current
  let centerCoordinate :=
    extChartAt throatCoverModelWithCorners current current
  have hTransitionC2 : ContDiffAt Real 2 transition centerCoordinate :=
    throatGaugeCovectorTransitionCenteredChart_contDiffAt_two period hPeriod
      firstAnchor secondAnchor current hCurrent
  have hFirstC2 : ContDiffAt Real 2 firstRepresentative centerCoordinate :=
    throatGaugeCovectorCenteredChart_contDiffAt_two period hPeriod potential
      component firstAnchor current hCurrent.1
  have hGerm :
      (fun coordinate => transition coordinate
        (firstRepresentative coordinate)) =ᶠ[𝓝 centerCoordinate]
        secondRepresentative :=
    throatGaugeCovectorCenteredChart_transition_eventuallyEq period hPeriod
      potential component firstAnchor secondAnchor current hCurrent
  have hSecondDerivativeEq :
      fderiv Real (fderiv Real
          (fun coordinate => transition coordinate
            (firstRepresentative coordinate))) centerCoordinate =
        fderiv Real (fderiv Real secondRepresentative) centerCoordinate :=
    (hGerm.fderiv).fderiv_eq
  have hLeibniz := second_fderiv_clm_apply_apply transition
    firstRepresentative centerCoordinate first second hTransitionC2 hFirstC2
  rw [throatGaugeCovectorSecondOrderJetInFrameAt_secondDerivative,
    show fderiv Real (fderiv Real secondRepresentative) centerCoordinate
        first second =
      fderiv Real (fderiv Real
        (fun coordinate => transition coordinate
          (firstRepresentative coordinate))) centerCoordinate first second by
      exact congrArg
        (fun derivative : ThroatCoverCoordinates →L[Real]
            ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates =>
          derivative first second) hSecondDerivativeEq.symm]
  simpa only [transition, firstRepresentative, centerCoordinate,
    throatGaugeCovectorTransitionCenteredChart,
    throatGaugeCovectorCenteredChart, extChartAt_to_inv,
    throatGaugeCovectorSecondOrderJetInFrameAt_value,
    throatGaugeCovectorSecondOrderJetInFrameAt_firstDerivative,
    throatGaugeCovectorSecondOrderJetInFrameAt_secondDerivative,
    ContinuousLinearEquiv.coe_coe] using hLeibniz

end
end P0EFTJanusProgramPActualThroatGaugeChartwiseSecondOrderJetOverlap4D
end JanusFormal
