import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeChartwiseSecondOrderJetOverlap4D

/-!
# Combined frame and base-chart overlap law for the throat gauge jet

Starting in the extended chart centered at the common point, this gate combines
the varying tangent-frame transition with a subsequent genuine change of base
chart.  The resulting value, first derivative and second derivative laws are
exact consequences of the two separately compiled overlap gates.

This is centered-source local descent data.  It is not yet the arbitrary
two-chart/two-frame cocycle or a global jet-bundle section.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeCombinedFrameBaseChartSecondOrderJetOverlap4D

set_option autoImplicit false

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
open P0EFTJanusProgramPActualThroatGaugeDifferentiatedOverlap4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D

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

/-! ## The combined representative germ -/

/-- After changing the tangent frame in the centered source chart, the result
is locally the target-frame representative in `secondCenter` composed with the
genuine base-chart transition. -/
theorem throatGaugeCovectorCenteredChart_combinedFrameBaseChartTransition_eventuallyEq
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (fun coordinate =>
      throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor current coordinate
        (throatGaugeCovectorCenteredChart period hPeriod potential component
          firstAnchor current coordinate)) =ᶠ[𝓝
            (extChartAt throatCoverModelWithCorners current current)]
      (throatGaugeCovectorCenteredChart period hPeriod potential component
          secondAnchor secondCenter) ∘
        throatGaugeBaseChartTransition period hPeriod current secondCenter := by
  exact
    (throatGaugeCovectorCenteredChart_transition_eventuallyEq period hPeriod
      potential component firstAnchor secondAnchor current hCurrent).trans
    (throatGaugeCovectorCenteredChart_baseChartTransition_eventuallyEq
      period hPeriod potential component secondAnchor current secondCenter
        current (mem_extChartAt_source current) hSecond)

/-! ## Combined laws in the actual jet fields -/

/-- The target value in the second chart is the exact contragredient transport
of the source-frame value. -/
theorem throatGaugeCovectorSecondOrderJet_combinedFrameBaseChart_value
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component secondAnchor secondCenter current hCurrent.2 hSecond).value =
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current
        (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).value := by
  rw [throatGaugeCovectorSecondOrderJetInBaseChartAt_value,
    throatGaugeCovectorSecondOrderJetInFrameAt_value]
  exact (throatGaugeCovectorCoordinatesTransported_eq period hPeriod potential
    component firstAnchor secondAnchor current hCurrent).symm

/-- Combined first-order law.  Pulling the target derivative back through the
base-chart Jacobian gives the full varying-frame Leibniz law. -/
theorem throatGaugeCovectorSecondOrderJet_combinedFrameBaseChart_firstDerivative_transition
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component secondAnchor secondCenter current hCurrent.2 hSecond).firstDerivative.comp
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod current secondCenter)
          (extChartAt throatCoverModelWithCorners current current)) =
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates).comp
        (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).firstDerivative +
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor current)
        (extChartAt throatCoverModelWithCorners current current)).flip
          (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
            component firstAnchor current hCurrent.1).value := by
  have hBase :=
    throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative_transition
      period hPeriod potential component secondAnchor current secondCenter
        current hCurrent.2 (mem_extChartAt_source current) hSecond
  have hBase' :
      (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
        component secondAnchor current hCurrent.2).firstDerivative =
        (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component secondAnchor secondCenter current hCurrent.2 hSecond).firstDerivative.comp
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod current secondCenter)
              (extChartAt throatCoverModelWithCorners current current)) := by
    simpa only [
      throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative_diagonal]
      using hBase
  exact hBase'.symm.trans
    (throatGaugeCovectorSecondOrderJetInFrameAt_firstDerivative_transition
      period hPeriod potential component firstAnchor secondAnchor current
        hCurrent)

/-- Combined second-order law.  Its left side is the base-chart chain rule;
its right side is the four-term varying-frame Leibniz rule. -/
theorem throatGaugeCovectorSecondOrderJet_combinedFrameBaseChart_secondDerivative_transition_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : ThroatCoverCoordinates) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component secondAnchor secondCenter current hCurrent.2 hSecond).secondDerivative
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod current secondCenter)
          (extChartAt throatCoverModelWithCorners current current) first)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod current secondCenter)
          (extChartAt throatCoverModelWithCorners current current) second) +
      (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
        component secondAnchor secondCenter current hCurrent.2 hSecond).firstDerivative
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod current secondCenter))
            (extChartAt throatCoverModelWithCorners current current)
              first second) =
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current
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
  have hBase :=
    throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative_transition_apply
      period hPeriod potential component secondAnchor current secondCenter
        current hCurrent.2 (mem_extChartAt_source current) hSecond first second
  have hBase' :
      (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
        component secondAnchor current hCurrent.2).secondDerivative first second =
        (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component secondAnchor secondCenter current hCurrent.2 hSecond).secondDerivative
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod current secondCenter)
              (extChartAt throatCoverModelWithCorners current current) first)
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod current secondCenter)
              (extChartAt throatCoverModelWithCorners current current) second) +
        (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component secondAnchor secondCenter current hCurrent.2 hSecond).firstDerivative
            (fderiv Real
              (fderiv Real
                (throatGaugeBaseChartTransition period hPeriod current secondCenter))
              (extChartAt throatCoverModelWithCorners current current)
                first second) := by
    simpa only [
      throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative_diagonal,
      throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative_diagonal]
      using hBase
  exact hBase'.symm.trans
    (throatGaugeCovectorSecondOrderJetInFrameAt_secondDerivative_transition_apply
      period hPeriod potential component firstAnchor secondAnchor current
        hCurrent first second)

end
end P0EFTJanusProgramPActualThroatGaugeCombinedFrameBaseChartSecondOrderJetOverlap4D
end JanusFormal
