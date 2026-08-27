import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeFrameTransitionInBaseChartSecondOrderJetOverlap4D

/-!
# Arbitrary frame and base-chart overlap law for the throat gauge jet

Both the tangent-frame anchor and the base-chart anchor may now change between
source and target.  At a common throat point, the representative germ and the
value, first-derivative and second-derivative laws combine the exact varying
frame action with the genuine base-chart chain rule.

This is pairwise local descent data, not yet its triple cocycle or quotient.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartSecondOrderJetOverlap4D

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
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeFrameTransitionInBaseChartSecondOrderJetOverlap4D

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

/-! ## Arbitrary-pair germ -/

/-- Changing frame in `firstCenter` and then changing base chart gives exactly
the target representative as a germ. -/
theorem throatGaugeCovectorCenteredChart_arbitraryFrameBaseChartTransition_eventuallyEq
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (fun coordinate =>
      throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter coordinate
        (throatGaugeCovectorCenteredChart period hPeriod potential component
          firstAnchor firstCenter coordinate)) =ᶠ[𝓝
            (extChartAt throatCoverModelWithCorners firstCenter current)]
      (throatGaugeCovectorCenteredChart period hPeriod potential component
          secondAnchor secondCenter) ∘
        throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter := by
  exact
    (throatGaugeCovectorCenteredChart_frameTransition_eventuallyEq_of_mem_source
      period hPeriod potential component firstAnchor secondAnchor firstCenter
        current hCurrent hFirst).trans
    (throatGaugeCovectorCenteredChart_baseChartTransition_eventuallyEq
      period hPeriod potential component secondAnchor firstCenter secondCenter
        current hFirst hSecond)

/-! ## Exact arbitrary-pair jet laws -/

/-- The target value is the exact contragredient transport of the source
value, independently of the selected base charts. -/
theorem throatGaugeCovectorSecondOrderJet_arbitraryFrameBaseChart_value
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component secondAnchor secondCenter current hCurrent.2 hSecond).value =
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current
        (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor firstCenter current hCurrent.1 hFirst).value := by
  rw [throatGaugeCovectorSecondOrderJetInBaseChartAt_value,
    throatGaugeCovectorSecondOrderJetInBaseChartAt_value]
  exact (throatGaugeCovectorCoordinatesTransported_eq period hPeriod potential
    component firstAnchor secondAnchor current hCurrent).symm

/-- Arbitrary-pair first-order law: the target derivative pulled back by the
base-chart Jacobian equals the varying-frame Leibniz expression. -/
theorem throatGaugeCovectorSecondOrderJet_arbitraryFrameBaseChart_firstDerivative_transition
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component secondAnchor secondCenter current hCurrent.2 hSecond).firstDerivative.comp
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)) =
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates).comp
        (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor firstCenter current hCurrent.1 hFirst).firstDerivative +
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current)).flip
          (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
            component firstAnchor firstCenter current hCurrent.1 hFirst).value := by
  have hBase :=
    throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative_transition
      period hPeriod potential component secondAnchor firstCenter secondCenter
        current hCurrent.2 hFirst hSecond
  exact hBase.symm.trans
    (throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative_frame_transition
      period hPeriod potential component firstAnchor secondAnchor firstCenter
        current hCurrent hFirst)

/-- Arbitrary-pair second-order law.  The base-chart Hessian terms on the left
equal the full four-term varying-frame expression on the right. -/
theorem throatGaugeCovectorSecondOrderJet_arbitraryFrameBaseChart_secondDerivative_transition_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : ThroatCoverCoordinates) :
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component secondAnchor secondCenter current hCurrent.2 hSecond).secondDerivative
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) first)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) second) +
      (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
        component secondAnchor secondCenter current hCurrent.2 hSecond).firstDerivative
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter))
            (extChartAt throatCoverModelWithCorners firstCenter current)
              first second) =
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current
        ((throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor firstCenter current hCurrent.1 hFirst).secondDerivative
            first second) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) first
        ((throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor firstCenter current hCurrent.1 hFirst).firstDerivative
            second) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) second
        ((throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor firstCenter current hCurrent.1 hFirst).firstDerivative
            first) +
      fderiv Real
          (fun coordinate =>
            fderiv Real
              (throatGaugeCovectorTransitionCenteredChart period hPeriod
                firstAnchor secondAnchor firstCenter) coordinate second)
          (extChartAt throatCoverModelWithCorners firstCenter current) first
        ((throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component firstAnchor firstCenter current hCurrent.1 hFirst).value) := by
  have hBase :=
    throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative_transition_apply
      period hPeriod potential component secondAnchor firstCenter secondCenter
        current hCurrent.2 hFirst hSecond first second
  exact hBase.symm.trans
    (throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative_frame_transition_apply
      period hPeriod potential component firstAnchor secondAnchor firstCenter
        current hCurrent hFirst first second)

end
end P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartSecondOrderJetOverlap4D
end JanusFormal
