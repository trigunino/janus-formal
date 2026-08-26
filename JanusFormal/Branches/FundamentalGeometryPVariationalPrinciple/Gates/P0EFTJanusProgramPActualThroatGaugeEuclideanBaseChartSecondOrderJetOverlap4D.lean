import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeEuclideanSecondOrderJetOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D

/-!
# Euclidean base-chart overlap law for the actual throat gauge jet

The three-parameter gauge jet and the derivatives of its genuine base-chart
transition are transported to the exact `EuclideanR3` physical carrier.  The
first- and second-order chain rules retain their precise holonomic form.

No chart-independent quotient or global connection is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeEuclideanBaseChartSecondOrderJetOverlap4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeEuclideanSecondOrderJetOverlap4D

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

/-! ## Euclidean three-parameter jet -/

/-- The actual gauge jet with independent frame anchor, base-chart anchor and
evaluation point, transported to the physical Euclidean carrier. -/
def throatGaugeEuclideanSecondOrderJetInBaseChartAt
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedSecondOrderJet EuclideanR3 (FramedCovector EuclideanR3) :=
  transportThroatGaugeSecondOrderJetToEuclidean
    (throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame hChart)

@[simp]
theorem throatGaugeEuclideanSecondOrderJetInBaseChartAt_firstDerivative_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source)
    (direction : EuclideanR3) :
    (throatGaugeEuclideanSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame hChart).firstDerivative
        direction =
      throatCovectorToEuclideanEquiv
        ((throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component frameAnchor chartAnchor current hFrame hChart).firstDerivative
            (throatRadialReferenceEquiv direction)) :=
  rfl

@[simp]
theorem throatGaugeEuclideanSecondOrderJetInBaseChartAt_secondDerivative_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source)
    (first second : EuclideanR3) :
    (throatGaugeEuclideanSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame hChart).secondDerivative
        first second =
      throatCovectorToEuclideanEquiv
        ((throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component frameAnchor chartAnchor current hFrame hChart).secondDerivative
            (throatRadialReferenceEquiv first)
            (throatRadialReferenceEquiv second)) :=
  rfl

/-! ## Euclidean derivatives of the base-chart transition -/

/-- Jacobian of the base-chart transition in the fixed Euclidean model. -/
def throatGaugeEuclideanBaseChartTransitionFirstDerivativeAt
    (firstCenter secondCenter current : EffectiveThroat period hPeriod) :
    EuclideanR3 →L[Real] EuclideanR3 :=
  throatToEuclideanEquiv.arrowCongr throatToEuclideanEquiv
    (fderiv Real
      (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
      (extChartAt throatCoverModelWithCorners firstCenter current))

/-- Hessian of the base-chart transition in the fixed Euclidean model. -/
def throatGaugeEuclideanBaseChartTransitionSecondDerivativeAt
    (firstCenter secondCenter current : EffectiveThroat period hPeriod) :
    EuclideanR3 →L[Real] EuclideanR3 →L[Real] EuclideanR3 :=
  throatToEuclideanEquiv.arrowCongr
    (throatToEuclideanEquiv.arrowCongr throatToEuclideanEquiv)
    (fderiv Real
      (fderiv Real
        (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter))
      (extChartAt throatCoverModelWithCorners firstCenter current))

/-! ## Exact physical-carrier chain rules -/

/-- First-order base-chart chain rule in the exact Euclidean gauge carrier. -/
theorem throatGaugeEuclideanSecondOrderJetInBaseChartAt_firstDerivative_transition_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (direction : EuclideanR3) :
    (throatGaugeEuclideanSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor firstCenter current hFrame hFirst).firstDerivative
        direction =
      (throatGaugeEuclideanSecondOrderJetInBaseChartAt period hPeriod potential
        component frameAnchor secondCenter current hFrame hSecond).firstDerivative
          (throatGaugeEuclideanBaseChartTransitionFirstDerivativeAt
            period hPeriod firstCenter secondCenter current direction) := by
  have hRaw := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        FramedCovector ThroatCoverCoordinates =>
      throatCovectorToEuclideanEquiv
        (derivative (throatRadialReferenceEquiv direction)))
    (throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative_transition
      period hPeriod potential component frameAnchor firstCenter secondCenter
        current hFrame hFirst hSecond)
  simpa only [
    throatGaugeEuclideanSecondOrderJetInBaseChartAt_firstDerivative_apply,
    throatGaugeEuclideanBaseChartTransitionFirstDerivativeAt,
    throatToEuclideanEquiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_symm] using hRaw

/-- Second-order base-chart chain rule in the exact Euclidean gauge carrier. -/
theorem throatGaugeEuclideanSecondOrderJetInBaseChartAt_secondDerivative_transition_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : EuclideanR3) :
    (throatGaugeEuclideanSecondOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor firstCenter current hFrame hFirst).secondDerivative
        first second =
      (throatGaugeEuclideanSecondOrderJetInBaseChartAt period hPeriod potential
        component frameAnchor secondCenter current hFrame hSecond).secondDerivative
          (throatGaugeEuclideanBaseChartTransitionFirstDerivativeAt
            period hPeriod firstCenter secondCenter current first)
          (throatGaugeEuclideanBaseChartTransitionFirstDerivativeAt
            period hPeriod firstCenter secondCenter current second) +
      (throatGaugeEuclideanSecondOrderJetInBaseChartAt period hPeriod potential
        component frameAnchor secondCenter current hFrame hSecond).firstDerivative
          (throatGaugeEuclideanBaseChartTransitionSecondDerivativeAt
            period hPeriod firstCenter secondCenter current first second) := by
  have hRaw := congrArg
    (fun covector : FramedCovector ThroatCoverCoordinates =>
      throatCovectorToEuclideanEquiv covector)
    (throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative_transition_apply
      period hPeriod potential component frameAnchor firstCenter secondCenter
        current hFrame hFirst hSecond
        (throatRadialReferenceEquiv first)
        (throatRadialReferenceEquiv second))
  simpa only [
    throatGaugeEuclideanSecondOrderJetInBaseChartAt_secondDerivative_apply,
    throatGaugeEuclideanSecondOrderJetInBaseChartAt_firstDerivative_apply,
    throatGaugeEuclideanBaseChartTransitionFirstDerivativeAt,
    throatGaugeEuclideanBaseChartTransitionSecondDerivativeAt,
    throatToEuclideanEquiv,
    ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_symm, map_add] using hRaw

end
end P0EFTJanusProgramPActualThroatGaugeEuclideanBaseChartSecondOrderJetOverlap4D
end JanusFormal
