import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeChartwiseSecondOrderJetOverlap4D

/-!
# Euclidean-carrier overlap law for the actual throat gauge jet

The two-parameter throat gauge jet and its frame-transition law are transported
through the fixed equivalence to the exact `EuclideanR3` gauge-connection
carrier used by the physical structured background.

This is still a fixed-base-chart statement.  No chart-independent descent,
gauge transformation or global connection is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeEuclideanSecondOrderJetOverlap4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeDifferentiatedOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseSecondOrderJetOverlap4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Fixed transport of the two-parameter jet -/

/-- The genuine local gauge jet, with both its base directions and its
covector values transported to the physical Euclidean carrier. -/
def throatGaugeEuclideanSecondOrderJetInFrameAt
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet) :
    FramedSecondOrderJet EuclideanR3 (FramedCovector EuclideanR3) :=
  transportThroatGaugeSecondOrderJetToEuclidean
    (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
      component frameAnchor current hCurrent)

@[simp]
theorem throatGaugeEuclideanSecondOrderJetInFrameAt_value
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet) :
    (throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
      component frameAnchor current hCurrent).value =
      throatCovectorToEuclideanEquiv
        (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
          component frameAnchor current hCurrent).value :=
  rfl

@[simp]
theorem throatGaugeEuclideanSecondOrderJetInFrameAt_firstDerivative_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (direction : EuclideanR3) :
    (throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
      component frameAnchor current hCurrent).firstDerivative direction =
      throatCovectorToEuclideanEquiv
        ((throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
          component frameAnchor current hCurrent).firstDerivative
            (throatRadialReferenceEquiv direction)) :=
  rfl

@[simp]
theorem throatGaugeEuclideanSecondOrderJetInFrameAt_secondDerivative_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (first second : EuclideanR3) :
    (throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
      component frameAnchor current hCurrent).secondDerivative first second =
      throatCovectorToEuclideanEquiv
        ((throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
          component frameAnchor current hCurrent).secondDerivative
            (throatRadialReferenceEquiv first)
            (throatRadialReferenceEquiv second)) :=
  rfl

/-- On the diagonal this Euclidean two-parameter jet is exactly the existing
Candidate-A Euclidean gauge jet. -/
theorem globalCandidateAThroatGaugeEuclideanSecondOrderJetAt_eq_inFrameAt
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod) :
    globalCandidateAThroatGaugeEuclideanSecondOrderJetAt period hPeriod data
        sector component anchor =
      throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data sector)
        component anchor anchor
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor) := by
  rw [globalCandidateAThroatGaugeEuclideanSecondOrderJetAt,
    throatGaugeEuclideanSecondOrderJetInFrameAt,
    globalCandidateAThroatGaugeSecondOrderJetAt_eq_inFrameAt]

/-! ## Transition and its first two variations in the Euclidean carrier -/

/-- Fixed conjugation of a throat-coordinate covector endomorphism to the
physical Euclidean covector model. -/
def transportThroatGaugeCovectorEndomorphismToEuclidean
    (operator : FramedCovector ThroatCoverCoordinates →L[Real]
      FramedCovector ThroatCoverCoordinates) :
    FramedCovector EuclideanR3 →L[Real] FramedCovector EuclideanR3 :=
  throatCovectorToEuclideanEquiv.arrowCongr
    throatCovectorToEuclideanEquiv operator

/-- The order-zero frame transition in the physical covector model. -/
def throatGaugeEuclideanCovectorTransitionAt
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod) :
    FramedCovector EuclideanR3 →L[Real] FramedCovector EuclideanR3 :=
  transportThroatGaugeCovectorEndomorphismToEuclidean
    (throatGaugeCovectorTrivializationTransitionAt period hPeriod
      firstAnchor secondAnchor current)

/-- First variation of the frame transition, transported in both covector
slots and in its base direction. -/
def throatGaugeEuclideanCovectorTransitionFirstVariationAt
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (direction : EuclideanR3) :
    FramedCovector EuclideanR3 →L[Real] FramedCovector EuclideanR3 :=
  transportThroatGaugeCovectorEndomorphismToEuclidean
    (fderiv Real
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor current)
      (extChartAt throatCoverModelWithCorners current current)
      (throatRadialReferenceEquiv direction))

/-- Second variation in two Euclidean base directions, in the same order as
the fixed-chart second-order Leibniz law. -/
def throatGaugeEuclideanCovectorTransitionSecondVariationAt
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (first second : EuclideanR3) :
    FramedCovector EuclideanR3 →L[Real] FramedCovector EuclideanR3 :=
  transportThroatGaugeCovectorEndomorphismToEuclidean
    (fderiv Real
      (fun coordinate =>
        fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor current) coordinate
          (throatRadialReferenceEquiv second))
      (extChartAt throatCoverModelWithCorners current current)
      (throatRadialReferenceEquiv first))

/-! ## Exact overlap laws in the physical carrier -/

/-- The first-derivative overlap law transported to the exact physical gauge
carrier. -/
theorem throatGaugeEuclideanSecondOrderJetInFrameAt_firstDerivative_transition_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (direction : EuclideanR3) :
    (throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
      component secondAnchor current hCurrent.2).firstDerivative direction =
      throatGaugeEuclideanCovectorTransitionAt period hPeriod
        firstAnchor secondAnchor current
        ((throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).firstDerivative direction) +
      throatGaugeEuclideanCovectorTransitionFirstVariationAt period hPeriod
        firstAnchor secondAnchor current direction
        (throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).value := by
  have hIntrinsic :=
    throatGaugeCovectorSecondOrderJetInFrameAt_firstDerivative_transition
      period hPeriod potential component firstAnchor secondAnchor current hCurrent
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        FramedCovector ThroatCoverCoordinates =>
      throatCovectorToEuclideanEquiv
        (derivative (throatRadialReferenceEquiv direction))) hIntrinsic
  simpa only [throatGaugeEuclideanSecondOrderJetInFrameAt_firstDerivative_apply,
    throatGaugeEuclideanSecondOrderJetInFrameAt_value,
    throatGaugeEuclideanCovectorTransitionAt,
    throatGaugeEuclideanCovectorTransitionFirstVariationAt,
    transportThroatGaugeCovectorEndomorphismToEuclidean,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.symm_apply_apply, map_add] using hApplied

/-- The full four-term second-order overlap law transported to the exact
physical gauge carrier. -/
theorem throatGaugeEuclideanSecondOrderJetInFrameAt_secondDerivative_transition_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor)
    (first second : EuclideanR3) :
    (throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
      component secondAnchor current hCurrent.2).secondDerivative first second =
      throatGaugeEuclideanCovectorTransitionAt period hPeriod
        firstAnchor secondAnchor current
        ((throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).secondDerivative
            first second) +
      throatGaugeEuclideanCovectorTransitionFirstVariationAt period hPeriod
        firstAnchor secondAnchor current first
        ((throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).firstDerivative second) +
      throatGaugeEuclideanCovectorTransitionFirstVariationAt period hPeriod
        firstAnchor secondAnchor current second
        ((throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).firstDerivative first) +
      throatGaugeEuclideanCovectorTransitionSecondVariationAt period hPeriod
        firstAnchor secondAnchor current first second
        (throatGaugeEuclideanSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).value := by
  have hIntrinsic :=
    throatGaugeCovectorSecondOrderJetInFrameAt_secondDerivative_transition_apply
      period hPeriod potential component firstAnchor secondAnchor current hCurrent
        (throatRadialReferenceEquiv first)
        (throatRadialReferenceEquiv second)
  have hTransported := congrArg
    (fun covector : FramedCovector ThroatCoverCoordinates =>
      throatCovectorToEuclideanEquiv covector) hIntrinsic
  simpa only [throatGaugeEuclideanSecondOrderJetInFrameAt_secondDerivative_apply,
    throatGaugeEuclideanSecondOrderJetInFrameAt_firstDerivative_apply,
    throatGaugeEuclideanSecondOrderJetInFrameAt_value,
    throatGaugeEuclideanCovectorTransitionAt,
    throatGaugeEuclideanCovectorTransitionFirstVariationAt,
    throatGaugeEuclideanCovectorTransitionSecondVariationAt,
    transportThroatGaugeCovectorEndomorphismToEuclidean,
    ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.coe_coe, map_add] using hTransported

end
end P0EFTJanusProgramPActualThroatGaugeEuclideanSecondOrderJetOverlap4D
end JanusFormal
