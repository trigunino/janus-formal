import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

/-!
# Unoriented scalar-current cancellation on the cut boundary

The residual deck involution is half-period translation on the doubled throat
and preserves its canonical measure.  Since the descended scalar current is
deck-odd, its unoriented integral vanishes.  The oriented Stokes density also
contains the reversing normal orientation and is deliberately not identified
with this scalar integral.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryScalarCurrentIntegralCancellation4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance boundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

local instance boundaryMeasurableSpace :
    MeasurableSpace (CutThroatBoundary period hPeriod) := borel _

local instance boundaryBorelSpace :
    BorelSpace (CutThroatBoundary period hPeriod) where
  measurable_eq := rfl

/-- Canonical positive measure on the orientation-double throat. -/
def cutBoundaryCanonicalMeasure :
    Measure (CutThroatBoundary period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

/-- The residual deck involution is exactly translation by the original
period on the doubled-period throat. -/
theorem orientationDeck_eq_throatTimeFlow :
    orientationDeck period hPeriod =
      throatTimeFlow (doubledPeriod period)
        (doubledPeriod_ne_zero period hPeriod) period := by
  funext boundary
  refine Quotient.inductionOn boundary ?_
  intro point
  rfl

theorem cutBoundaryCanonicalMeasure_orientationDeck_measurePreserving :
    MeasurePreserving (orientationDeck period hPeriod)
      (cutBoundaryCanonicalMeasure period hPeriod)
      (cutBoundaryCanonicalMeasure period hPeriod) := by
  rw [orientationDeck_eq_throatTimeFlow]
  exact intrinsicCanonicalThroatVolumeMeasure_timeTranslation_measurePreserving
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) period

/-- The scalar current cancels between the two unoriented lifts. -/
theorem integral_cutBoundaryScalarCurrent_eq_zero
    (field test : SmoothQuotientField period hPeriod Real) :
    ∫ boundary, cutBoundaryScalarCurrent period hPeriod field test boundary
        ∂cutBoundaryCanonicalMeasure period hPeriod = 0 := by
  let deckEquiv := (orientationDeckHomeomorph period hPeriod).toMeasurableEquiv
  have hDeckMeasure : MeasurePreserving deckEquiv
      (cutBoundaryCanonicalMeasure period hPeriod)
      (cutBoundaryCanonicalMeasure period hPeriod) := by
    change MeasurePreserving (orientationDeck period hPeriod)
      (cutBoundaryCanonicalMeasure period hPeriod)
      (cutBoundaryCanonicalMeasure period hPeriod)
    exact cutBoundaryCanonicalMeasure_orientationDeck_measurePreserving
      period hPeriod
  have hChange := hDeckMeasure.integral_comp'
    (cutBoundaryScalarCurrent period hPeriod field test)
  have hOdd :
      (fun boundary => cutBoundaryScalarCurrent period hPeriod field test
        (deckEquiv boundary)) =
      fun boundary => -cutBoundaryScalarCurrent period hPeriod field test boundary := by
    funext boundary
    exact cutBoundaryScalarCurrent_deck period hPeriod field test boundary
  rw [hOdd, integral_neg] at hChange
  linarith

end
end P0EFTJanusMappingTorusCutBoundaryScalarCurrentIntegralCancellation4D
end JanusFormal
