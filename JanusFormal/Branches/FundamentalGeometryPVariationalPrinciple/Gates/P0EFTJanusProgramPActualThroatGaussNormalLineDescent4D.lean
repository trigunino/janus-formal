import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatOrientedGaussNormalBackgroundBridge4D

/-!
# Actual throat Gauss normal-line descent

The deck-odd scalar coordinate of the actual Gauss form defines a point of
the associated normal line.  This gate only descends its pointwise values;
it makes no descent claim for the full second-order jet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaussNormalLineDescent4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusNormalLine
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatOrientedGaussNormalBackgroundBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The associated-line point represented by an oriented lift and a scalar
normal coefficient. -/
def normalLinePointOfOrientedCoefficient
    (boundary : CutThroatBoundary period hPeriod) (coefficient : Real) :
    MappingTorusNormalLine period hPeriod :=
  orientationNormalToOriginal period hPeriod
    (orientationNormalTrivializationInv period hPeriod (boundary, coefficient))

@[simp] theorem normalLinePointOfOrientedCoefficient_projection
    (boundary : CutThroatBoundary period hPeriod) (coefficient : Real) :
    normalLineProjection period hPeriod
        (normalLinePointOfOrientedCoefficient period hPeriod boundary coefficient) =
      orientationDoubleToThroat period hPeriod boundary := by
  refine Quotient.inductionOn boundary ?_
  intro representative
  rfl

/-- Deck reversal together with coefficient reversal represents the same
point of the associated normal line. -/
@[simp] theorem normalLinePointOfOrientedCoefficient_deck_neg
    (boundary : CutThroatBoundary period hPeriod) (coefficient : Real) :
    normalLinePointOfOrientedCoefficient period hPeriod
        (orientationDeck period hPeriod boundary) (-coefficient) =
      normalLinePointOfOrientedCoefficient period hPeriod boundary coefficient := by
  refine Quotient.inductionOn boundary ?_
  intro representative
  change normalLineMk period hPeriod
      ⟨orientationDoubleCoverHomeomorph period hPeriod
        (orientationDeckCover period hPeriod representative), -coefficient⟩ =
    normalLineMk period hPeriod
      ⟨orientationDoubleCoverHomeomorph period hPeriod representative, coefficient⟩
  rw [show orientationDoubleCoverHomeomorph period hPeriod
      (orientationDeckCover period hPeriod representative) =
        (1 : Int) +ᵥ orientationDoubleCoverHomeomorph period hPeriod representative by
    apply MappingTorusCover.ext
    · simp only [orientationDoubleCoverHomeomorph_fiber,
        orientationDeckCover_fiber, vadd_fiber]
      simp [fixedEquatorData]
    · simp only [orientationDoubleCoverHomeomorph_time,
        orientationDeckCover_time, vadd_time]
      simp [fixedEquatorData]]
  exact one_loop_normal_flip period hPeriod
    (orientationDoubleCoverHomeomorph period hPeriod representative) coefficient

/-- Pointwise associated-normal-line value of the actual Gauss form. -/
def actualThroatSectorGaussNormalLineValueAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector)
    (first second : EuclideanR3) : MappingTorusNormalLine period hPeriod :=
  normalLinePointOfOrientedCoefficient period hPeriod boundary
    (actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
      boundary sector first second)

@[simp] theorem actualThroatSectorGaussNormalLineValueAt_projection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector)
    (first second : EuclideanR3) :
    normalLineProjection period hPeriod
        (actualThroatSectorGaussNormalLineValueAt period hPeriod configuration
          boundary sector first second) =
      orientationDoubleToThroat period hPeriod boundary := by
  exact normalLinePointOfOrientedCoefficient_projection period hPeriod _ _

theorem actualThroatSectorGaussNormalLineValueAt_symmetric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector)
    (first second : EuclideanR3) :
    actualThroatSectorGaussNormalLineValueAt period hPeriod configuration
        boundary sector first second =
      actualThroatSectorGaussNormalLineValueAt period hPeriod configuration
        boundary sector second first := by
  unfold actualThroatSectorGaussNormalLineValueAt
  rw [actualThroatSectorGaussNormalQuadraticAt_symmetric]

/-- The associated-line value is independent of deck reversal. -/
theorem actualThroatSectorGaussNormalLineValueAt_deck
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector)
    (first second : EuclideanR3) :
    actualThroatSectorGaussNormalLineValueAt period hPeriod configuration
        (orientationDeck period hPeriod boundary) sector first second =
      actualThroatSectorGaussNormalLineValueAt period hPeriod configuration
        boundary sector first second := by
  unfold actualThroatSectorGaussNormalLineValueAt
  have hDeck := congrArg (fun form ↦ form first second)
    (actualThroatSectorGaussNormalQuadraticAt_deck period hPeriod
      configuration hTransverse boundary sector)
  simp only [neg_apply] at hDeck
  rw [hDeck]
  exact normalLinePointOfOrientedCoefficient_deck_neg period hPeriod _ _

/-- Pointwise descent is independent of any two orientation lifts over the
same effective throat point. -/
theorem actualThroatSectorGaussNormalLineValueAt_eq_of_same_projection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (firstBoundary secondBoundary : CutThroatBoundary period hPeriod)
    (hSame : orientationDoubleToThroat period hPeriod firstBoundary =
      orientationDoubleToThroat period hPeriod secondBoundary)
    (sector : Sector) (first second : EuclideanR3) :
    actualThroatSectorGaussNormalLineValueAt period hPeriod configuration
        firstBoundary sector first second =
      actualThroatSectorGaussNormalLineValueAt period hPeriod configuration
        secondBoundary sector first second := by
  rcases (orientationDouble_fiber_iff period hPeriod
    firstBoundary secondBoundary).mp hSame with h | h
  · rw [h]
  · rw [h]
    exact actualThroatSectorGaussNormalLineValueAt_deck period hPeriod
      configuration hTransverse secondBoundary sector first second

/-- A set-theoretic choice of orientation lift, used only to expose the
pointwise descended value on the effective throat. -/
def actualThroatChosenOrientationLift
    (throat : MappingTorus (fixedEquatorData period hPeriod)) :
    CutThroatBoundary period hPeriod :=
  Classical.choose (orientationDoubleToThroat_surjective period hPeriod throat)

@[simp] theorem actualThroatChosenOrientationLift_projects
    (throat : MappingTorus (fixedEquatorData period hPeriod)) :
    orientationDoubleToThroat period hPeriod
        (actualThroatChosenOrientationLift period hPeriod throat) = throat :=
  Classical.choose_spec (orientationDoubleToThroat_surjective period hPeriod throat)

/-- Pointwise Gauss value on the unoriented throat.  Its lift-independence is
the theorem below; no continuity assertion is made for the chosen lift. -/
def actualThroatSectorGaussNormalLineValue
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (_hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (throat : MappingTorus (fixedEquatorData period hPeriod)) (sector : Sector)
    (first second : EuclideanR3) : MappingTorusNormalLine period hPeriod :=
  actualThroatSectorGaussNormalLineValueAt period hPeriod configuration
    (actualThroatChosenOrientationLift period hPeriod throat) sector first second

@[simp] theorem actualThroatSectorGaussNormalLineValue_projection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (throat : MappingTorus (fixedEquatorData period hPeriod)) (sector : Sector)
    (first second : EuclideanR3) :
    normalLineProjection period hPeriod
        (actualThroatSectorGaussNormalLineValue period hPeriod configuration
          hTransverse throat sector first second) = throat := by
  rw [actualThroatSectorGaussNormalLineValue,
    actualThroatSectorGaussNormalLineValueAt_projection,
    actualThroatChosenOrientationLift_projects]

theorem actualThroatSectorGaussNormalLineValue_eq_at_lift
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (throat : MappingTorus (fixedEquatorData period hPeriod))
    (boundary : CutThroatBoundary period hPeriod)
    (hBoundary : orientationDoubleToThroat period hPeriod boundary = throat)
    (sector : Sector) (first second : EuclideanR3) :
    actualThroatSectorGaussNormalLineValue period hPeriod configuration
        hTransverse throat sector first second =
      actualThroatSectorGaussNormalLineValueAt period hPeriod configuration
        boundary sector first second := by
  apply actualThroatSectorGaussNormalLineValueAt_eq_of_same_projection
    period hPeriod configuration hTransverse
  rw [actualThroatChosenOrientationLift_projects, hBoundary]

theorem actualThroatSectorGaussNormalLineValue_symmetric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (throat : MappingTorus (fixedEquatorData period hPeriod)) (sector : Sector)
    (first second : EuclideanR3) :
    actualThroatSectorGaussNormalLineValue period hPeriod configuration
        hTransverse throat sector first second =
      actualThroatSectorGaussNormalLineValue period hPeriod configuration
        hTransverse throat sector second first := by
  unfold actualThroatSectorGaussNormalLineValue
  exact actualThroatSectorGaussNormalLineValueAt_symmetric period hPeriod
    configuration _ sector first second

end
end P0EFTJanusProgramPActualThroatGaussNormalLineDescent4D
end JanusFormal
