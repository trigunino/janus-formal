import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatStructuredBackgroundCompletion4D

/-!
# Actual oriented Gauss normal background

This gate fills the normal slots from the genuine sector metric at the fixed
throat. Under `HasNoTangentialRadical`, its bundled continuous quadratic is
the Gauss second fundamental form, is symmetric, and is odd under the
orientation deck involution. The selected metric normal is nonzero, has
absolute square one, and has causal sign `+1` or `-1`; orthogonality is the
imported `normalGraphCanonicalMetricUnitNormal_orthogonal` theorem.

The background scalar `1` is only the coordinate of that normal in the local
oriented frame. It is not a global trivialization of the normal line.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatOrientedGaussNormalBackgroundBridge4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatTangentialConnectionQuadratic4D
open P0EFTJanusProgramPActualThroatStructuredBackgroundCompletion4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Non-nullness at the fixed throat, derived from the actual sector metric. -/
def actualThroatSectorNormalNonNull
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) :
    NormalGraphNonNullAt period hPeriod
      (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
      (zeroNormalDisplacement period hPeriod) 0 :=
  zero_mem_normalGraphNonNullDomain period hPeriod
    (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
    (zeroNormalDisplacement period hPeriod) (hTransverse sector)

/-- The genuine normalized metric normal selected by one lift of the throat's
orientation double cover. -/
def actualThroatSectorMetricUnitNormalAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector) :=
  normalGraphCanonicalMetricUnitNormal period hPeriod
    (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
    (zeroNormalDisplacement period hPeriod) 0
    (actualThroatSectorNormalNonNull period hPeriod configuration hTransverse
      sector)
    boundary

/-- The actual Gauss second fundamental form in the fixed physical
`EuclideanR3` tangent frame. The normal model is the oriented unit-normal
coordinate line selected by `boundary`. -/
def actualThroatSectorGaussNormalQuadraticAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector) :
    ContinuousSecondFundamentalForm
      (Tangent := EuclideanR3) (Normal := Real) :=
  let metric :=
    globalGaugeFixedBulkMetricBySector period hPeriod configuration sector
  let displacement := zeroNormalDisplacement period hPeriod
  let base := orientationDoubleToThroat period hPeriod boundary
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, 0)
  let patch := normalGraphCanonicalSelectedHolonomicPatchAt
    period hPeriod point
  let coordinate := normalGraphCanonicalSelectedHolonomicCoordinateAt
    period hPeriod point
  throatMetricTensorToEuclideanEquiv
    (normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
      period hPeriod metric displacement boundary 0 patch coordinate (base, 0))

theorem actualThroatSectorGaussNormalQuadraticAt_symmetric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector)
    (first second : EuclideanR3) :
    actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        boundary sector first second =
      actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        boundary sector second first := by
  unfold actualThroatSectorGaussNormalQuadraticAt
  simp only [throatMetricTensorToEuclideanEquiv, throatToEuclideanEquiv,
    ContinuousLinearEquiv.arrowCongr_apply]
  rw [normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_apply,
    normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_apply]
  ring_nf

/-- At the throat anchor, the bundled continuous form is exactly the genuine
Gauss second fundamental form of the actual sector metric. -/
theorem actualThroatSectorGaussNormalQuadraticAt_eq_gauss
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector)
    (first second : EuclideanR3) :
    let metric :=
      globalGaugeFixedBulkMetricBySector period hPeriod configuration sector
    let displacement := zeroNormalDisplacement period hPeriod
    let hNonNull := actualThroatSectorNormalNonNull period hPeriod configuration
      hTransverse sector
    let point := normalGraphOrientationDouble period hPeriod displacement
      (boundary, 0)
    let patch := normalGraphCanonicalSelectedHolonomicPatchAt
      period hPeriod point
    let coordinate := normalGraphCanonicalSelectedHolonomicCoordinateAt
      period hPeriod point
    actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        boundary sector first second =
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt
        period hPeriod metric displacement 0 hNonNull boundary patch coordinate
          (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod point)
          (throatRadialReferenceEquiv first)
          (throatRadialReferenceEquiv second) := by
  dsimp only
  unfold actualThroatSectorGaussNormalQuadraticAt
  simp only [throatMetricTensorToEuclideanEquiv, throatToEuclideanEquiv,
    ContinuousLinearEquiv.arrowCongr_apply]
  rw [normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_apply,
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_base_eq_gauss
      period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
        (zeroNormalDisplacement period hPeriod) 0
        (actualThroatSectorNormalNonNull period hPeriod configuration hTransverse
          sector)
        boundary
        (normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod
          (normalGraphOrientationDouble period hPeriod
            (zeroNormalDisplacement period hPeriod) (boundary, 0)))
        (normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod
          (normalGraphOrientationDouble period hPeriod
            (zeroNormalDisplacement period hPeriod) (boundary, 0)))
        (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod
          (normalGraphOrientationDouble period hPeriod
            (zeroNormalDisplacement period hPeriod) (boundary, 0))),
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_base_eq_gauss
      period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
        (zeroNormalDisplacement period hPeriod) 0
        (actualThroatSectorNormalNonNull period hPeriod configuration hTransverse
          sector)
        boundary
        (normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod
          (normalGraphOrientationDouble period hPeriod
            (zeroNormalDisplacement period hPeriod) (boundary, 0)))
        (normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod
          (normalGraphOrientationDouble period hPeriod
            (zeroNormalDisplacement period hPeriod) (boundary, 0)))
        (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod
          (normalGraphOrientationDouble period hPeriod
            (zeroNormalDisplacement period hPeriod) (boundary, 0)))]
  rfl

/-- Reversing the chosen orientation lift reverses the scalar-valued second
fundamental form. -/
theorem actualThroatSectorGaussNormalQuadraticAt_deck
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector) :
    actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        (orientationDeck period hPeriod boundary) sector =
      -actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        boundary sector := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  simp only [neg_apply]
  rw [actualThroatSectorGaussNormalQuadraticAt_eq_gauss period hPeriod
      configuration hTransverse (orientationDeck period hPeriod boundary)
      sector first second,
    actualThroatSectorGaussNormalQuadraticAt_eq_gauss period hPeriod
      configuration hTransverse boundary sector first second]
  let metric :=
    globalGaugeFixedBulkMetricBySector period hPeriod configuration sector
  let displacement := zeroNormalDisplacement period hPeriod
  let hNonNull := actualThroatSectorNormalNonNull period hPeriod configuration
    hTransverse sector
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, 0)
  let deckPoint := normalGraphOrientationDouble period hPeriod displacement
    (orientationDeck period hPeriod boundary, 0)
  let patch := normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod point
  let coordinate :=
    normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod point
  let deckPatch :=
    normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod deckPoint
  let deckCoordinate :=
    normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod deckPoint
  have hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, 0) := by
    simpa [point, patch, coordinate] using
      normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod point
  have hAtDeck : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, 0) :=
    hAt.trans
      (normalGraphOrientationDouble_deck period hPeriod displacement boundary
        0).symm
  have hSelectedDeck : deckPatch.coordinateMap deckCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, 0) := by
    simpa [deckPoint, deckPatch, deckCoordinate] using
      normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod deckPoint
  have hChart :=
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt_chart_independent
      period hPeriod metric displacement 0 hNonNull
        (orientationDeck period hPeriod boundary) deckPatch patch deckCoordinate
          coordinate hSelectedDeck hAtDeck (throatRadialReferenceEquiv first)
            (throatRadialReferenceEquiv second)
  have hDeck :=
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt_deck
      period hPeriod metric displacement 0 hNonNull boundary patch coordinate
        hAt hAtDeck (throatRadialReferenceEquiv first)
          (throatRadialReferenceEquiv second)
  simpa [metric, displacement, hNonNull, point, deckPoint, patch, coordinate,
    deckPatch, deckCoordinate] using hChart.trans hDeck

/-- Completion of the background's two missing normal slots. The scalar `1`
is local: it is the coordinate of the metric unit normal in the oriented frame
selected by `boundary`, not a global trivialization of the normal line. -/
def actualThroatOrientedGaussCompletionData
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) :
    ExternalThroatStructuredBackgroundCompletionData where
  normalQuadratic :=
    actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
      boundary
  physicalNormal := fun _ => 1
  normalQuadratic_symmetric := fun sector first second =>
    actualThroatSectorGaussNormalQuadraticAt_symmetric period hPeriod
      configuration boundary sector first second

@[simp] theorem actualThroatOrientedGaussCompletionData_physicalNormal
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector) :
    (actualThroatOrientedGaussCompletionData period hPeriod configuration
      boundary).physicalNormal sector = 1 :=
  rfl

theorem actualThroatSectorMetricUnitNormalAt_abs_square
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector) :
    let metric :=
      globalGaugeFixedBulkMetricBySector period hPeriod configuration sector
    let normal := actualThroatSectorMetricUnitNormalAt period hPeriod
      configuration hTransverse boundary sector
    |metric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod
          (zeroNormalDisplacement period hPeriod) (boundary, 0))
        normal normal| = 1 := by
  dsimp only
  exact abs_normalGraphCanonicalMetricUnitNormal_square period hPeriod
    (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
    (zeroNormalDisplacement period hPeriod) 0
    (actualThroatSectorNormalNonNull period hPeriod configuration hTransverse
      sector)
    boundary

theorem actualThroatSectorMetricUnitNormalAt_ne_zero
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector) :
    actualThroatSectorMetricUnitNormalAt period hPeriod configuration
      hTransverse boundary sector ≠ 0 := by
  unfold actualThroatSectorMetricUnitNormalAt
  exact normalGraphCanonicalMetricUnitNormal_ne_zero period hPeriod
    (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
    (zeroNormalDisplacement period hPeriod) 0
    (actualThroatSectorNormalNonNull period hPeriod configuration hTransverse
      sector)
    boundary

theorem actualThroatSectorMetricUnitNormalAt_causalSign_admissible
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector) :
    let metric :=
      globalGaugeFixedBulkMetricBySector period hPeriod configuration sector
    let displacement := zeroNormalDisplacement period hPeriod
    let hNonNull := actualThroatSectorNormalNonNull period hPeriod configuration
      hTransverse sector
    normalGraphMetricNormalCausalSign period hPeriod metric displacement 0
        hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalNormalClass period hPeriod displacement 0 boundary) =
          1 ∨
      normalGraphMetricNormalCausalSign period hPeriod metric displacement 0
        hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalNormalClass period hPeriod displacement 0 boundary) =
          -1 := by
  dsimp only
  exact normalGraphCanonicalMetricUnitNormal_causalSign_admissible period hPeriod
    (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
    (zeroNormalDisplacement period hPeriod) 0
    (actualThroatSectorNormalNonNull period hPeriod configuration hTransverse
      sector)
    boundary

theorem actualThroatSectorMetricUnitNormalAt_deck
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (boundary : CutThroatBoundary period hPeriod) (sector : Sector) :
    HEq
      (actualThroatSectorMetricUnitNormalAt period hPeriod configuration
        hTransverse (orientationDeck period hPeriod boundary) sector)
      (-actualThroatSectorMetricUnitNormalAt period hPeriod configuration
        hTransverse boundary sector) := by
  unfold actualThroatSectorMetricUnitNormalAt
  exact normalGraphCanonicalMetricUnitNormal_deck period hPeriod
    (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
    (zeroNormalDisplacement period hPeriod) 0
    (actualThroatSectorNormalNonNull period hPeriod configuration hTransverse
      sector)
    boundary

/-- Actual structured background at one oriented lift of the physical throat. -/
def globalCandidateAActualOrientedGaussThroatStructuredBackgroundSecondJet
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)) :
    StructuredBackgroundSecondJet EuclideanR3 :=
  globalCandidateAConditionalThroatStructuredBackgroundSecondJet
    period hPeriod configuration data
      (orientationDoubleToThroat period hPeriod boundary) hTransverse
      (actualThroatOrientedGaussCompletionData period hPeriod configuration
        boundary)

@[simp] theorem globalCandidateAActualOrientedGaussThroatStructuredBackgroundSecondJet_normalQuadratic
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) :
    (globalCandidateAActualOrientedGaussThroatStructuredBackgroundSecondJet
      period hPeriod configuration data boundary hTransverse).normalQuadratic
        sector =
      actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        boundary sector :=
  rfl

@[simp] theorem globalCandidateAActualOrientedGaussThroatStructuredBackgroundSecondJet_physicalNormal
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (boundary : CutThroatBoundary period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) :
    (globalCandidateAActualOrientedGaussThroatStructuredBackgroundSecondJet
      period hPeriod configuration data boundary hTransverse).physicalNormal
        sector = 1 :=
  rfl

end
end P0EFTJanusProgramPActualThroatOrientedGaussNormalBackgroundBridge4D
end JanusFormal
