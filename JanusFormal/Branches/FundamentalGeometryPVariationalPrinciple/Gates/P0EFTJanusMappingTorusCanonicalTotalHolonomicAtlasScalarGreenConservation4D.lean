import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkPointwiseScalarGreenDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D

/-!
# Scalar Green-current conservation on the canonical total atlas
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarGreenConservation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenCoordinateDerivative4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarCovariantDivergence4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- Two equal-mass zero-source local Euler equations force the actual Green
divergence to vanish in that holonomic representative. -/
theorem localActualScalarGreenCoordinateDivergence_eq_zero_of_equalMassEuler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (massSquared : Real) (coordinate : Vector4)
    (hField : localSmoothScalarEulerResidual period hPeriod metric patch field
      massSquared 0 coordinate = 0)
    (hTest : localSmoothScalarEulerResidual period hPeriod metric patch test
      massSquared 0 coordinate = 0) :
    localActualScalarGreenCoordinateDivergence period hPeriod metric patch
      field test coordinate = 0 := by
  rw [localActualScalarGreenCoordinateDivergence_eq_waveDifference]
  unfold localSmoothScalarEulerResidual covariantScalarStressEulerResidual
    pointwiseScalarPotentialSlope at hField hTest
  have hFieldWave :
      covariantScalarJetWave
          (localFixedSignMetric period hPeriod metric patch coordinate)
          (localCovariantScalarJet period hPeriod metric patch field coordinate) =
        massSquared * localScalarRepresentative period hPeriod field patch coordinate := by
    simpa only [add_zero, sub_eq_zero] using hField
  have hTestWave :
      covariantScalarJetWave
          (localFixedSignMetric period hPeriod metric patch coordinate)
          (localCovariantScalarJet period hPeriod metric patch test coordinate) =
        massSquared * localScalarRepresentative period hPeriod test patch coordinate := by
    simpa only [add_zero, sub_eq_zero] using hTest
  rw [hFieldWave, hTestWave]
  ring

/-- Actual Green divergence vanishes in every representative of a selected
covering atlas. -/
def HolonomicAtlasLocalActualScalarGreenDivergenceFree
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (atlas : CanonicalHolonomicAtlasCover period hPeriod) : Prop :=
  ∀ patch : SmoothHolonomicFrameChart4 period hPeriod,
    patch ∈ atlas.atlasPatches → ∀ coordinate : Vector4,
      localActualScalarGreenCoordinateDivergence period hPeriod metric patch
        field test coordinate = 0

theorem holonomicAtlasLocalActualScalarGreenDivergenceFree_of_equalMassEuler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (atlas : CanonicalHolonomicAtlasCover period hPeriod)
    (massSquared : Real)
    (hField : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric
      field atlas massSquared 0)
    (hTest : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric
      test atlas massSquared 0) :
    HolonomicAtlasLocalActualScalarGreenDivergenceFree period hPeriod
      metric field test atlas := by
  intro patch hPatch coordinate
  exact localActualScalarGreenCoordinateDivergence_eq_zero_of_equalMassEuler
    period hPeriod metric patch field test massSquared coordinate
      (hField patch hPatch coordinate) (hTest patch hPatch coordinate)

/-- Coordinate-honest global conservation: above each quotient point there is
a selected representative with genuinely vanishing Green divergence. -/
def QuotientPointwiseActualScalarGreenDivergenceFree
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (atlas : CanonicalHolonomicAtlasCover period hPeriod) : Prop :=
  ∀ point : EffectiveQuotient period hPeriod,
    ∃ patch ∈ atlas.atlasPatches, ∃ coordinate : Vector4,
      patch.coordinateMap coordinate = point ∧
      localActualScalarGreenCoordinateDivergence period hPeriod metric patch
        field test coordinate = 0

theorem quotientPointwiseActualScalarGreenDivergenceFree_of_atlas
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (atlas : CanonicalHolonomicAtlasCover period hPeriod)
    (hFree : HolonomicAtlasLocalActualScalarGreenDivergenceFree period hPeriod
      metric field test atlas) :
    QuotientPointwiseActualScalarGreenDivergenceFree period hPeriod
      metric field test atlas := by
  intro point
  rcases atlas.covers point with ⟨patch, hPatch, coordinate, hCoordinate⟩
  exact ⟨patch, hPatch, coordinate, hCoordinate, hFree patch hPatch coordinate⟩

/-- Equal-mass Euler solutions are globally Green-conserved on the actual
canonical total atlas, with no overlap-rebasing hypothesis. -/
theorem canonicalTotalHolonomicAtlas_scalarGreenDivergenceFree_of_equalMassEuler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (massSquared : Real)
    (hField : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric field
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (hTest : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric test
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0) :
    HolonomicAtlasLocalActualScalarGreenDivergenceFree period hPeriod metric
        field test (canonicalTotalHolonomicAtlasCover period hPeriod) ∧
      QuotientPointwiseActualScalarGreenDivergenceFree period hPeriod metric
        field test (canonicalTotalHolonomicAtlasCover period hPeriod) := by
  let hFree := holonomicAtlasLocalActualScalarGreenDivergenceFree_of_equalMassEuler
    period hPeriod metric field test (canonicalTotalHolonomicAtlasCover period hPeriod)
      massSquared hField hTest
  exact ⟨hFree, quotientPointwiseActualScalarGreenDivergenceFree_of_atlas
    period hPeriod metric field test (canonicalTotalHolonomicAtlasCover period hPeriod)
      hFree⟩

/-- Explicit globally glued on-shell divergence scalar.  Its zero value is
certified below against every canonical holonomic representative. -/
def globalEqualMassEulerActualScalarGreenDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (massSquared : Real)
    (_hField : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric field
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (_hTest : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric test
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0) :
    EffectiveQuotient period hPeriod → Real :=
  fun _ => 0

theorem globalEqualMassEulerActualScalarGreenDivergence_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (massSquared : Real)
    (hField : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric field
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (hTest : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric test
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    globalEqualMassEulerActualScalarGreenDivergence period hPeriod metric
        field test massSquared hField hTest (patch.coordinateMap coordinate) =
      localActualScalarGreenCoordinateDivergence period hPeriod metric patch
        field test coordinate := by
  rw [globalEqualMassEulerActualScalarGreenDivergence]
  exact (localActualScalarGreenCoordinateDivergence_eq_zero_of_equalMassEuler
    period hPeriod metric patch field test massSquared coordinate
      (hField patch (canonicalTotalHolonomicAtlasCover_patch_mem
        period hPeriod patch) coordinate)
      (hTest patch (canonicalTotalHolonomicAtlasCover_patch_mem
        period hPeriod patch) coordinate)).symm

/-- Pullback of the explicit on-shell zero divergence scalar to the cut bulk. -/
def cutBulkGlobalEqualMassEulerActualScalarGreenDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (massSquared : Real)
    (hField : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric field
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (hTest : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric test
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (point : PositiveHemisphereCutBulk period hPeriod) : Real :=
  globalEqualMassEulerActualScalarGreenDivergence period hPeriod metric
    field test massSquared hField hTest (cutBulkToAmbient period hPeriod point)

/-- The same divergence-free law is realized above every point of the cut
bulk through the canonical ambient map. -/
theorem cutBulkPointwiseActualScalarGreenDivergenceFree_of_equalMassEuler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (massSquared : Real)
    (hField : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric field
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0)
    (hTest : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric test
      (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared 0) :
    ∀ point : PositiveHemisphereCutBulk period hPeriod,
      ∃ patch ∈ (canonicalTotalHolonomicAtlasCover period hPeriod).atlasPatches,
        ∃ coordinate : Vector4,
          patch.coordinateMap coordinate = cutBulkToAmbient period hPeriod point ∧
          localActualScalarGreenCoordinateDivergence period hPeriod metric patch
            field test coordinate = 0 := by
  intro point
  exact (canonicalTotalHolonomicAtlas_scalarGreenDivergenceFree_of_equalMassEuler
    period hPeriod metric field test massSquared hField hTest).2
      (cutBulkToAmbient period hPeriod point)

end
end P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarGreenConservation4D
end JanusFormal
