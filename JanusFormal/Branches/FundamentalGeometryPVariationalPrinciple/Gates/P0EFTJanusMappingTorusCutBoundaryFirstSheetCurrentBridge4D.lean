import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentHalfCollarStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D

/-! # First-sheet bridge from the cut boundary to latitude coordinates -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentHalfCollarStokes4D
open P0EFTJanusEquatorialTubularOpenEmbedding4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D
open P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D
open P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Fundamental-domain parametrization of the first sheet of the connected
orientation-double cut boundary. -/
def canonicalLatitudeCutBoundaryFirstLift
    (base : CanonicalLatitudeBase) : CutThroatBoundary period hPeriod :=
  mappingTorusMk (orientationDoubleData period hPeriod)
    ⟨equatorialTwoSphereHomeomorph.symm base.1, base.2⟩

theorem cutBoundaryScalarCurrent_firstLift
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    cutBoundaryScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base) =
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0 := by
  let equator := equatorialTwoSphereHomeomorph.symm base.1
  have hBand : equatorialSphereInclusion equator ∈ EquatorialSphericalBand := by
    change |(equator : R4Point) 0| < 1
    rw [equator.2.2]
    norm_num
  let bandPoint : equatorialSphericalBandOpen :=
    ⟨equatorialSphereInclusion equator, hBand⟩
  let zeroNormal : equatorialTubularNormalOpen :=
    ⟨0, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hBandPoint :
      bandPoint = equatorialTubularSmoothMap (equator, zeroNormal) := by
    apply Subtype.ext
    simp [bandPoint, equatorialTubularSmoothMap, zeroNormal,
      equatorialLatitude_zero]
  have hParameter :
      equatorialBandCanonicalParameter (bandPoint, base.2) = (base, 0) := by
    rw [equatorialBandCanonicalParameter, hBandPoint,
      equatorialTubularSmoothInverse_map]
    simp [equator, zeroNormal]
  rw [canonicalLatitudeCutBoundaryFirstLift, cutBoundaryScalarCurrent_mk,
    cutBoundaryScalarCurrentCover]
  rw [equatorialBandScalarCurrentZeroExtension_eq_on_band period hPeriod
    field test _ hBand]
  change equatorialBandScalarCurrentDensity period hPeriod field test
      (bandPoint, base.2) = _
  rw [equatorialBandScalarCurrentDensity, hParameter,
    jointCutoffCollarScalarCurrentDensity_eq,
    cutoffCollarScalarCurrentDensity_boundary_zero]

theorem measuredScalarGreenCurrent_zero_eq_firstSheetIntegral
    (field test : SmoothQuotientField period hPeriod Real) :
    canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test 0 =
      ∫ base, cutBoundaryScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)
        ∂canonicalLatitudeBaseMeasure period := by
  unfold canonicalLatitudeMeasuredScalarGreenCurrent
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    (cutBoundaryScalarCurrent_firstLift period hPeriod field test base).symm

/-- The half-collar divergence is the negative first-sheet cut-boundary
current integral. -/
theorem productHalfCollarIntegral_eq_neg_firstSheetBoundaryCurrent
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real) :
    ∫ base, (∫ normal in (0 : Real)..1,
        cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
          field test base normal) ∂canonicalLatitudeBaseMeasure period =
      -∫ base, cutBoundaryScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)
        ∂canonicalLatitudeBaseMeasure period := by
  rw [productHalfCollarIntegral_cutoffCurrentDivergence_eq_neg_throatFlux,
    measuredScalarGreenCurrent_zero_eq_firstSheetIntegral]

end
end P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
end JanusFormal
