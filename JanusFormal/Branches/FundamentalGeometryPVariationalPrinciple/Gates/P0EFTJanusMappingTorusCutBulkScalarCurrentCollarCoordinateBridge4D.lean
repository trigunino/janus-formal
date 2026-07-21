import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentGlobalSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D

/-!
# Coordinate bridge for the global cut-bulk scalar current

On the canonical first-sheet positive collar, the global current is exactly
the cutoff density used by the previously proved one-dimensional FTC formula.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkScalarCurrentCollarCoordinateBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusEquatorialTubularOpenEmbedding4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D
open P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D
open P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Fundamental-domain parametrization of the positive cut-bulk collar. -/
def canonicalLatitudeCutBulkCollarLift
    (base : CanonicalLatitudeBase) (normal : CutCollarInterval) :
    PositiveHemisphereCutBulk period hPeriod :=
  cutCollarAttachment period hPeriod
    (canonicalLatitudeCutBoundaryFirstLift period hPeriod base, normal)

/-- Exact identification of the global current with its canonical collar
coordinate density. -/
theorem cutBulkScalarCurrent_canonicalCollarLift
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : CutCollarInterval) :
    cutBulkScalarCurrent period hPeriod field test
        (canonicalLatitudeCutBulkCollarLift period hPeriod base normal) =
      cutoffCollarScalarCurrentDensity period hPeriod field test base normal.1 := by
  let equator := equatorialTwoSphereHomeomorph.symm base.1
  have hNormalOpen : normal.1 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [normal.2.1, normal.2.2, Real.pi_gt_three]
  let tubularNormal : equatorialTubularNormalOpen := ⟨normal.1, hNormalOpen⟩
  have hBand : equatorialLatitude equator normal.1 ∈
      EquatorialSphericalBand := by
    change |Real.sin normal.1| < 1
    have hCos := Real.cos_pos_of_mem_Ioo hNormalOpen
    have hCosSq : 0 < Real.cos normal.1 ^ 2 := sq_pos_of_pos hCos
    rw [abs_lt]
    constructor <;> nlinarith [Real.sin_sq_add_cos_sq normal.1]
  let bandPoint : equatorialSphericalBandOpen :=
    ⟨equatorialLatitude equator normal.1, hBand⟩
  have hBandPoint :
      bandPoint = equatorialTubularSmoothMap (equator, tubularNormal) := by
    apply Subtype.ext
    rfl
  have hParameter :
      equatorialBandCanonicalParameter (bandPoint, base.2) =
        (base, normal.1) := by
    rw [equatorialBandCanonicalParameter, hBandPoint,
      equatorialTubularSmoothInverse_map]
    simp [equator, tubularNormal]
  rw [canonicalLatitudeCutBulkCollarLift,
    canonicalLatitudeCutBoundaryFirstLift]
  change equatorialBandScalarCurrentZeroExtension period hPeriod field test
    (equatorialLatitude equator normal.1, base.2) = _
  rw [equatorialBandScalarCurrentZeroExtension_eq_on_band period hPeriod
    field test _ hBand]
  change equatorialBandScalarCurrentDensity period hPeriod field test
      (bandPoint, base.2) = _
  rw [equatorialBandScalarCurrentDensity, hParameter,
    jointCutoffCollarScalarCurrentDensity_eq]

end
end P0EFTJanusMappingTorusCutBulkScalarCurrentCollarCoordinateBridge4D
end JanusFormal
