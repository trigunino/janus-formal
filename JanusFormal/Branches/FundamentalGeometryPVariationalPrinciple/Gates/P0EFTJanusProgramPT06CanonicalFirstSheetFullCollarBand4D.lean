import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateGerm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D

/-!
# Canonical first-sheet full collar in the tubular band

The canonical first-sheet screen parametrization extends through every normal
in the finite collar `[0,1]`.  Its tubular-band representative agrees exactly
with the true cut-bulk collar and reads as the explicit warped null collar.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarBand4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutCollarTubularNormalLift4D
open P0EFTJanusMappingTorusCutCollarTubularSpacetimeDerivativeIsomorphism4D
open P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutCollarCoverToAmbientDerivativeIsomorphism4D
open P0EFTJanusMappingTorusCutBulkFiniteCollarAmbientDerivativeIsomorphism4D
open P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusEquatorialBandScalarCurrentJointSmooth4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusProgramPT06AmbientNullFluxPullback4D
open P0EFTJanusProgramPT06ExplicitWarpedNullLinearCollar4D
open P0EFTJanusProgramPT06WarpedNullClosedHalfCollar4D
open P0EFTJanusProgramPT06CanonicalFirstSheetBoundarySmooth4D
open P0EFTJanusProgramPT06CanonicalFirstSheetAdaptedCoordinateGerm4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLatitudeSphereFinrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

private abbrev BoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

/-- Tubular-band representative of the whole canonical first-sheet finite
collar. -/
def programPT06CanonicalFirstSheetFullCollarBandPoint
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (normal : CutCollarInterval) : equatorialSphericalBandOpen × Real :=
  cutCollarTubularSpacetimeMap
    ((equatorialTwoSphereHomeomorph.symm
        (standardEquatorialStereographicInverse pole source.2), source.1),
      normal)

@[simp] theorem programPT06CanonicalFirstSheetFullCollarBandPoint_eq
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (normal : CutCollarInterval) :
    programPT06CanonicalFirstSheetFullCollarBandPoint pole source normal =
      (equatorialTubularSmoothMap
          (equatorialTwoSphereHomeomorph.symm
              (standardEquatorialStereographicInverse pole source.2),
            cutCollarTubularNormalLift normal),
        source.1) :=
  rfl

/-- Every point of the finite collar stays in the selected stereographic
tubular coordinate domain. -/
theorem programPT06CanonicalFirstSheetFullCollarBandPoint_mem_coordinateDomain
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (normal : CutCollarInterval) :
    programPT06CanonicalFirstSheetFullCollarBandPoint pole source normal ∈
      programPT06WarpedNullBandCoordinateDomain pole := by
  rw [programPT06CanonicalFirstSheetFullCollarBandPoint_eq]
  change (equatorialBandCanonicalParameter
    (equatorialTubularSmoothMap
        (equatorialTwoSphereHomeomorph.symm
            (standardEquatorialStereographicInverse pole source.2),
          cutCollarTubularNormalLift normal),
      source.1)).1.1 ∈ (stereographic' 2 pole).source
  unfold equatorialBandCanonicalParameter
  rw [equatorialTubularSmoothInverse_map]
  simp only [Homeomorph.apply_symm_apply]
  change (stereographic' 2 pole).symm source.2 ∈
    (stereographic' 2 pole).source
  exact (stereographic' 2 pole).map_target (by simp)

/-- The tubular representative and the true finite cut-bulk collar define the
same ambient point. -/
theorem programPT06CanonicalFirstSheetFullCollarBandPoint_toAmbient
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (normal : CutCollarInterval) :
    tubularBandSpacetimeToAmbient period hPeriod
        (programPT06CanonicalFirstSheetFullCollarBandPoint pole source normal) =
      cutBulkFiniteCollarToAmbient period hPeriod
        (programPT06CanonicalFirstSheetBoundaryMap
          period hPeriod pole source, normal) := by
  rw [programPT06CanonicalFirstSheetBoundaryMap_eq_mk]
  let representative : BoundaryCover period hPeriod :=
    ⟨equatorialTwoSphereHomeomorph.symm
        (standardEquatorialStereographicInverse pole source.2), source.1⟩
  change cutCollarCoverToAmbient period hPeriod (representative, normal) =
    cutBulkFiniteCollarToAmbient period hPeriod
      (mappingTorusMk (orientationDoubleData period hPeriod) representative,
        normal)
  exact cutCollarCoverToAmbient_eq_existing period hPeriod
    (representative, normal)

/-- The adapted band coordinate is exactly the explicit warped closed
half-collar coordinate for every normal in `[0,1]`. -/
@[simp] theorem programPT06WarpedNullBandCoordinate_fullCollar
    (pole : StandardEquatorialTwoSphere)
    (source : ProgramPT06NullFaceSource3)
    (normal : CutCollarInterval) :
    programPT06WarpedNullBandCoordinate pole
        (programPT06CanonicalFirstSheetFullCollarBandPoint pole source normal) =
      programPT06WarpedNullClosedHalfCollarEmbedding (source, normal) := by
  rw [programPT06CanonicalFirstSheetFullCollarBandPoint_eq]
  unfold programPT06WarpedNullBandCoordinate equatorialBandCanonicalParameter
  rw [equatorialTubularSmoothInverse_map]
  simp [standardEquatorialStereographicInverse,
    programPT06WarpedNullClosedHalfCollarEmbedding,
    programPT06WarpedNullClosedHalfCollarCoordinate,
    cutCollarTubularNormalLift]

end
end P0EFTJanusProgramPT06CanonicalFirstSheetFullCollarBand4D
end JanusFormal
