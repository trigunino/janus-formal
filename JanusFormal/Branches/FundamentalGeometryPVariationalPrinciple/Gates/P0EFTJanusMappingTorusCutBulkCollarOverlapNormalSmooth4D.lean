import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarOverlapOpenCollarIdentification4D

/-!
# Smooth normal coordinate on the quotient collar overlap
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarOverlapNormalSmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D

local instance equatorialTubularNormalOpenLocallyCompactSpace :
    LocallyCompactSpace equatorialTubularNormalOpen :=
  equatorialTubularNormalOpen.2.locallyCompactSpace

local instance positiveUnitTubularParameterOpenLocallyCompactSpace :
    LocallyCompactSpace positiveUnitTubularParameterOpen :=
  positiveUnitTubularParameterOpen.2.locallyCompactSpace

variable (period : Real) (hPeriod : period ≠ 0)

def smoothCutCollarOverlapNormalCover
    (point : MappingTorusCover
      (identityMappingTorusData (X := positiveUnitTubularParameterOpen)
        CollarOverlapFiberModel (doubledPeriod period)
        (doubledPeriod_ne_zero period hPeriod))) : Real :=
  point.fiber.1.2.1

theorem smoothCutCollarOverlapNormalCover_invariant
    (winding : Int)
    (point : MappingTorusCover
      (identityMappingTorusData (X := positiveUnitTubularParameterOpen)
        CollarOverlapFiberModel (doubledPeriod period)
        (doubledPeriod_ne_zero period hPeriod))) :
    smoothCutCollarOverlapNormalCover period hPeriod (winding +ᵥ point) =
      smoothCutCollarOverlapNormalCover period hPeriod point := by
  change (((Homeomorph.refl positiveUnitTubularParameterOpen) ^ winding)
    point.fiber).1.2.1 = point.fiber.1.2.1
  rw [show ((Homeomorph.refl positiveUnitTubularParameterOpen) ^ winding)
      point.fiber =
    ((Homeomorph.refl positiveUnitTubularParameterOpen) ^ winding).toEquiv
      point.fiber from rfl,
    homeomorph_toEquiv_zpow,
    show (Homeomorph.refl positiveUnitTubularParameterOpen).toEquiv = 1 from rfl,
    one_zpow]
  rfl

def smoothCutCollarOverlapNormal :
    SmoothCutCollarOverlap period hPeriod → Real :=
  mappingTorusInvariantMap _
    (smoothCutCollarOverlapNormalCover period hPeriod)
    (smoothCutCollarOverlapNormalCover_invariant period hPeriod)

@[simp] theorem smoothCutCollarOverlapNormal_mk
    (point : MappingTorusCover
      (identityMappingTorusData (X := positiveUnitTubularParameterOpen)
        CollarOverlapFiberModel (doubledPeriod period)
        (doubledPeriod_ne_zero period hPeriod))) :
    smoothCutCollarOverlapNormal period hPeriod (mappingTorusMk _ point) =
      point.fiber.1.2.1 :=
  rfl

theorem smoothCutCollarOverlapNormal_contMDiff :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    ContMDiff (identityCoverModelWithCorners CollarOverlapFiberModel)
      𝓘(Real, Real) ∞ (smoothCutCollarOverlapNormal period hPeriod) := by
  letI := identityMappingTorusCoverChartedSpace
    (X := positiveUnitTubularParameterOpen) CollarOverlapFiberModel
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff
    (identityCoverModelWithCorners CollarOverlapFiberModel) ∞
    (coverHomeomorphProd
      (identityMappingTorusData (X := positiveUnitTubularParameterOpen)
        CollarOverlapFiberModel (doubledPeriod period)
        (doubledPeriod_ne_zero period hPeriod)))
  have hFiber : ContMDiff CollarOverlapFiberModel 𝓘(Real, Real) ∞
      (fun point : positiveUnitTubularParameterOpen => point.1.2.1) := by
    exact contMDiff_subtype_val.comp
      (contMDiff_snd.comp contMDiff_subtype_val)
  have hCover : ContMDiff
      (identityCoverModelWithCorners CollarOverlapFiberModel) 𝓘(Real, Real) ∞
      (smoothCutCollarOverlapNormalCover period hPeriod) :=
    hFiber.comp (contMDiff_fst.comp hTo)
  exact mappingTorusInvariantMap_contMDiff
    (sourceData := identityMappingTorusData
      (X := positiveUnitTubularParameterOpen) CollarOverlapFiberModel
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (sourceModel := identityCoverModelWithCorners CollarOverlapFiberModel)
    (n := ∞) (targetModel' := 𝓘(Real, Real))
    (invariantMap := smoothCutCollarOverlapNormalCover period hPeriod)
    (hInvariant := smoothCutCollarOverlapNormalCover_invariant period hPeriod)
    (hSourceProjection := identityMappingTorus_projection_isLocalDiffeomorph
      (X := positiveUnitTubularParameterOpen) CollarOverlapFiberModel
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (hInvariantMap := hCover)

end
end P0EFTJanusMappingTorusCutBulkCollarOverlapNormalSmooth4D
end JanusFormal
