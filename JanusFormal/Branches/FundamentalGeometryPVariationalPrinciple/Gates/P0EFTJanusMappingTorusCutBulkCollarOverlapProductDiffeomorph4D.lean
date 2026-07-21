import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIdentityMappingTorusProductDiffeomorph4D

/-!
# Product diffeomorphism for the strict collar overlap
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarOverlapProductDiffeomorph4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
open P0EFTJanusMappingTorusCutBulkPositiveUnitTubularProductDiffeomorph4D
open P0EFTJanusIdentityMappingTorusProductDiffeomorph4D

local instance equatorialTubularNormalOpenLocallyCompactSpace :
    LocallyCompactSpace equatorialTubularNormalOpen :=
  equatorialTubularNormalOpen.2.locallyCompactSpace

local instance positiveUnitTubularParameterOpenLocallyCompactSpace :
    LocallyCompactSpace positiveUnitTubularParameterOpen :=
  positiveUnitTubularParameterOpen.2.locallyCompactSpace

local instance positiveUnitNormalOpenLocallyCompactSpace :
    LocallyCompactSpace positiveUnitNormalOpen :=
  positiveUnitNormalOpen.2.locallyCompactSpace

variable (period : Real) (hPeriod : period ≠ 0)

abbrev SmoothCutCollarProductTorus :=
  MappingTorus (identityMappingTorusData
    (X := EquatorialTwoSphere × positiveUnitNormalOpen)
    CollarOverlapFiberModel (doubledPeriod period)
    (doubledPeriod_ne_zero period hPeriod))

def smoothCutCollarOverlapFiberProductDiffeomorph :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    letI := identityMappingTorusQuotientChartedSpace
      (X := EquatorialTwoSphere × positiveUnitNormalOpen)
      CollarOverlapFiberModel (doubledPeriod period)
      (doubledPeriod_ne_zero period hPeriod)
    SmoothCutCollarOverlap period hPeriod ≃ₘ^∞⟮
      identityCoverModelWithCorners CollarOverlapFiberModel,
      identityCoverModelWithCorners CollarOverlapFiberModel⟯
        SmoothCutCollarProductTorus period hPeriod := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  letI := identityMappingTorusQuotientChartedSpace
    (X := EquatorialTwoSphere × positiveUnitNormalOpen)
    CollarOverlapFiberModel (doubledPeriod period)
    (doubledPeriod_ne_zero period hPeriod)
  exact identityMappingTorusDiffeomorph CollarOverlapFiberModel
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    CollarOverlapFiberModel positiveUnitTubularProductDiffeomorph

def smoothCutCollarProductTorusDiffeomorph :
    letI := identityMappingTorusQuotientChartedSpace
      (X := EquatorialTwoSphere × positiveUnitNormalOpen)
      CollarOverlapFiberModel (doubledPeriod period)
      (doubledPeriod_ne_zero period hPeriod)
    letI := cutThroatBoundaryChartedSpace period hPeriod
    SmoothCutCollarProductTorus period hPeriod ≃ₘ^∞⟮
      identityCoverModelWithCorners CollarOverlapFiberModel,
      throatCoverModelWithCorners.prod 𝓘(Real, Real)⟯
        (CutThroatBoundary period hPeriod × positiveUnitNormalOpen) := by
  letI := identityMappingTorusQuotientChartedSpace
    (X := EquatorialTwoSphere × positiveUnitNormalOpen)
    CollarOverlapFiberModel (doubledPeriod period)
    (doubledPeriod_ne_zero period hPeriod)
  letI := cutThroatBoundaryChartedSpace period hPeriod
  exact identityMappingTorusProductDiffeomorph (𝓡 2) 𝓘(Real, Real)
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

def smoothCutCollarOverlapProductDiffeomorph :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    letI := cutThroatBoundaryChartedSpace period hPeriod
    SmoothCutCollarOverlap period hPeriod ≃ₘ^∞⟮
      identityCoverModelWithCorners CollarOverlapFiberModel,
      throatCoverModelWithCorners.prod 𝓘(Real, Real)⟯
        (CutThroatBoundary period hPeriod × positiveUnitNormalOpen) := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  letI := identityMappingTorusQuotientChartedSpace
    (X := EquatorialTwoSphere × positiveUnitNormalOpen)
    CollarOverlapFiberModel (doubledPeriod period)
    (doubledPeriod_ne_zero period hPeriod)
  letI := cutThroatBoundaryChartedSpace period hPeriod
  exact (smoothCutCollarOverlapFiberProductDiffeomorph period hPeriod).trans
    (smoothCutCollarProductTorusDiffeomorph period hPeriod)

end
end P0EFTJanusMappingTorusCutBulkCollarOverlapProductDiffeomorph4D
end JanusFormal
