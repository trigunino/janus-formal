import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarOverlapNormalSmooth4D

/-!
# Smooth boundary projection of the quotient collar overlap
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarOverlapBoundarySmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D

local instance equatorialTubularNormalOpenLocallyCompactSpace :
    LocallyCompactSpace equatorialTubularNormalOpen :=
  equatorialTubularNormalOpen.2.locallyCompactSpace

local instance positiveUnitTubularParameterOpenLocallyCompactSpace :
    LocallyCompactSpace positiveUnitTubularParameterOpen :=
  positiveUnitTubularParameterOpen.2.locallyCompactSpace

variable (period : Real) (hPeriod : period ≠ 0)

def smoothCutCollarOverlapBoundary :
    SmoothCutCollarOverlap period hPeriod →
      CutThroatBoundary period hPeriod :=
  identityMappingTorusMap CollarOverlapFiberModel
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) (𝓡 2)
    (fun parameter : positiveUnitTubularParameterOpen => parameter.1.1)

theorem smoothCutCollarOverlapBoundary_contMDiff :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    letI := cutThroatBoundaryChartedSpace period hPeriod
    ContMDiff (identityCoverModelWithCorners CollarOverlapFiberModel)
      throatCoverModelWithCorners ∞
      (smoothCutCollarOverlapBoundary period hPeriod) := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  letI := cutThroatBoundaryChartedSpace period hPeriod
  have hFiber : ContMDiff CollarOverlapFiberModel (𝓡 2) ∞
      (fun parameter : positiveUnitTubularParameterOpen => parameter.1.1) :=
    contMDiff_fst.comp contMDiff_subtype_val
  exact identityMappingTorusMap_contMDiff CollarOverlapFiberModel
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) (𝓡 2)
    (fun parameter : positiveUnitTubularParameterOpen => parameter.1.1) hFiber

end
end P0EFTJanusMappingTorusCutBulkCollarOverlapBoundarySmooth4D
end JanusFormal
