import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIdentityMappingTorusSmoothFunctor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D

/-!
# Analytic collar--cap compatibility on the quotient overlap

The cover-level tubular diffeomorphism on `0 < normal < 1` commutes with the
identity decks and therefore descends to an analytic diffeomorphism between
the two doubled-period mapping-torus overlap models.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D

local instance equatorialTubularNormalOpenLocallyCompactSpace :
    LocallyCompactSpace equatorialTubularNormalOpen :=
  equatorialTubularNormalOpen.2.locallyCompactSpace

local instance equatorialSphericalBandOpenLocallyCompactSpace :
    LocallyCompactSpace equatorialSphericalBandOpen :=
  equatorialSphericalBandOpen.2.locallyCompactSpace

local instance positiveUnitTubularParameterOpenLocallyCompactSpace :
    LocallyCompactSpace positiveUnitTubularParameterOpen :=
  positiveUnitTubularParameterOpen.2.locallyCompactSpace

local instance positiveUnitLatitudeBandOpenLocallyCompactSpace :
    LocallyCompactSpace positiveUnitLatitudeBandOpen :=
  positiveUnitLatitudeBandOpen.2.locallyCompactSpace

variable (period : Real) (hPeriod : period ≠ 0)

abbrev CollarOverlapFiberModel :=
  (𝓡 2).prod 𝓘(Real, Real)

/-- Doubled-period smooth mapping torus of the strict collar parameters. -/
abbrev SmoothCutCollarOverlap :=
  MappingTorus (identityMappingTorusData
    (X := positiveUnitTubularParameterOpen) CollarOverlapFiberModel
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))

/-- Doubled-period smooth mapping torus of the strict latitude-band image. -/
abbrev SmoothCutCapOverlap :=
  MappingTorus (identityMappingTorusData
    (X := positiveUnitLatitudeBandOpen) (𝓡 3)
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))

@[implicit_reducible] def smoothCutCollarOverlapChartedSpace :
    ChartedSpace (IdentityCoverModel
      (ModelProd (EuclideanSpace Real (Fin 2)) Real))
      (SmoothCutCollarOverlap period hPeriod) :=
  identityMappingTorusQuotientChartedSpace CollarOverlapFiberModel
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

@[implicit_reducible] def smoothCutCapOverlapChartedSpace :
    ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
      (SmoothCutCapOverlap period hPeriod) :=
  identityMappingTorusQuotientChartedSpace (𝓡 3)
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

theorem smoothCutCollarOverlap_isManifold :
    letI : ChartedSpace (IdentityCoverModel
        (ModelProd (EuclideanSpace Real (Fin 2)) Real))
        (SmoothCutCollarOverlap period hPeriod) :=
      smoothCutCollarOverlapChartedSpace period hPeriod
    IsManifold (identityCoverModelWithCorners CollarOverlapFiberModel) ∞
      (SmoothCutCollarOverlap period hPeriod) := by
  letI : ChartedSpace (IdentityCoverModel
      (ModelProd (EuclideanSpace Real (Fin 2)) Real))
      (SmoothCutCollarOverlap period hPeriod) :=
    smoothCutCollarOverlapChartedSpace period hPeriod
  exact identityMappingTorus_isManifold CollarOverlapFiberModel
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

theorem smoothCutCapOverlap_isManifold :
    letI : ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
        (SmoothCutCapOverlap period hPeriod) :=
      smoothCutCapOverlapChartedSpace period hPeriod
    IsManifold (identityCoverModelWithCorners (𝓡 3)) ∞
      (SmoothCutCapOverlap period hPeriod) := by
  letI : ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
      (SmoothCutCapOverlap period hPeriod) :=
    smoothCutCapOverlapChartedSpace period hPeriod
  exact identityMappingTorus_isManifold (𝓡 3)
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

/-- Smooth compatibility diffeomorphism after quotienting by the doubled
time deck action. -/
def smoothCutCollarCapOverlapDiffeomorph :
    letI : ChartedSpace (IdentityCoverModel
        (ModelProd (EuclideanSpace Real (Fin 2)) Real))
        (SmoothCutCollarOverlap period hPeriod) :=
      smoothCutCollarOverlapChartedSpace period hPeriod
    letI : ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
        (SmoothCutCapOverlap period hPeriod) :=
      smoothCutCapOverlapChartedSpace period hPeriod
    SmoothCutCollarOverlap period hPeriod ≃ₘ^∞⟮
      identityCoverModelWithCorners CollarOverlapFiberModel,
      identityCoverModelWithCorners (𝓡 3)⟯
        SmoothCutCapOverlap period hPeriod := by
  letI : ChartedSpace (IdentityCoverModel
      (ModelProd (EuclideanSpace Real (Fin 2)) Real))
      (SmoothCutCollarOverlap period hPeriod) :=
    smoothCutCollarOverlapChartedSpace period hPeriod
  letI : ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
      (SmoothCutCapOverlap period hPeriod) :=
    smoothCutCapOverlapChartedSpace period hPeriod
  exact identityMappingTorusDiffeomorph CollarOverlapFiberModel
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) (𝓡 3)
    positiveUnitTubularDiffeomorph

end
end P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
end JanusFormal
