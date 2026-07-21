import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarCapCoverExactOverlap4D

/-!
# Smooth open embedding of the cap overlap model

The strict latitude-band mapping torus embeds smoothly and openly in the full
smooth cap mapping torus.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCapOverlapSmoothEmbedding4D

set_option autoImplicit false
noncomputable section

open Topology
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverExactOverlap4D
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D

local instance equatorialSphericalBandOpenLocallyCompactSpace :
    LocallyCompactSpace equatorialSphericalBandOpen :=
  equatorialSphericalBandOpen.2.locallyCompactSpace

local instance positiveUnitLatitudeBandOpenLocallyCompactSpace :
    LocallyCompactSpace positiveUnitLatitudeBandOpen :=
  positiveUnitLatitudeBandOpen.2.locallyCompactSpace

local instance positiveHemisphereInteriorOpenLocallyCompactSpace :
    LocallyCompactSpace positiveHemisphereInteriorOpen :=
  positiveHemisphereInteriorOpen.2.locallyCompactSpace

variable (period : Real) (hPeriod : period ≠ 0)

/-- Inclusion of the exact strict latitude band in the positive hemisphere. -/
def positiveUnitLatitudeBandToCapFiber
    (point : positiveUnitLatitudeBandOpen) :
    positiveHemisphereInteriorOpen :=
  ⟨point.1.1,
    (mem_positiveUnitLatitudeBandOpen_iff point.1).1 point.2 |>.1⟩

theorem positiveUnitLatitudeBandToCapFiber_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      positiveUnitLatitudeBandToCapFiber := by
  rw [← ContMDiff.subtypeVal_comp_iff positiveHemisphereInteriorOpen]
  have hFirst : ContMDiff (𝓡 3) (𝓡 3) ∞
      (Subtype.val : positiveUnitLatitudeBandOpen →
        equatorialSphericalBandOpen) := contMDiff_subtype_val
  have hSecond : ContMDiff (𝓡 3) (𝓡 3) ∞
      (Subtype.val : equatorialSphericalBandOpen → UnitThreeSphere) :=
    contMDiff_subtype_val
  exact (hSecond.comp hFirst).congr fun _ => rfl

theorem positiveUnitLatitudeBandToCapFiber_isOpenEmbedding :
    IsOpenEmbedding positiveUnitLatitudeBandToCapFiber := by
  have hAmbient : IsOpenEmbedding
      (fun point : positiveUnitLatitudeBandOpen => point.1.1) :=
    equatorialSphericalBandOpen.2.isOpenEmbedding_subtypeVal.comp
      positiveUnitLatitudeBandOpen.2.isOpenEmbedding_subtypeVal
  apply IsOpenEmbedding.of_comp _
    positiveHemisphereInteriorOpen.2.isOpenEmbedding_subtypeVal
  convert hAmbient using 1
  funext point
  rfl

/-- Natural inclusion of the strict-band mapping torus in the smooth cap. -/
def smoothCutCapOverlapToSmoothCap :
    SmoothCutCapOverlap period hPeriod →
      SmoothCutBulkOpenCap period hPeriod :=
  identityMappingTorusMap (𝓡 3) (doubledPeriod period)
    (doubledPeriod_ne_zero period hPeriod) (𝓡 3)
    positiveUnitLatitudeBandToCapFiber

theorem smoothCutCapOverlapToSmoothCap_isOpenEmbedding :
    IsOpenEmbedding (smoothCutCapOverlapToSmoothCap period hPeriod) := by
  exact identityMappingTorusMap_isOpenEmbedding (𝓡 3)
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) (𝓡 3)
    positiveUnitLatitudeBandToCapFiber
    positiveUnitLatitudeBandToCapFiber_isOpenEmbedding

theorem smoothCutCapOverlapToSmoothCap_contMDiff :
    letI : ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
        (SmoothCutCapOverlap period hPeriod) :=
      smoothCutCapOverlapChartedSpace period hPeriod
    letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
      cutBulkOpenCapQuotientChartedSpace period hPeriod
    ContMDiff (identityCoverModelWithCorners (𝓡 3))
      coverModelWithCorners ∞
      (smoothCutCapOverlapToSmoothCap period hPeriod) := by
  letI : ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
      (SmoothCutCapOverlap period hPeriod) :=
    smoothCutCapOverlapChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  exact identityMappingTorusMap_contMDiff (𝓡 3)
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) (𝓡 3)
    positiveUnitLatitudeBandToCapFiber
    positiveUnitLatitudeBandToCapFiber_contMDiff

end
end P0EFTJanusMappingTorusCutBulkCapOverlapSmoothEmbedding4D
end JanusFormal
