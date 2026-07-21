import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCapOverlapSmoothEmbedding4D

/-!
# Exact intrinsic range of the smooth cap overlap

The strict-band mapping torus maps exactly to the intrinsic cut-bulk overlap
`0 < latitude < sin 1`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCapOverlapExactIntrinsicRange4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
open P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D
open P0EFTJanusEquatorialTubularOpenEmbedding4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverExactOverlap4D
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
open P0EFTJanusMappingTorusCutBulkCapOverlapSmoothEmbedding4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The cap-overlap model mapped into the intrinsic cut bulk. -/
def smoothCutCapOverlapToCutBulk :
    SmoothCutCapOverlap period hPeriod →
      PositiveHemisphereCutBulk period hPeriod :=
  smoothCutBulkOpenCapToCutBulk period hPeriod ∘
    smoothCutCapOverlapToSmoothCap period hPeriod

theorem smoothCutCapOverlapToCutBulk_isOpenEmbedding :
    IsOpenEmbedding (smoothCutCapOverlapToCutBulk period hPeriod) := by
  exact (smoothCutBulkOpenCapToCutBulk_isOpenEmbedding period hPeriod).comp
    (smoothCutCapOverlapToSmoothCap_isOpenEmbedding period hPeriod)

@[simp] theorem cutBulkLatitudeCoordinate_smoothCutCapOverlapToCutBulk_mk
    (representative : MappingTorusCover
      (identityMappingTorusData (X := positiveUnitLatitudeBandOpen) (𝓡 3)
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))) :
    cutBulkLatitudeCoordinate period hPeriod
        (smoothCutCapOverlapToCutBulk period hPeriod
          (mappingTorusMk _ representative)) =
      representative.fiber.1.1.1 0 := by
  rfl

/-- Exact intrinsic range of the smooth cap-overlap inclusion. -/
theorem range_smoothCutCapOverlapToCutBulk :
    Set.range (smoothCutCapOverlapToCutBulk period hPeriod) =
      (cutBulkLatitudeCoordinate period hPeriod) ⁻¹'
        Ioo 0 (Real.sin 1) := by
  ext bulk
  constructor
  · rintro ⟨overlap, rfl⟩
    refine Quotient.inductionOn overlap ?_
    intro representative
    change representative.fiber.1.1.1 0 ∈ Ioo 0 (Real.sin 1)
    exact (mem_positiveUnitLatitudeBandOpen_iff representative.fiber.1).1
      representative.fiber.2
  · intro hBulk
    refine Quotient.inductionOn bulk ?_ hBulk
    intro representative hCoordinate
    change representative.fiber.1.1 0 ∈ Ioo 0 (Real.sin 1) at hCoordinate
    let spherePoint : UnitThreeSphere := representative.fiber.1
    have hBand : spherePoint ∈ EquatorialSphericalBand := by
      change |spherePoint.1 0| < 1
      rw [abs_of_pos hCoordinate.1]
      exact hCoordinate.2.trans_le (Real.sin_le_one 1)
    let bandPoint : equatorialSphericalBandOpen := ⟨spherePoint, hBand⟩
    have hPositiveBand : bandPoint ∈ positiveUnitLatitudeBandOpen :=
      (mem_positiveUnitLatitudeBandOpen_iff bandPoint).2 hCoordinate
    let overlapRepresentative : MappingTorusCover
        (identityMappingTorusData (X := positiveUnitLatitudeBandOpen) (𝓡 3)
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) :=
      ⟨⟨bandPoint, hPositiveBand⟩, representative.time⟩
    refine ⟨mappingTorusMk _ overlapRepresentative, ?_⟩
    apply congrArg (mappingTorusMk (cutBulkData period hPeriod))
    rfl

end
end P0EFTJanusMappingTorusCutBulkCapOverlapExactIntrinsicRange4D
end JanusFormal
