import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCapOverlapLocalDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D

/-!
# Diffeomorphism onto the intrinsic cap overlap
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkIntrinsicCapOverlapDiffeomorph4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
open P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
open P0EFTJanusMappingTorusCutBulkCapOverlapSmoothEmbedding4D
open P0EFTJanusMappingTorusCutBulkCapOverlapLocalDiffeomorph4D

variable (period : Real) (hPeriod : period ≠ 0)

private instance smoothCutCapOverlapNonempty :
    Nonempty (SmoothCutCapOverlap period hPeriod) := inferInstance

/-- Natural cap-overlap inclusion into the intrinsic open cap. -/
def smoothCutCapOverlapToIntrinsicCap :
    SmoothCutCapOverlap period hPeriod → CutBulkOpenCap period hPeriod :=
  smoothCutBulkOpenCapHomeomorph period hPeriod ∘
    smoothCutCapOverlapToSmoothCap period hPeriod

theorem smoothCutCapOverlapToIntrinsicCap_isOpenEmbedding :
    IsOpenEmbedding (smoothCutCapOverlapToIntrinsicCap period hPeriod) :=
  (smoothCutBulkOpenCapHomeomorph period hPeriod).isOpenEmbedding.comp
    (smoothCutCapOverlapToSmoothCap_isOpenEmbedding period hPeriod)

/-- The strict intrinsic cap overlap as an open subtype. -/
def intrinsicCapOverlapOpen :
    TopologicalSpace.Opens (CutBulkOpenCap period hPeriod) :=
  ⟨Set.range (smoothCutCapOverlapToIntrinsicCap period hPeriod),
    (smoothCutCapOverlapToIntrinsicCap_isOpenEmbedding period hPeriod)
      |>.isOpen_range⟩

def smoothCutCapOverlapToIntrinsicCapOpen
    (point : SmoothCutCapOverlap period hPeriod) :
    intrinsicCapOverlapOpen period hPeriod :=
  ⟨smoothCutCapOverlapToIntrinsicCap period hPeriod point, ⟨point, rfl⟩⟩

def intrinsicCapOpenToSmoothCutCapOverlap
    (point : intrinsicCapOverlapOpen period hPeriod) :
    SmoothCutCapOverlap period hPeriod :=
  ((smoothCutCapOverlapToSmoothCap_isOpenEmbedding period hPeriod)
    |>.toOpenPartialHomeomorph
      (smoothCutCapOverlapToSmoothCap period hPeriod)).symm
    ((smoothCutBulkOpenCapHomeomorph period hPeriod).symm point.1)

theorem smoothCutCapOverlapToIntrinsicCapOpen_leftInverse :
    Function.LeftInverse
      (intrinsicCapOpenToSmoothCutCapOverlap period hPeriod)
      (smoothCutCapOverlapToIntrinsicCapOpen period hPeriod) := by
  intro point
  apply (smoothCutCapOverlapToSmoothCap_isOpenEmbedding period hPeriod).injective
  change smoothCutCapOverlapToSmoothCap period hPeriod
      (((smoothCutCapOverlapToSmoothCap_isOpenEmbedding period hPeriod)
        |>.toOpenPartialHomeomorph
          (smoothCutCapOverlapToSmoothCap period hPeriod)).symm
        ((smoothCutBulkOpenCapHomeomorph period hPeriod).symm
          (smoothCutBulkOpenCapHomeomorph period hPeriod
            (smoothCutCapOverlapToSmoothCap period hPeriod point)))) =
    smoothCutCapOverlapToSmoothCap period hPeriod point
  rw [(smoothCutBulkOpenCapHomeomorph period hPeriod).symm_apply_apply]
  exact (smoothCutCapOverlapToSmoothCap_isOpenEmbedding period hPeriod)
    |>.toOpenPartialHomeomorph_right_inv
      (smoothCutCapOverlapToSmoothCap period hPeriod) ⟨point, rfl⟩

theorem smoothCutCapOverlapToIntrinsicCapOpen_rightInverse :
    Function.RightInverse
      (intrinsicCapOpenToSmoothCutCapOverlap period hPeriod)
      (smoothCutCapOverlapToIntrinsicCapOpen period hPeriod) := by
  intro point
  apply Subtype.ext
  rcases point.2 with ⟨source, hSource⟩
  change smoothCutCapOverlapToIntrinsicCap period hPeriod source = point.1 at hSource
  change smoothCutCapOverlapToIntrinsicCap period hPeriod
      (intrinsicCapOpenToSmoothCutCapOverlap period hPeriod point) = point.1
  have hCap : (smoothCutBulkOpenCapHomeomorph period hPeriod).symm point.1 =
      smoothCutCapOverlapToSmoothCap period hPeriod source := by
    apply (smoothCutBulkOpenCapHomeomorph period hPeriod).injective
    rw [(smoothCutBulkOpenCapHomeomorph period hPeriod).apply_symm_apply]
    exact hSource.symm
  simp only [smoothCutCapOverlapToIntrinsicCap,
    intrinsicCapOpenToSmoothCutCapOverlap, Function.comp_apply]
  rw [hCap]
  rw [(smoothCutCapOverlapToSmoothCap_isOpenEmbedding period hPeriod)
    |>.toOpenPartialHomeomorph_right_inv
      (smoothCutCapOverlapToSmoothCap period hPeriod) ⟨source, rfl⟩]
  exact hSource

theorem smoothCutCapOverlapToIntrinsicCapOpen_contMDiff :
    letI := smoothCutCapOverlapChartedSpace period hPeriod
    letI := cutBulkOpenCapQuotientChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    ContMDiff (identityCoverModelWithCorners (𝓡 3))
      coverModelWithCorners ∞
      (smoothCutCapOverlapToIntrinsicCapOpen period hPeriod) := by
  letI := smoothCutCapOverlapChartedSpace period hPeriod
  letI := cutBulkOpenCapQuotientChartedSpace period hPeriod
  letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
  rw [← ContMDiff.subtypeVal_comp_iff (intrinsicCapOverlapOpen period hPeriod)]
  exact ((smoothCapHomeomorph_contMDiff period hPeriod).of_le le_top).comp
    (smoothCutCapOverlapToSmoothCap_contMDiff period hPeriod)

theorem intrinsicCapOpenToSmoothCutCapOverlap_contMDiff :
    letI := smoothCutCapOverlapChartedSpace period hPeriod
    letI := cutBulkOpenCapQuotientChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    ContMDiff coverModelWithCorners
      (identityCoverModelWithCorners (𝓡 3)) ∞
      (intrinsicCapOpenToSmoothCutCapOverlap period hPeriod) := by
  letI := smoothCutCapOverlapChartedSpace period hPeriod
  letI := cutBulkOpenCapQuotientChartedSpace period hPeriod
  letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
  have hIntoCap : ContMDiff coverModelWithCorners coverModelWithCorners ∞
      (fun point : intrinsicCapOverlapOpen period hPeriod =>
        (smoothCutBulkOpenCapHomeomorph period hPeriod).symm point.1) :=
    ((smoothCapHomeomorph_symm_contMDiff period hPeriod).of_le le_top).comp
      contMDiff_subtype_val |>.congr fun _ => rfl
  have hRange (point : intrinsicCapOverlapOpen period hPeriod) :
      (smoothCutBulkOpenCapHomeomorph period hPeriod).symm point.1 ∈
        Set.range (smoothCutCapOverlapToSmoothCap period hPeriod) := by
    rcases point.2 with ⟨source, hSource⟩
    refine ⟨source, ?_⟩
    apply (smoothCutBulkOpenCapHomeomorph period hPeriod).injective
    simpa [smoothCutCapOverlapToIntrinsicCap] using hSource
  exact (smoothCutCapOverlapToSmoothCap_inverse_contMDiffOn period hPeriod)
    |>.comp_contMDiff hIntoCap hRange

def smoothCutCapOverlapIntrinsicDiffeomorph :
    letI := smoothCutCapOverlapChartedSpace period hPeriod
    letI := cutBulkOpenCapQuotientChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    SmoothCutCapOverlap period hPeriod ≃ₘ^∞⟮
      identityCoverModelWithCorners (𝓡 3), coverModelWithCorners⟯
      intrinsicCapOverlapOpen period hPeriod := by
  letI := smoothCutCapOverlapChartedSpace period hPeriod
  letI := cutBulkOpenCapQuotientChartedSpace period hPeriod
  letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
  exact
    { toFun := smoothCutCapOverlapToIntrinsicCapOpen period hPeriod
      invFun := intrinsicCapOpenToSmoothCutCapOverlap period hPeriod
      left_inv := smoothCutCapOverlapToIntrinsicCapOpen_leftInverse period hPeriod
      right_inv := smoothCutCapOverlapToIntrinsicCapOpen_rightInverse period hPeriod
      contMDiff_toFun :=
        smoothCutCapOverlapToIntrinsicCapOpen_contMDiff period hPeriod
      contMDiff_invFun :=
        intrinsicCapOpenToSmoothCutCapOverlap_contMDiff period hPeriod }

end
end P0EFTJanusMappingTorusCutBulkIntrinsicCapOverlapDiffeomorph4D
end JanusFormal
