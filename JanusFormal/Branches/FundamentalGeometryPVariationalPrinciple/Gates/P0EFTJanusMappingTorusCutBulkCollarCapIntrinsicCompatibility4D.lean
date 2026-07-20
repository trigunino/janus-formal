import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicCapOverlapDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarPositiveOpenDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarOverlapExactIntrinsicRange4D

/-!
# Intrinsic smooth collar--cap compatibility
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarCapIntrinsicCompatibility4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarPositiveOpenDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkCollarOverlapOpenCollarIdentification4D
open P0EFTJanusMappingTorusCutBulkCollarOverlapExactIntrinsicRange4D
open P0EFTJanusMappingTorusCutBulkCapOverlapExactIntrinsicRange4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapOverlapDiffeomorph4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem smoothCutCapOverlapToIntrinsicCapOpen_common_contMDiff :
    letI := smoothCutCapOverlapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    ContMDiff (identityCoverModelWithCorners (𝓡 3))
      cutCollarModelWithCorners ∞
      (smoothCutCapOverlapToIntrinsicCapOpen period hPeriod) := by
  letI := smoothCutCapOverlapChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  rw [← ContMDiff.subtypeVal_comp_iff (intrinsicCapOverlapOpen period hPeriod)]
  have hStandard :=
    smoothCutCapOverlapToIntrinsicCapOpen_contMDiff period hPeriod
  have hUnderlying : ContMDiff (identityCoverModelWithCorners (𝓡 3))
      coverModelWithCorners ∞
      (Subtype.val ∘ smoothCutCapOverlapToIntrinsicCapOpen period hPeriod) :=
    (ContMDiff.subtypeVal_comp_iff
      (intrinsicCapOverlapOpen period hPeriod)
      (smoothCutCapOverlapToIntrinsicCapOpen period hPeriod)).2 hStandard
  exact ((intrinsicCapStandardToCommon_contMDiff period hPeriod).comp
    hUnderlying).congr fun _ => rfl

theorem intrinsicCapOpenToSmoothCutCapOverlap_common_contMDiff :
    letI := smoothCutCapOverlapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    ContMDiff cutCollarModelWithCorners
      (identityCoverModelWithCorners (𝓡 3)) ∞
      (intrinsicCapOpenToSmoothCutCapOverlap period hPeriod) := by
  letI := smoothCutCapOverlapChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  have hOpenIdentity : ContMDiff cutCollarModelWithCorners
      coverModelWithCorners ∞
      (id : intrinsicCapOverlapOpen period hPeriod →
        intrinsicCapOverlapOpen period hPeriod) := by
    rw [← ContMDiff.subtypeVal_comp_iff (intrinsicCapOverlapOpen period hPeriod)]
    exact ((intrinsicCapCommonToStandard_contMDiff period hPeriod).comp
      (contMDiff_subtype_val : ContMDiff cutCollarModelWithCorners
        cutCollarModelWithCorners ∞
        (Subtype.val : intrinsicCapOverlapOpen period hPeriod →
          CutBulkOpenCap period hPeriod))).congr fun _ => rfl
  exact (intrinsicCapOpenToSmoothCutCapOverlap_contMDiff period hPeriod).comp
    hOpenIdentity

def smoothCutCapOverlapIntrinsicCommonDiffeomorph :
    letI := smoothCutCapOverlapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    SmoothCutCapOverlap period hPeriod ≃ₘ^∞⟮
      identityCoverModelWithCorners (𝓡 3), cutCollarModelWithCorners⟯
      intrinsicCapOverlapOpen period hPeriod := by
  letI := smoothCutCapOverlapChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  exact
    { toFun := smoothCutCapOverlapToIntrinsicCapOpen period hPeriod
      invFun := intrinsicCapOpenToSmoothCutCapOverlap period hPeriod
      left_inv := smoothCutCapOverlapToIntrinsicCapOpen_leftInverse period hPeriod
      right_inv := smoothCutCapOverlapToIntrinsicCapOpen_rightInverse period hPeriod
      contMDiff_toFun :=
        smoothCutCapOverlapToIntrinsicCapOpen_common_contMDiff period hPeriod
      contMDiff_invFun :=
        intrinsicCapOpenToSmoothCutCapOverlap_common_contMDiff period hPeriod }

/-- Final smooth transition between the positive intrinsic collar and the
strict intrinsic cap overlap, both expressed in the common half-space model. -/
def intrinsicCollarCapOverlapDiffeomorph :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    letI := smoothCutCapOverlapChartedSpace period hPeriod
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    cutThroatPositiveOpenCollarOpen period hPeriod ≃ₘ^∞⟮
      cutCollarModelWithCorners, cutCollarModelWithCorners⟯
      intrinsicCapOverlapOpen period hPeriod := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  letI := smoothCutCapOverlapChartedSpace period hPeriod
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  exact (smoothCutCollarOverlapIntrinsicDiffeomorph period hPeriod).symm |>.trans
    ((smoothCutCollarCapOverlapDiffeomorph period hPeriod).trans
      (smoothCutCapOverlapIntrinsicCommonDiffeomorph period hPeriod))

theorem intrinsicCollarCapOverlapDiffeomorph_bulk_eq_attachment
    (point : cutThroatPositiveOpenCollarOpen period hPeriod) :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    letI := smoothCutCapOverlapChartedSpace period hPeriod
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapChartedSpace period hPeriod
    letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    ((intrinsicCollarCapOverlapDiffeomorph period hPeriod point).1.1 :
      PositiveHemisphereCutBulk period hPeriod) =
      cutOpenCollarAttachment period hPeriod point.1 := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  letI := smoothCutCapOverlapChartedSpace period hPeriod
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  let overlap :=
    (smoothCutCollarOverlapIntrinsicDiffeomorph period hPeriod).symm point
  have hPoint :
      smoothCutCollarOverlapIntrinsicDiffeomorph period hPeriod overlap = point :=
    (smoothCutCollarOverlapIntrinsicDiffeomorph period hPeriod).apply_symm_apply point
  change smoothCutCapOverlapToCutBulk period hPeriod
      (smoothCutCollarCapOverlapDiffeomorph period hPeriod overlap) =
    cutOpenCollarAttachment period hPeriod point.1
  change smoothCutCollarOverlapToCutBulk period hPeriod overlap =
    cutOpenCollarAttachment period hPeriod point.1
  rw [← cutOpenCollarAttachment_smoothCutCollarOverlapToIntrinsicOpenCollar]
  congr 1
  have hPointValue := congrArg Subtype.val hPoint
  rw [smoothCutCollarOverlapIntrinsicDiffeomorph_apply period hPeriod] at hPointValue
  exact hPointValue

end
end P0EFTJanusMappingTorusCutBulkCollarCapIntrinsicCompatibility4D
end JanusFormal
