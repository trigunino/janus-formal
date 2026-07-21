import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarOverlapBoundarySmooth4D

/-!
# Smooth intrinsic realization of the quotient collar overlap
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarOverlapIntrinsicSmooth4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarOverlapExactIntrinsicRange4D
open P0EFTJanusMappingTorusCutBulkCollarOverlapOpenCollarIdentification4D
open P0EFTJanusMappingTorusCutBulkCollarOverlapNormalSmooth4D
open P0EFTJanusMappingTorusCutBulkCollarOverlapBoundarySmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem smoothCutCollarOverlapNormal_mem_Ioo
    (point : SmoothCutCollarOverlap period hPeriod) :
    smoothCutCollarOverlapNormal period hPeriod point ∈ Ioo 0 1 := by
  refine Quotient.inductionOn point ?_
  intro representative
  exact representative.fiber.2

def smoothCutCollarOverlapInterval
    (point : SmoothCutCollarOverlap period hPeriod) : CutCollarInterval :=
  ⟨smoothCutCollarOverlapNormal period hPeriod point,
    (smoothCutCollarOverlapNormal_mem_Ioo period hPeriod point).1.le,
    (smoothCutCollarOverlapNormal_mem_Ioo period hPeriod point).2.le⟩

theorem smoothCutCollarOverlapInterval_contMDiff :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    ContMDiff (identityCoverModelWithCorners CollarOverlapFiberModel)
      (modelWithCornersEuclideanHalfSpace 1) ∞
      (smoothCutCollarOverlapInterval period hPeriod) := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  have hNormal := smoothCutCollarOverlapNormal_contMDiff period hPeriod
  have hRange (point : SmoothCutCollarOverlap period hPeriod) :
      smoothCutCollarOverlapNormal period hPeriod point ∈ Icc 0 1 :=
    ⟨(smoothCutCollarOverlapNormal_mem_Ioo period hPeriod point).1.le,
      (smoothCutCollarOverlapNormal_mem_Ioo period hPeriod point).2.le⟩
  have hProjection := (contMDiffOn_projIcc (x := (0 : Real)) (y := 1)
    (n := ∞)).comp_contMDiff hNormal hRange
  exact hProjection.congr fun point => by
    rw [Function.comp_apply, projIcc_of_mem _ (hRange point)]
    apply Subtype.ext
    rfl

def smoothCutCollarOverlapNaturalOpenCollar
    (point : SmoothCutCollarOverlap period hPeriod) :
    CutThroatOpenCollar period hPeriod :=
  ⟨(smoothCutCollarOverlapBoundary period hPeriod point,
      smoothCutCollarOverlapInterval period hPeriod point),
    (smoothCutCollarOverlapNormal_mem_Ioo period hPeriod point).2⟩

theorem smoothCutCollarOverlapNaturalOpenCollar_contMDiff :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    ContMDiff (identityCoverModelWithCorners CollarOverlapFiberModel)
      cutCollarModelWithCorners ∞
      (smoothCutCollarOverlapNaturalOpenCollar period hPeriod) := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatFiniteCollarChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  change ContMDiff (identityCoverModelWithCorners CollarOverlapFiberModel)
    cutCollarModelWithCorners ∞
    (fun point => show cutThroatOpenCollarOpen period hPeriod from
      smoothCutCollarOverlapNaturalOpenCollar period hPeriod point)
  rw [← ContMDiff.subtypeVal_comp_iff (cutThroatOpenCollarOpen period hPeriod)]
  exact (smoothCutCollarOverlapBoundary_contMDiff period hPeriod).prodMk
    (smoothCutCollarOverlapInterval_contMDiff period hPeriod)

theorem cutOpenCollarAttachment_smoothCutCollarOverlapNaturalOpenCollar
    (point : SmoothCutCollarOverlap period hPeriod) :
    cutOpenCollarAttachment period hPeriod
        (smoothCutCollarOverlapNaturalOpenCollar period hPeriod point) =
      smoothCutCollarOverlapToCutBulk period hPeriod point := by
  refine Quotient.inductionOn point ?_
  intro representative
  rfl

theorem smoothCutCollarOverlapToIntrinsicOpenCollar_eq_natural :
    smoothCutCollarOverlapToIntrinsicOpenCollar period hPeriod =
      smoothCutCollarOverlapNaturalOpenCollar period hPeriod := by
  funext point
  apply cutOpenCollarAttachment_injective period hPeriod
  rw [cutOpenCollarAttachment_smoothCutCollarOverlapToIntrinsicOpenCollar,
    cutOpenCollarAttachment_smoothCutCollarOverlapNaturalOpenCollar]

theorem smoothCutCollarOverlapToIntrinsicOpenCollar_contMDiff :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    ContMDiff (identityCoverModelWithCorners CollarOverlapFiberModel)
      cutCollarModelWithCorners ∞
      (smoothCutCollarOverlapToIntrinsicOpenCollar period hPeriod) := by
  rw [smoothCutCollarOverlapToIntrinsicOpenCollar_eq_natural]
  exact smoothCutCollarOverlapNaturalOpenCollar_contMDiff period hPeriod

end
end P0EFTJanusMappingTorusCutBulkCollarOverlapIntrinsicSmooth4D
end JanusFormal
