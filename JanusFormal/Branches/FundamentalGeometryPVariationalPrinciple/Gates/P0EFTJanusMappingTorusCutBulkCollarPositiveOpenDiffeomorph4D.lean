import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarOverlapProductDiffeomorph4D

/-!
# Product diffeomorphism onto the positive intrinsic collar overlap
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarPositiveOpenDiffeomorph4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarOverlapOpenCollarIdentification4D
open P0EFTJanusMappingTorusCutBulkCollarOverlapIntrinsicSmooth4D
open P0EFTJanusMappingTorusCutBulkPositiveUnitTubularProductDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkCollarOverlapProductDiffeomorph4D

variable (period : Real) (hPeriod : period ≠ 0)

def cutThroatPositiveOpenCollarOpen :
    TopologicalSpace.Opens (CutThroatOpenCollar period hPeriod) :=
  ⟨{point | 0 < point.1.2.1}, by
    have hNormal : Continuous
        (fun point : CutThroatOpenCollar period hPeriod => point.1.2.1) :=
      continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)
    exact isOpen_lt continuous_const hNormal⟩

def positiveCollarProductToOpen
    (point : CutThroatBoundary period hPeriod × positiveUnitNormalOpen) :
    cutThroatPositiveOpenCollarOpen period hPeriod :=
  ⟨⟨(point.1, ⟨point.2.1, point.2.2.1.le, point.2.2.2.le⟩),
      point.2.2.2⟩,
    point.2.2.1⟩

def positiveCollarOpenToProduct
    (point : cutThroatPositiveOpenCollarOpen period hPeriod) :
    CutThroatBoundary period hPeriod × positiveUnitNormalOpen :=
  (point.1.1.1, ⟨point.1.1.2.1, point.2, point.1.2⟩)

theorem positiveUnitNormalToInterval_contMDiff :
    ContMDiff 𝓘(Real, Real) (modelWithCornersEuclideanHalfSpace 1) ∞
      (fun normal : positiveUnitNormalOpen =>
        (⟨normal.1, normal.2.1.le, normal.2.2.le⟩ : CutCollarInterval)) := by
  have hVal : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞
      (Subtype.val : positiveUnitNormalOpen → Real) := contMDiff_subtype_val
  have hRange (normal : positiveUnitNormalOpen) : (normal : Real) ∈ Icc 0 1 :=
    ⟨normal.2.1.le, normal.2.2.le⟩
  have hProjection := (contMDiffOn_projIcc (x := (0 : Real)) (y := 1)
    (n := ∞)).comp_contMDiff hVal hRange
  exact hProjection.congr fun normal => by
    rw [Function.comp_apply, projIcc_of_mem _ (hRange normal)]

theorem positiveCollarProductToOpen_contMDiff :
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    ContMDiff (throatCoverModelWithCorners.prod 𝓘(Real, Real))
      cutCollarModelWithCorners ∞
      (positiveCollarProductToOpen period hPeriod) := by
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatFiniteCollarChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  change ContMDiff (throatCoverModelWithCorners.prod 𝓘(Real, Real))
    cutCollarModelWithCorners ∞
    (fun point => show cutThroatPositiveOpenCollarOpen period hPeriod from
      positiveCollarProductToOpen period hPeriod point)
  rw [← ContMDiff.subtypeVal_comp_iff
    (cutThroatPositiveOpenCollarOpen period hPeriod)]
  change ContMDiff (throatCoverModelWithCorners.prod 𝓘(Real, Real))
    cutCollarModelWithCorners ∞
    (fun point => show cutThroatOpenCollarOpen period hPeriod from
      (positiveCollarProductToOpen period hPeriod point).1)
  rw [← ContMDiff.subtypeVal_comp_iff (cutThroatOpenCollarOpen period hPeriod)]
  exact contMDiff_fst.prodMk
    (positiveUnitNormalToInterval_contMDiff.comp contMDiff_snd)

theorem positiveCollarOpenToProduct_contMDiff :
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    ContMDiff cutCollarModelWithCorners
      (throatCoverModelWithCorners.prod 𝓘(Real, Real)) ∞
      (positiveCollarOpenToProduct period hPeriod) := by
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatFiniteCollarChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  have hOpenVal : ContMDiff cutCollarModelWithCorners cutCollarModelWithCorners ∞
      (fun point : cutThroatPositiveOpenCollarOpen period hPeriod => point.1) :=
    contMDiff_subtype_val
  have hFinite : ContMDiff cutCollarModelWithCorners cutCollarModelWithCorners ∞
      (fun point : cutThroatPositiveOpenCollarOpen period hPeriod => point.1.1) :=
    ((cutThroatOpenCollar_val_contMDiff period hPeriod).of_le (by simp)).comp
      hOpenVal |>.congr fun _ => rfl
  have hBoundary := contMDiff_fst.comp hFinite
  have hNormal : ContMDiff cutCollarModelWithCorners 𝓘(Real, Real) ∞
      (fun point : cutThroatPositiveOpenCollarOpen period hPeriod =>
        (positiveCollarOpenToProduct period hPeriod point).2) := by
    rw [← ContMDiff.subtypeVal_comp_iff positiveUnitNormalOpen]
    exact (contMDiff_subtype_coe_Icc.comp
      (contMDiff_snd.comp hFinite)).congr fun _ => rfl
  exact hBoundary.prodMk hNormal

def positiveCollarProductDiffeomorph :
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    (CutThroatBoundary period hPeriod × positiveUnitNormalOpen) ≃ₘ^∞⟮
      throatCoverModelWithCorners.prod 𝓘(Real, Real),
      cutCollarModelWithCorners⟯
        cutThroatPositiveOpenCollarOpen period hPeriod := by
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  exact
    { toFun := positiveCollarProductToOpen period hPeriod
      invFun := positiveCollarOpenToProduct period hPeriod
      left_inv := by intro point; rfl
      right_inv := by intro point; rfl
      contMDiff_toFun := positiveCollarProductToOpen_contMDiff period hPeriod
      contMDiff_invFun := positiveCollarOpenToProduct_contMDiff period hPeriod }

def smoothCutCollarOverlapIntrinsicDiffeomorph :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    SmoothCutCollarOverlap period hPeriod ≃ₘ^∞⟮
      identityCoverModelWithCorners CollarOverlapFiberModel,
      cutCollarModelWithCorners⟯
        cutThroatPositiveOpenCollarOpen period hPeriod := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  exact (smoothCutCollarOverlapProductDiffeomorph period hPeriod).trans
    (positiveCollarProductDiffeomorph period hPeriod)

def smoothCutCollarOverlapToPositiveOpen
    (point : SmoothCutCollarOverlap period hPeriod) :
    cutThroatPositiveOpenCollarOpen period hPeriod :=
  ⟨smoothCutCollarOverlapToIntrinsicOpenCollar period hPeriod point, by
    rw [smoothCutCollarOverlapToIntrinsicOpenCollar_eq_natural]
    exact (smoothCutCollarOverlapNormal_mem_Ioo period hPeriod point).1⟩

theorem smoothCutCollarOverlapIntrinsicDiffeomorph_apply :
    letI := smoothCutCollarOverlapChartedSpace period hPeriod
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    (smoothCutCollarOverlapIntrinsicDiffeomorph period hPeriod :
      SmoothCutCollarOverlap period hPeriod →
        cutThroatPositiveOpenCollarOpen period hPeriod) =
      smoothCutCollarOverlapToPositiveOpen period hPeriod := by
  letI := smoothCutCollarOverlapChartedSpace period hPeriod
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatOpenCollarChartedSpace period hPeriod
  funext point
  refine Quotient.inductionOn point ?_
  intro representative
  apply Subtype.ext
  change (smoothCutCollarOverlapIntrinsicDiffeomorph period hPeriod
      (mappingTorusMk _ representative)).1 =
    smoothCutCollarOverlapToIntrinsicOpenCollar period hPeriod
      (mappingTorusMk _ representative)
  rw [smoothCutCollarOverlapToIntrinsicOpenCollar_eq_natural]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

end
end P0EFTJanusMappingTorusCutBulkCollarPositiveOpenDiffeomorph4D
end JanusFormal
