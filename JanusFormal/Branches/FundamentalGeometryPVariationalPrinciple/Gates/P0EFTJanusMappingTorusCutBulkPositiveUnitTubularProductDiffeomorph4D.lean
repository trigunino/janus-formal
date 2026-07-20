import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarOverlapIntrinsicSmooth4D

/-!
# Product form of the strict positive tubular parameters
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkPositiveUnitTubularProductDiffeomorph4D

set_option autoImplicit false
noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D

def positiveUnitNormalOpen : Opens Real :=
  ⟨Ioo 0 1, isOpen_Ioo⟩

def positiveUnitTubularToProduct
    (parameter : positiveUnitTubularParameterOpen) :
    EquatorialTwoSphere × positiveUnitNormalOpen :=
  (parameter.1.1, ⟨parameter.1.2.1, parameter.2⟩)

def positiveUnitTubularFromProduct
    (parameter : EquatorialTwoSphere × positiveUnitNormalOpen) :
    positiveUnitTubularParameterOpen :=
  ⟨(parameter.1,
      ⟨parameter.2.1, by
        constructor
        · linarith [parameter.2.2.1, Real.pi_pos]
        · linarith [parameter.2.2.2, Real.pi_gt_three]⟩),
    parameter.2.2⟩

theorem positiveUnitTubularToProduct_contMDiff :
    ContMDiff CollarOverlapFiberModel CollarOverlapFiberModel ∞
      positiveUnitTubularToProduct := by
  have hBase : ContMDiff CollarOverlapFiberModel (𝓡 2) ∞
      (fun parameter : positiveUnitTubularParameterOpen => parameter.1.1) :=
    contMDiff_fst.comp contMDiff_subtype_val
  have hNormal : ContMDiff CollarOverlapFiberModel 𝓘(Real, Real) ∞
      (fun parameter : positiveUnitTubularParameterOpen =>
        (positiveUnitTubularToProduct parameter).2) := by
    rw [← ContMDiff.subtypeVal_comp_iff positiveUnitNormalOpen]
    have hVal : ContMDiff CollarOverlapFiberModel CollarOverlapFiberModel ∞
        (Subtype.val : positiveUnitTubularParameterOpen →
          EquatorialTwoSphere × equatorialTubularNormalOpen) :=
      contMDiff_subtype_val
    have hNormalOpen : ContMDiff CollarOverlapFiberModel 𝓘(Real, Real) ∞
        (fun parameter : positiveUnitTubularParameterOpen => parameter.1.2) :=
      contMDiff_snd.comp hVal
    exact (contMDiff_subtype_val.comp hNormalOpen).congr fun _ => rfl
  exact hBase.prodMk hNormal

theorem positiveUnitTubularFromProduct_contMDiff :
    ContMDiff CollarOverlapFiberModel CollarOverlapFiberModel ∞
      positiveUnitTubularFromProduct := by
  rw [← ContMDiff.subtypeVal_comp_iff positiveUnitTubularParameterOpen]
  have hNormal : ContMDiff CollarOverlapFiberModel 𝓘(Real, Real) ∞
      (fun parameter : EquatorialTwoSphere × positiveUnitNormalOpen =>
        (positiveUnitTubularFromProduct parameter).1.2) := by
    rw [← ContMDiff.subtypeVal_comp_iff equatorialTubularNormalOpen]
    have hSnd : ContMDiff CollarOverlapFiberModel 𝓘(Real, Real) ∞
        (Prod.snd : EquatorialTwoSphere × positiveUnitNormalOpen →
          positiveUnitNormalOpen) := contMDiff_snd
    exact (contMDiff_subtype_val.comp hSnd).congr fun _ => rfl
  exact contMDiff_fst.prodMk hNormal

def positiveUnitTubularProductDiffeomorph :
    positiveUnitTubularParameterOpen ≃ₘ^∞⟮
      CollarOverlapFiberModel, CollarOverlapFiberModel⟯
        (EquatorialTwoSphere × positiveUnitNormalOpen) where
  toFun := positiveUnitTubularToProduct
  invFun := positiveUnitTubularFromProduct
  left_inv := by intro parameter; rfl
  right_inv := by intro parameter; rfl
  contMDiff_toFun := positiveUnitTubularToProduct_contMDiff
  contMDiff_invFun := positiveUnitTubularFromProduct_contMDiff

end
end P0EFTJanusMappingTorusCutBulkPositiveUnitTubularProductDiffeomorph4D
end JanusFormal
