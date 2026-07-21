import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarOverlapExactIntrinsicRange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D

/-!
# Identification of the quotient collar overlap with the intrinsic open collar
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarOverlapOpenCollarIdentification4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarOverlapExactIntrinsicRange4D

variable (period : Real) (hPeriod : period ≠ 0)

private theorem smoothCutCollarOverlapToCutBulk_mem_openCollar
    (point : SmoothCutCollarOverlap period hPeriod) :
    smoothCutCollarOverlapToCutBulk period hPeriod point ∈
      Set.range (cutOpenCollarAttachment period hPeriod) := by
  rw [range_cutOpenCollarAttachment]
  have hRange : smoothCutCollarOverlapToCutBulk period hPeriod point ∈
      Set.range (smoothCutCollarOverlapToCutBulk period hPeriod) := ⟨point, rfl⟩
  rw [range_smoothCutCollarOverlapToCutBulk] at hRange
  exact hRange.2

/-- Canonical realization of the quotient collar overlap inside the intrinsic
open collar. -/
def smoothCutCollarOverlapToIntrinsicOpenCollar :
    SmoothCutCollarOverlap period hPeriod →
      CutThroatOpenCollar period hPeriod :=
  fun point =>
    ((cutOpenCollarAttachment_isOpenEmbedding period hPeriod).isEmbedding
      |>.toHomeomorph).symm
      ⟨smoothCutCollarOverlapToCutBulk period hPeriod point,
        smoothCutCollarOverlapToCutBulk_mem_openCollar period hPeriod point⟩

@[simp] theorem cutOpenCollarAttachment_smoothCutCollarOverlapToIntrinsicOpenCollar
    (point : SmoothCutCollarOverlap period hPeriod) :
    cutOpenCollarAttachment period hPeriod
        (smoothCutCollarOverlapToIntrinsicOpenCollar period hPeriod point) =
      smoothCutCollarOverlapToCutBulk period hPeriod point := by
  let homeomorph :=
    (cutOpenCollarAttachment_isOpenEmbedding period hPeriod).isEmbedding
      |>.toHomeomorph
  have hApply := homeomorph.apply_symm_apply
    ⟨smoothCutCollarOverlapToCutBulk period hPeriod point,
      smoothCutCollarOverlapToCutBulk_mem_openCollar period hPeriod point⟩
  exact congrArg Subtype.val hApply

theorem smoothCutCollarOverlapToIntrinsicOpenCollar_isOpenEmbedding :
    IsOpenEmbedding
      (smoothCutCollarOverlapToIntrinsicOpenCollar period hPeriod) := by
  let targetRange := Set.range (cutOpenCollarAttachment period hPeriod)
  let restricted : SmoothCutCollarOverlap period hPeriod → targetRange :=
    targetRange.codRestrict
      (smoothCutCollarOverlapToCutBulk period hPeriod)
      (smoothCutCollarOverlapToCutBulk_mem_openCollar period hPeriod)
  have hRestricted : IsOpenEmbedding restricted := by
    constructor
    · exact (smoothCutCollarOverlapToCutBulk_isOpenEmbedding period hPeriod).isEmbedding
        |>.codRestrict targetRange
          (smoothCutCollarOverlapToCutBulk_mem_openCollar period hPeriod)
    · rw [← image_univ]
      exact (smoothCutCollarOverlapToCutBulk_isOpenEmbedding period hPeriod).isOpenMap
        |>.codRestrict
          (smoothCutCollarOverlapToCutBulk_mem_openCollar period hPeriod)
          Set.univ isOpen_univ
  let homeomorph :=
    (cutOpenCollarAttachment_isOpenEmbedding period hPeriod).isEmbedding
      |>.toHomeomorph
  have hComposite := homeomorph.symm.isOpenEmbedding.comp hRestricted
  have hEq : smoothCutCollarOverlapToIntrinsicOpenCollar period hPeriod =
      homeomorph.symm ∘ restricted := by
    funext point
    apply congrArg homeomorph.symm
    apply Subtype.ext
    rfl
  rw [hEq]
  exact hComposite

end
end P0EFTJanusMappingTorusCutBulkCollarOverlapOpenCollarIdentification4D
end JanusFormal
