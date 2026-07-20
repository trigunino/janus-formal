import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkLatitudeBand4D

/-!
# Closed collar/remainder decomposition of the cut bulk

The latitude band occupied by the attached collar and the closed outer
remainder cover the cut bulk.  Their intersection is exactly the artificial
outer face.  This closes the topological gluing ledger; compatibility of a
global smooth atlas and geometric Stokes remain separate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCollarRemainderDecomposition4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Closed part of the positive-hemisphere cut bulk beyond latitude one. -/
def cutBulkOuterRemainder :
    Set (PositiveHemisphereCutBulk period hPeriod) :=
  {bulk | Real.sin 1 ≤ cutBulkLatitudeCoordinate period hPeriod bulk}

theorem cutBulkLatitudeCoordinate_nonneg
    (bulk : PositiveHemisphereCutBulk period hPeriod) :
    0 ≤ cutBulkLatitudeCoordinate period hPeriod bulk := by
  refine Quotient.inductionOn bulk ?_
  intro representative
  exact representative.fiber.2

theorem isClosed_cutBulkOuterRemainder :
    IsClosed (cutBulkOuterRemainder period hPeriod) :=
  isClosed_Ici.preimage (continuous_cutBulkLatitudeCoordinate period hPeriod)

/-- The attached collar and outer remainder cover the whole cut bulk. -/
theorem range_cutCollarAttachment_union_outerRemainder :
    Set.range (cutCollarAttachment period hPeriod) ∪
        cutBulkOuterRemainder period hPeriod = Set.univ := by
  rw [range_cutCollarAttachment]
  ext bulk
  simp only [cutBulkOuterRemainder, mem_union, mem_preimage, mem_Icc,
    mem_setOf_eq, mem_univ, iff_true]
  have hNonneg := cutBulkLatitudeCoordinate_nonneg period hPeriod bulk
  exact (le_total (cutBulkLatitudeCoordinate period hPeriod bulk)
    (Real.sin 1)).elim (fun h => Or.inl ⟨hNonneg, h⟩) Or.inr

/-- The overlap of the two closed pieces is precisely the explicit outer
latitude face. -/
theorem range_cutCollarAttachment_inter_outerRemainder :
    Set.range (cutCollarAttachment period hPeriod) ∩
        cutBulkOuterRemainder period hPeriod =
      Set.range (cutOuterLatitudeInclusion period hPeriod) := by
  rw [range_cutCollarAttachment, range_cutOuterLatitudeInclusion]
  ext bulk
  simp only [cutBulkOuterRemainder, mem_inter_iff, mem_preimage, mem_Icc,
    mem_setOf_eq]
  constructor
  · rintro ⟨⟨-, hUpper⟩, hLower⟩
    exact le_antisymm hUpper hLower
  · intro hLevel
    rw [hLevel]
    exact ⟨⟨Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
      (by linarith [Real.pi_gt_three]), le_rfl⟩, le_rfl⟩

end
end P0EFTJanusMappingTorusCutBulkCollarRemainderDecomposition4D
end JanusFormal
