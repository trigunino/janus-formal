import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D

/-!
# Two-open atlas cover of the cut bulk

The intrinsic positive-latitude cap and the previously constructed open
collar cover the whole cut bulk.  Their overlap is exactly
`0 < latitude < sin 1`.  This isolates the two pieces whose smooth structures
must be made compatible for the global manifold-with-boundary atlas.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusCutBulkCollarRemainderDecomposition4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Intrinsic open cap away from the cut boundary. -/
def cutBulkOpenCap : Set (PositiveHemisphereCutBulk period hPeriod) :=
  (cutBulkLatitudeCoordinate period hPeriod) ⁻¹' Ioi 0

theorem isOpen_cutBulkOpenCap : IsOpen (cutBulkOpenCap period hPeriod) :=
  isOpen_Ioi.preimage (continuous_cutBulkLatitudeCoordinate period hPeriod)

def CutBulkOpenCap := ↥(cutBulkOpenCap period hPeriod)

instance : TopologicalSpace (CutBulkOpenCap period hPeriod) :=
  inferInstanceAs (TopologicalSpace ↥(cutBulkOpenCap period hPeriod))

theorem cutBulkOpenCap_subtypeVal_isOpenEmbedding :
    IsOpenEmbedding
      (Subtype.val : CutBulkOpenCap period hPeriod →
        PositiveHemisphereCutBulk period hPeriod) :=
  (isOpen_cutBulkOpenCap period hPeriod).isOpenEmbedding_subtypeVal

private theorem sin_one_pos : 0 < Real.sin 1 :=
  Real.sin_pos_of_pos_of_lt_pi (by norm_num)
    (by linarith [Real.pi_gt_three])

/-- The boundary collar and positive cap form an actual open cover. -/
theorem openCollar_union_openCap :
    Set.range (cutOpenCollarAttachment period hPeriod) ∪
        cutBulkOpenCap period hPeriod = Set.univ := by
  rw [range_cutOpenCollarAttachment]
  ext bulk
  simp only [cutBulkOpenCap, mem_union, mem_preimage, mem_Iio, mem_Ioi,
    mem_univ, iff_true]
  by_cases hPositive : 0 < cutBulkLatitudeCoordinate period hPeriod bulk
  · exact Or.inr hPositive
  · left
    have hZero : cutBulkLatitudeCoordinate period hPeriod bulk = 0 :=
      le_antisymm (le_of_not_gt hPositive)
        (cutBulkLatitudeCoordinate_nonneg period hPeriod bulk)
    rw [hZero]
    exact sin_one_pos

/-- Exact overlap on which collar and cap transition maps must agree. -/
theorem openCollar_inter_openCap :
    Set.range (cutOpenCollarAttachment period hPeriod) ∩
        cutBulkOpenCap period hPeriod =
      (cutBulkLatitudeCoordinate period hPeriod) ⁻¹'
        Ioo 0 (Real.sin 1) := by
  rw [range_cutOpenCollarAttachment]
  ext bulk
  simp only [cutBulkOpenCap, mem_inter_iff, mem_preimage, mem_Iio, mem_Ioi,
    mem_Ioo, and_comm]

end
end P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
end JanusFormal
