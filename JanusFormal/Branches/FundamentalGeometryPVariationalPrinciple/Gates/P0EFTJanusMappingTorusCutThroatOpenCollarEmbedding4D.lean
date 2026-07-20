import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCollarRemainderDecomposition4D

/-!
# Open collar chart in the cut bulk

Removing the artificial outer face from the finite collar gives an open
collar.  Its latitude attachment is an open embedding whose range is exactly
the intrinsic open band `latitude < sin 1`.  This is the boundary-chart piece
needed for a future global smooth atlas on the cut bulk.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusCutBulkCollarRemainderDecomposition4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The finite collar with its artificial latitude-one face removed. -/
def CutThroatOpenCollar :=
  {parameter : CutThroatFiniteCollar period hPeriod // parameter.2.1 < 1}

instance : TopologicalSpace (CutThroatOpenCollar period hPeriod) :=
  inferInstanceAs (TopologicalSpace
    {parameter : CutThroatFiniteCollar period hPeriod // parameter.2.1 < 1})

theorem isOpen_cutThroatOpenCollar :
    IsOpen {parameter : CutThroatFiniteCollar period hPeriod |
      parameter.2.1 < 1} :=
  isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const

/-- Restriction of the closed collar attachment to its open collar. -/
def cutOpenCollarAttachment :
    CutThroatOpenCollar period hPeriod →
      PositiveHemisphereCutBulk period hPeriod :=
  fun parameter => cutCollarAttachment period hPeriod parameter.1

theorem continuous_cutOpenCollarAttachment :
    Continuous (cutOpenCollarAttachment period hPeriod) :=
  (continuous_cutCollarAttachment period hPeriod).comp continuous_subtype_val

theorem cutOpenCollarAttachment_injective :
    Function.Injective (cutOpenCollarAttachment period hPeriod) :=
  (cutCollarAttachment_injective period hPeriod).comp Subtype.val_injective

/-- Exact intrinsic image of the open collar. -/
theorem range_cutOpenCollarAttachment :
    Set.range (cutOpenCollarAttachment period hPeriod) =
      (cutBulkLatitudeCoordinate period hPeriod) ⁻¹' Iio (Real.sin 1) := by
  ext bulk
  constructor
  · rintro ⟨parameter, rfl⟩
    change cutBulkLatitudeCoordinate period hPeriod
        (cutCollarAttachment period hPeriod parameter.1) < Real.sin 1
    rw [cutBulkLatitudeCoordinate_cutCollarAttachment]
    have hNormalRange : parameter.1.2.1 ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;>
        linarith [parameter.1.2.2.1, parameter.1.2.2.2, Real.pi_gt_three]
    have hOneRange : (1 : Real) ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_gt_three]
    exact Real.strictMonoOn_sin hNormalRange hOneRange parameter.2
  · intro hBulk
    change cutBulkLatitudeCoordinate period hPeriod bulk < Real.sin 1 at hBulk
    have hClosedBand : bulk ∈
        Set.range (cutCollarAttachment period hPeriod) := by
      rw [range_cutCollarAttachment]
      exact ⟨cutBulkLatitudeCoordinate_nonneg period hPeriod bulk, hBulk.le⟩
    rcases hClosedBand with ⟨⟨boundary, normal⟩, hAttachment⟩
    have hSin : Real.sin normal.1 < Real.sin 1 := by
      have hCoordinate :=
        cutBulkLatitudeCoordinate_cutCollarAttachment period hPeriod
          (boundary, normal)
      rw [hAttachment] at hCoordinate
      exact hCoordinate.symm.trans_lt hBulk
    have hNormalRange : normal.1 ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [normal.2.1, normal.2.2, Real.pi_gt_three]
    have hOneRange : (1 : Real) ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [Real.pi_gt_three]
    have hNormal : normal.1 < 1 :=
      (Real.strictMonoOn_sin.lt_iff_lt hNormalRange hOneRange).mp hSin
    exact ⟨⟨(boundary, normal), hNormal⟩, hAttachment⟩

theorem isOpen_range_cutOpenCollarAttachment :
    IsOpen (Set.range (cutOpenCollarAttachment period hPeriod)) := by
  rw [range_cutOpenCollarAttachment]
  exact isOpen_Iio.preimage
    (continuous_cutBulkLatitudeCoordinate period hPeriod)

theorem cutOpenCollarAttachment_isOpenEmbedding :
    IsOpenEmbedding (cutOpenCollarAttachment period hPeriod) := by
  constructor
  · exact (cutCollarAttachment_isClosedEmbedding period hPeriod).isEmbedding.comp
      IsEmbedding.subtypeVal
  · exact isOpen_range_cutOpenCollarAttachment period hPeriod

end
end P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
end JanusFormal
