import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D

/-! # The cut boundary as the zero face of the open collar -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryOpenCollarFace4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The throat boundary included as the zero face of the open collar. -/
def cutBoundaryOpenCollarFace
    (boundary : CutThroatBoundary period hPeriod) :
    ↥(cutThroatOpenCollarOpen period hPeriod) :=
  ⟨cutThroatFace period hPeriod boundary,
    by change ((⊥ : CutCollarInterval) : Real) < 1; simp⟩

@[simp] theorem cutBoundaryOpenCollarFace_val
    (boundary : CutThroatBoundary period hPeriod) :
    (cutBoundaryOpenCollarFace period hPeriod boundary).1 =
      cutThroatFace period hPeriod boundary :=
  rfl

theorem contMDiff_cutBoundaryOpenCollarFace :
    letI := cutThroatBoundaryChartedSpace period hPeriod
    letI := cutThroatFiniteCollarChartedSpace period hPeriod
    ContMDiff throatCoverModelWithCorners cutCollarModelWithCorners ∞
      (cutBoundaryOpenCollarFace period hPeriod) := by
  letI := cutThroatBoundaryChartedSpace period hPeriod
  letI := cutThroatFiniteCollarChartedSpace period hPeriod
  rw [← ContMDiff.subtypeVal_comp_iff
    (cutThroatOpenCollarOpen period hPeriod)]
  exact (contMDiff_cutThroatFace period hPeriod).of_le (by simp)

@[simp] theorem cutOpenCollarAttachment_cutBoundaryOpenCollarFace
    (boundary : CutThroatBoundary period hPeriod) :
    cutOpenCollarAttachment period hPeriod
        (cutBoundaryOpenCollarFace period hPeriod boundary) =
      cutBoundaryInclusion period hPeriod boundary :=
  cutCollarAttachment_cutThroatFace period hPeriod boundary

end
end P0EFTJanusMappingTorusCutBoundaryOpenCollarFace4D
end JanusFormal
