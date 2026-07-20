import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCapSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCollarSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D

/-!
# Global smoothness of the cut-bulk cutoff current

The cap and collar pullbacks glue across their open cover to a global `C∞`
scalar current on the preferred manifold-with-boundary atlas.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkScalarCurrentGlobalSmooth4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCollarSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

private theorem contMDiffOn_target_of_partialDiffeomorph
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace CutCollarModel M] [ChartedSpace CutCollarModel N]
    (Φ : PartialDiffeomorph cutCollarModelWithCorners
      cutCollarModelWithCorners M N ∞)
    (function : N → Real)
    (hPullback : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (function ∘ Φ)) :
    ContMDiffOn cutCollarModelWithCorners (modelWithCornersSelf Real Real) ∞
      function Φ.target := by
  have hPullbackOn : ContMDiffOn cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞ (function ∘ Φ) Set.univ :=
    hPullback.contMDiffOn
  have hComposite := hPullbackOn.comp Φ.symm.contMDiffOn (by simp)
  apply hComposite.congr
  intro point hPoint
  change function point = function (Φ (Φ.symm point))
  exact congrArg function (Φ.right_inv hPoint).symm

/-- The descended cutoff current is globally smooth in the preferred cut-bulk
manifold-with-boundary atlas. -/
theorem cutBulkScalarCurrent_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    letI := cutBulkGlobalChartedSpace period hPeriod
    ContMDiff cutCollarModelWithCorners (modelWithCornersSelf Real Real) ∞
      (cutBulkScalarCurrent period hPeriod field test) := by
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  have hCapStandard :=
    cutBulkScalarCurrent_intrinsicOpenCap_contMDiff period hPeriod field test
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  have hCap : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun cap : CutBulkOpenCap period hPeriod ↦
        cutBulkScalarCurrent period hPeriod field test cap.1) :=
    hCapStandard.comp
      (intrinsicCapCommonToStandard_contMDiff period hPeriod)

  letI : ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
    cutThroatBoundaryChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
    cutThroatFiniteCollarChartedSpace period hPeriod
  letI : ChartedSpace CutCollarModel (CutThroatOpenCollar period hPeriod) :=
    cutThroatOpenCollarChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutThroatOpenCollar period hPeriod) :=
    (cutThroatOpenCollar_isManifold period hPeriod).of_le le_top
  letI : ChartedSpace CutCollarModel
      (PositiveHemisphereCutBulk period hPeriod) :=
    cutBulkGlobalChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
    cutBulkGlobal_isManifold period hPeriod

  have hCapOnTarget := contMDiffOn_target_of_partialDiffeomorph
    (cutBulkOpenCapInclusionPartialDiffeomorph period hPeriod)
    (cutBulkScalarCurrent period hPeriod field test) hCap
  have hCapOn : ContMDiffOn cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (cutBulkScalarCurrent period hPeriod field test)
      (cutBulkOpenCap period hPeriod) := by
    apply hCapOnTarget.mono
    intro point hPoint
    have hRange : point ∈ Set.range
        (Subtype.val : CutBulkOpenCap period hPeriod →
          PositiveHemisphereCutBulk period hPeriod) :=
      ⟨⟨point, hPoint⟩, rfl⟩
    change point ∈
      (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod).target
    rw [cutBulkOpenCapInclusionPartialHomeomorph,
      IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact hRange

  have hCollar :=
    cutBulkScalarCurrent_openCollar_contMDiff period hPeriod field test
  have hCollarOnTarget := contMDiffOn_target_of_partialDiffeomorph
    (cutOpenCollarAttachmentPartialDiffeomorph period hPeriod)
    (cutBulkScalarCurrent period hPeriod field test) hCollar
  have hCollarOn : ContMDiffOn cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (cutBulkScalarCurrent period hPeriod field test)
      (Set.range (cutOpenCollarAttachment period hPeriod)) := by
    simpa [cutOpenCollarAttachmentPartialDiffeomorph,
      cutOpenCollarAttachmentPartialHomeomorph,
      IsOpenEmbedding.toOpenPartialHomeomorph_target] using hCollarOnTarget

  exact contMDiff_of_contMDiffOn_union_of_isOpen hCollarOn hCapOn
    (openCollar_union_openCap period hPeriod)
    (isOpen_range_cutOpenCollarAttachment period hPeriod)
    (isOpen_cutBulkOpenCap period hPeriod)

end
end P0EFTJanusMappingTorusCutBulkScalarCurrentGlobalSmooth4D
end JanusFormal
