import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkToAmbientOpenCapSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D

/-!
# Global smoothness of the cut-bulk map to the original mapping torus
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkToAmbientGlobalSmooth4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothAtlasFrontier
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
open P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkToAmbientOpenCapSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private theorem contMDiffOn_target_of_partialDiffeomorph
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace CutCollarModel M] [ChartedSpace CutCollarModel N]
    (Φ : PartialDiffeomorph cutCollarModelWithCorners
      cutCollarModelWithCorners M N ∞)
    (function : N → EffectiveQuotient period hPeriod)
    (hPullback : ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (function ∘ Φ)) :
    ContMDiffOn cutCollarModelWithCorners coverModelWithCorners ∞
      function Φ.target := by
  have hPullbackOn : ContMDiffOn cutCollarModelWithCorners
      coverModelWithCorners ∞ (function ∘ Φ) Set.univ :=
    hPullback.contMDiffOn
  have hComposite := hPullbackOn.comp Φ.symm.contMDiffOn (by simp)
  apply hComposite.congr
  intro point hPoint
  change function point = function (Φ (Φ.symm point))
  exact congrArg function (Φ.right_inv hPoint).symm

theorem cutBulkToAmbient_contMDiff :
    letI := cutBulkGlobalChartedSpace period hPeriod
    ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (cutBulkToAmbient period hPeriod) := by
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  have hCapStandard :=
    cutBulkToAmbient_intrinsicOpenCap_contMDiff period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  have hCap : ContMDiff cutCollarModelWithCorners coverModelWithCorners ∞
      (fun cap : CutBulkOpenCap period hPeriod ↦
        cutBulkToAmbient period hPeriod cap.1) :=
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
    period hPeriod
    (cutBulkOpenCapInclusionPartialDiffeomorph period hPeriod)
    (cutBulkToAmbient period hPeriod) hCap
  have hCapOn : ContMDiffOn cutCollarModelWithCorners coverModelWithCorners ∞
      (cutBulkToAmbient period hPeriod) (cutBulkOpenCap period hPeriod) := by
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

  have hCollar := cutBulkToAmbient_openCollar_contMDiff period hPeriod
  have hCollarOnTarget := contMDiffOn_target_of_partialDiffeomorph
    period hPeriod
    (cutOpenCollarAttachmentPartialDiffeomorph period hPeriod)
    (cutBulkToAmbient period hPeriod) hCollar
  have hCollarOn : ContMDiffOn cutCollarModelWithCorners coverModelWithCorners ∞
      (cutBulkToAmbient period hPeriod)
      (Set.range (cutOpenCollarAttachment period hPeriod)) := by
    simpa [cutOpenCollarAttachmentPartialDiffeomorph,
      cutOpenCollarAttachmentPartialHomeomorph,
      IsOpenEmbedding.toOpenPartialHomeomorph_target] using hCollarOnTarget

  exact contMDiff_of_contMDiffOn_union_of_isOpen hCollarOn hCapOn
    (openCollar_union_openCap period hPeriod)
    (isOpen_range_cutOpenCollarAttachment period hPeriod)
    (isOpen_cutBulkOpenCap period hPeriod)

end
end P0EFTJanusMappingTorusCutBulkToAmbientGlobalSmooth4D
end JanusFormal
