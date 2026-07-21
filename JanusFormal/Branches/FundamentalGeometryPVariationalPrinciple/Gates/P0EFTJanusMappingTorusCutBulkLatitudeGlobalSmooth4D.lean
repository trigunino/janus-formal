import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentGlobalSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkLatitudeBand4D

/-!
# Global smoothness of the cut-bulk latitude
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkLatitudeGlobalSmooth4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
open P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonCompatibility4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasGlobalLocalDiffeomorph4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance : Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩

local instance boundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance finiteCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatFiniteCollar period hPeriod) :=
  cutThroatFiniteCollarChartedSpace period hPeriod

local instance openCollarChartedSpace :
    ChartedSpace CutCollarModel (CutThroatOpenCollar period hPeriod) :=
  cutThroatOpenCollarChartedSpace period hPeriod

private abbrev OpenCapCover :=
  MappingTorusCover (cutBulkOpenCapData period hPeriod)

def cutBulkOpenCapLatitudeCover (point : OpenCapCover period hPeriod) : Real :=
  point.fiber.1.1 0

private theorem refl_zpow_apply {X : Type*} [TopologicalSpace X]
    (winding : Int) (point : X) :
    ((Homeomorph.refl X) ^ winding) point = point := by
  rw [show ((Homeomorph.refl X) ^ winding) point =
      ((Homeomorph.refl X) ^ winding).toEquiv point from rfl,
    homeomorph_toEquiv_zpow]
  rw [show (Homeomorph.refl X).toEquiv = 1 from rfl, one_zpow]
  rfl

private theorem cutBulkOpenCapLatitudeCover_invariant
    (winding : Int) (point : OpenCapCover period hPeriod) :
    cutBulkOpenCapLatitudeCover period hPeriod (winding +ᵥ point) =
      cutBulkOpenCapLatitudeCover period hPeriod point := by
  change (((Homeomorph.refl positiveHemisphereInteriorOpen) ^ winding)
    point.fiber).1.1 0 = point.fiber.1.1 0
  rw [refl_zpow_apply]

private theorem cutBulkOpenCapLatitudeCover_contMDiff :
    letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
      cutBulkOpenCapCoverChartedSpace period hPeriod
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (cutBulkOpenCapLatitudeCover period hPeriod) := by
  letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
    (coverHomeomorphProd (cutBulkOpenCapData period hPeriod))
  have hFst : ContMDiff
      ((𝓡 3).prod
        (modelWithCornersSelf Real Real))
      (𝓡 3) ∞
      (fun input : positiveHemisphereInteriorOpen × Real => input.1) :=
    contMDiff_fst
  have hOpenVal : ContMDiff (𝓡 3) (𝓡 3) ∞
      (Subtype.val : positiveHemisphereInteriorOpen → UnitThreeSphere) :=
    contMDiff_subtype_val
  have hRaw : ContMDiff (𝓡 3) (modelWithCornersSelf Real (Fin 4 → Real)) ∞
      (unitThreeSphereRawCoordinates ∘
        (Subtype.val : positiveHemisphereInteriorOpen → UnitThreeSphere)) :=
    unitThreeSphereRawCoordinates_contMDiff.comp hOpenVal
  have hLatitude : ContMDiff
      ((𝓡 3).prod
        (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun input : positiveHemisphereInteriorOpen × Real => input.1.1.1 0) :=
    ((ContinuousLinearMap.proj (R := Real) (0 : Fin 4) :
      (Fin 4 → Real) →L[Real] Real).contDiff.contMDiff.comp
        (hRaw.comp hFst)).congr fun input => by
          change input.1.1.1 0 = unitThreeSphereRawCoordinates input.1.1 0
          rw [unitThreeSphereRawCoordinates_eq]
  exact (hLatitude.comp hTo).congr fun _ => rfl

def smoothCutBulkOpenCapLatitude :
    SmoothCutBulkOpenCap period hPeriod → Real :=
  P0EFTJanusMappingTorusEquivariantSmoothDescent4D.mappingTorusInvariantMap
    (cutBulkOpenCapData period hPeriod)
    (cutBulkOpenCapLatitudeCover period hPeriod)
    (cutBulkOpenCapLatitudeCover_invariant period hPeriod)

private theorem smoothCutBulkOpenCapLatitude_contMDiff :
    letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
      cutBulkOpenCapCoverChartedSpace period hPeriod
    letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
      cutBulkOpenCapQuotientChartedSpace period hPeriod
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (smoothCutBulkOpenCapLatitude period hPeriod) := by
  letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  intro cap
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective (cutBulkOpenCapData period hPeriod) cap
  have hAt :=
    (cutBulkOpenCap_projection_isLocalDiffeomorph period hPeriod) coverPoint
  have hLocal : ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (cutBulkOpenCapLatitudeCover period hPeriod ∘ hAt.localInverse)
      (mappingTorusMk (cutBulkOpenCapData period hPeriod) coverPoint) :=
    (cutBulkOpenCapLatitudeCover_contMDiff period hPeriod).contMDiffAt.comp _
      (hAt.localInverse_contMDiffAt.of_le (by simp))
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' :
      mappingTorusMk (cutBulkOpenCapData period hPeriod) (hAt.localInverse point) =
        point := by
    simpa [Function.comp_def] using hPoint
  calc
    smoothCutBulkOpenCapLatitude period hPeriod point =
        smoothCutBulkOpenCapLatitude period hPeriod
          (mappingTorusMk (cutBulkOpenCapData period hPeriod)
            (hAt.localInverse point)) := congrArg _ hPoint'.symm
    _ = cutBulkOpenCapLatitudeCover period hPeriod (hAt.localInverse point) := rfl

private theorem smoothCutBulkOpenCapLatitude_eq_bulk
    (cap : SmoothCutBulkOpenCap period hPeriod) :
    smoothCutBulkOpenCapLatitude period hPeriod cap =
      cutBulkLatitudeCoordinate period hPeriod
        (smoothCutBulkOpenCapToCutBulk period hPeriod cap) := by
  refine Quotient.inductionOn cap ?_
  intro point
  rfl

private theorem smoothCutBulkOpenCapHomeomorph_symm_toCutBulk
    (cap : CutBulkOpenCap period hPeriod) :
    smoothCutBulkOpenCapToCutBulk period hPeriod
        ((smoothCutBulkOpenCapHomeomorph period hPeriod).symm cap) = cap.1 := by
  exact congrArg Subtype.val
    ((smoothCutBulkOpenCapHomeomorph period hPeriod).apply_symm_apply cap)

theorem cutBulkLatitudeCoordinate_intrinsicOpenCap_contMDiff :
    letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
      intrinsicCutBulkOpenCapChartedSpace period hPeriod
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun cap : CutBulkOpenCap period hPeriod =>
        cutBulkLatitudeCoordinate period hPeriod cap.1) := by
  letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  have h := (smoothCutBulkOpenCapLatitude_contMDiff period hPeriod).comp
    ((smoothCapHomeomorph_symm_contMDiff period hPeriod).of_le (by simp))
  apply h.congr
  intro cap
  change cutBulkLatitudeCoordinate period hPeriod cap.1 =
    smoothCutBulkOpenCapLatitude period hPeriod
      ((smoothCutBulkOpenCapHomeomorph period hPeriod).symm cap)
  rw [smoothCutBulkOpenCapLatitude_eq_bulk]
  exact congrArg (cutBulkLatitudeCoordinate period hPeriod)
    (smoothCutBulkOpenCapHomeomorph_symm_toCutBulk period hPeriod cap).symm

theorem cutBulkLatitudeCoordinate_openCollar_contMDiff :
    ContMDiff cutCollarModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun parameter : CutThroatOpenCollar period hPeriod =>
        cutBulkLatitudeCoordinate period hPeriod
          (cutOpenCollarAttachment period hPeriod parameter)) := by
  have hNormal : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun parameter : CutThroatFiniteCollar period hPeriod => parameter.2.1) :=
    contMDiff_subtype_coe_Icc.comp contMDiff_snd
  have hSin := (Real.contDiff_sin.contMDiff.comp hNormal).comp
    ((cutThroatOpenCollar_val_contMDiff period hPeriod).of_le (by simp))
  exact hSin.congr fun parameter =>
    cutBulkLatitudeCoordinate_cutCollarAttachment period hPeriod parameter.1

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
  exact congrArg function (Φ.right_inv hPoint).symm

/-- The positive latitude is `C∞` in the preferred global cut-bulk atlas. -/
theorem cutBulkLatitudeCoordinate_contMDiff :
    letI := cutBulkGlobalChartedSpace period hPeriod
    ContMDiff cutCollarModelWithCorners (modelWithCornersSelf Real Real) ∞
      (cutBulkLatitudeCoordinate period hPeriod) := by
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  have hCapStandard :=
    cutBulkLatitudeCoordinate_intrinsicOpenCap_contMDiff period hPeriod
  letI : ChartedSpace CutCollarModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
  have hCap : ContMDiff cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun cap : CutBulkOpenCap period hPeriod =>
        cutBulkLatitudeCoordinate period hPeriod cap.1) :=
    hCapStandard.comp
      (intrinsicCapCommonToStandard_contMDiff period hPeriod)

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
    (cutBulkLatitudeCoordinate period hPeriod) hCap
  have hCapOn : ContMDiffOn cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (cutBulkLatitudeCoordinate period hPeriod)
      (cutBulkOpenCap period hPeriod) := by
    apply hCapOnTarget.mono
    intro point hPoint
    change point ∈
      (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod).target
    rw [cutBulkOpenCapInclusionPartialHomeomorph,
      IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨⟨point, hPoint⟩, rfl⟩

  have hCollar := cutBulkLatitudeCoordinate_openCollar_contMDiff period hPeriod
  have hCollarOnTarget := contMDiffOn_target_of_partialDiffeomorph
    (cutOpenCollarAttachmentPartialDiffeomorph period hPeriod)
    (cutBulkLatitudeCoordinate period hPeriod) hCollar
  have hCollarOn : ContMDiffOn cutCollarModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (cutBulkLatitudeCoordinate period hPeriod)
      (Set.range (cutOpenCollarAttachment period hPeriod)) := by
    simpa [cutOpenCollarAttachmentPartialDiffeomorph,
      cutOpenCollarAttachmentPartialHomeomorph,
      IsOpenEmbedding.toOpenPartialHomeomorph_target] using hCollarOnTarget

  exact contMDiff_of_contMDiffOn_union_of_isOpen hCollarOn hCapOn
    (openCollar_union_openCap period hPeriod)
    (isOpen_range_cutOpenCollarAttachment period hPeriod)
    (isOpen_cutBulkOpenCap period hPeriod)

end
end P0EFTJanusMappingTorusCutBulkLatitudeGlobalSmooth4D
end JanusFormal
