import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkToAmbientOpenCollarSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D

/-!
# Smoothness of the cut-bulk map on the intrinsic open cap
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkToAmbientOpenCapSmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
open P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev OpenCapCover :=
  MappingTorusCover (cutBulkOpenCapData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

/-- Cover formula for the cut-bulk map on the strict positive cap. -/
def cutBulkOpenCapToAmbientCover
    (point : OpenCapCover period hPeriod) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (reflectedSphereData period hPeriod)
    (cutBulkCoverToAmbient period hPeriod
      (cutBulkOpenCapCoverInclusion period hPeriod point))

private theorem cutBulkOpenCapToAmbientCover_invariant
    (winding : Int) (point : OpenCapCover period hPeriod) :
    cutBulkOpenCapToAmbientCover period hPeriod (winding +ᵥ point) =
      cutBulkOpenCapToAmbientCover period hPeriod point := by
  rw [cutBulkOpenCapToAmbientCover,
    cutBulkOpenCapCoverInclusion_equivariant,
    cutBulkCoverToAmbient_even_equivariant]
  apply (mappingTorusMk_eq_iff_exists_vadd
    (reflectedSphereData period hPeriod) _ _).2
  exact ⟨2 * winding, rfl⟩

private theorem cutBulkOpenCapToAmbientCover_contMDiff :
    letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
      cutBulkOpenCapCoverChartedSpace period hPeriod
    ContMDiff coverModelWithCorners coverModelWithCorners ∞
      (cutBulkOpenCapToAmbientCover period hPeriod) := by
  letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
    (coverHomeomorphProd (cutBulkOpenCapData period hPeriod))
  have hInput : ContMDiff coverModelWithCorners coverModelWithCorners ∞
      (Prod.map (Subtype.val : positiveHemisphereInteriorOpen → UnitThreeSphere)
        (id : Real → Real)) :=
    contMDiff_subtype_val.prodMap contMDiff_id
  have hCover := (chartedSpacePullback_invFun_contMDiff coverModelWithCorners ∞
    (coverHomeomorphProd (reflectedSphereData period hPeriod))).comp
      (hInput.comp hTo)
  exact (((reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
    |>.of_le (by simp)).comp hCover).congr fun _ ↦ rfl

/-- Smooth cap quotient map before transport to the intrinsic cap subtype. -/
def smoothCutBulkOpenCapToAmbient :
    SmoothCutBulkOpenCap period hPeriod → EffectiveQuotient period hPeriod :=
  mappingTorusInvariantMap (cutBulkOpenCapData period hPeriod)
    (cutBulkOpenCapToAmbientCover period hPeriod)
    (cutBulkOpenCapToAmbientCover_invariant period hPeriod)

theorem smoothCutBulkOpenCapToAmbient_contMDiff :
    letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
      cutBulkOpenCapCoverChartedSpace period hPeriod
    letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
      cutBulkOpenCapQuotientChartedSpace period hPeriod
    ContMDiff coverModelWithCorners coverModelWithCorners ∞
      (smoothCutBulkOpenCapToAmbient period hPeriod) := by
  letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (SmoothCutBulkOpenCap period hPeriod) :=
    smoothCutBulkOpenCap_isManifold period hPeriod
  intro cap
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective (cutBulkOpenCapData period hPeriod) cap
  have hAt :=
    (cutBulkOpenCap_projection_isLocalDiffeomorph period hPeriod) coverPoint
  have hLocal : ContMDiffAt coverModelWithCorners coverModelWithCorners ∞
      (cutBulkOpenCapToAmbientCover period hPeriod ∘ hAt.localInverse)
      (mappingTorusMk (cutBulkOpenCapData period hPeriod) coverPoint) :=
    (cutBulkOpenCapToAmbientCover_contMDiff period hPeriod)
      |>.contMDiffAt.comp _ (hAt.localInverse_contMDiffAt.of_le (by simp))
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' :
      mappingTorusMk (cutBulkOpenCapData period hPeriod) (hAt.localInverse point) =
        point := by
    simpa [Function.comp_def] using hPoint
  calc
    smoothCutBulkOpenCapToAmbient period hPeriod point =
        smoothCutBulkOpenCapToAmbient period hPeriod
          (mappingTorusMk (cutBulkOpenCapData period hPeriod)
            (hAt.localInverse point)) := congrArg _ hPoint'.symm
    _ = cutBulkOpenCapToAmbientCover period hPeriod
        (hAt.localInverse point) := rfl

theorem smoothCutBulkOpenCapToAmbient_eq_bulk
    (cap : SmoothCutBulkOpenCap period hPeriod) :
    smoothCutBulkOpenCapToAmbient period hPeriod cap =
      cutBulkToAmbient period hPeriod
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

theorem cutBulkToAmbient_intrinsicOpenCap_contMDiff :
    letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
      intrinsicCutBulkOpenCapChartedSpace period hPeriod
    ContMDiff coverModelWithCorners coverModelWithCorners ∞
      (fun cap : CutBulkOpenCap period hPeriod ↦
        cutBulkToAmbient period hPeriod cap.1) := by
  letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (SmoothCutBulkOpenCap period hPeriod) :=
    smoothCutBulkOpenCap_isManifold period hPeriod
  letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
    intrinsicCutBulkOpenCapChartedSpace period hPeriod
  have h := (smoothCutBulkOpenCapToAmbient_contMDiff period hPeriod).comp
    ((smoothCapHomeomorph_symm_contMDiff period hPeriod).of_le (by simp))
  apply h.congr
  intro cap
  change cutBulkToAmbient period hPeriod cap.1 =
    smoothCutBulkOpenCapToAmbient period hPeriod
      ((smoothCutBulkOpenCapHomeomorph period hPeriod).symm cap)
  rw [smoothCutBulkOpenCapToAmbient_eq_bulk]
  exact congrArg (cutBulkToAmbient period hPeriod)
    (smoothCutBulkOpenCapHomeomorph_symm_toCutBulk period hPeriod cap).symm

end
end P0EFTJanusMappingTorusCutBulkToAmbientOpenCapSmooth4D
end JanusFormal
