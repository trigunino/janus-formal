import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquivariantSmoothDescent4D

/-!
# Smooth cutoff current on the open cut-bulk cap

The descended bulk current is analytic on the intrinsic positive-latitude cap.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCapSmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
open P0EFTJanusMappingTorusCutBulkOpenCapIdentification4D
open P0EFTJanusMappingTorusCutBulkIntrinsicOpenCapSmooth4D
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev OpenCapCover :=
  MappingTorusCover (cutBulkOpenCapData period hPeriod)

def cutBulkOpenCapScalarCurrentCover
    (field test : SmoothQuotientField period hPeriod Real)
    (point : OpenCapCover period hPeriod) : Real :=
  cutBulkScalarCurrentCover period hPeriod field test
    (cutBulkOpenCapCoverInclusion period hPeriod point)

private theorem cutBulkOpenCapScalarCurrentCover_invariant
    (field test : SmoothQuotientField period hPeriod Real)
    (winding : Int) (point : OpenCapCover period hPeriod) :
    cutBulkOpenCapScalarCurrentCover period hPeriod field test (winding +ᵥ point) =
      cutBulkOpenCapScalarCurrentCover period hPeriod field test point := by
  rw [cutBulkOpenCapScalarCurrentCover,
    cutBulkOpenCapCoverInclusion_equivariant]
  exact cutBulkScalarCurrentCover_invariant
    period hPeriod field test winding _

private theorem cutBulkOpenCapScalarCurrentCover_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
      cutBulkOpenCapCoverChartedSpace period hPeriod
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (cutBulkOpenCapScalarCurrentCover period hPeriod field test) := by
  letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
    cutBulkOpenCapCoverChartedSpace period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
    (coverHomeomorphProd (cutBulkOpenCapData period hPeriod))
  have hInput : ContMDiff coverModelWithCorners coverModelWithCorners ∞
      (Prod.map (Subtype.val : positiveHemisphereInteriorOpen → UnitThreeSphere)
        (id : Real → Real)) :=
    contMDiff_subtype_val.prodMap contMDiff_id
  exact (equatorialBandScalarCurrentZeroExtension_contMDiff
      period hPeriod field test).comp (hInput.comp hTo)

def smoothCutBulkOpenCapScalarCurrent
    (field test : SmoothQuotientField period hPeriod Real) :
    SmoothCutBulkOpenCap period hPeriod → Real :=
  mappingTorusInvariantMap (cutBulkOpenCapData period hPeriod)
    (cutBulkOpenCapScalarCurrentCover period hPeriod field test)
    (cutBulkOpenCapScalarCurrentCover_invariant period hPeriod field test)

theorem smoothCutBulkOpenCapScalarCurrent_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    letI : ChartedSpace CoverModel (OpenCapCover period hPeriod) :=
      cutBulkOpenCapCoverChartedSpace period hPeriod
    letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
      cutBulkOpenCapQuotientChartedSpace period hPeriod
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (smoothCutBulkOpenCapScalarCurrent period hPeriod field test) := by
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
  have hLocal : ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (cutBulkOpenCapScalarCurrentCover period hPeriod field test ∘
        hAt.localInverse)
      (mappingTorusMk (cutBulkOpenCapData period hPeriod) coverPoint) :=
    (cutBulkOpenCapScalarCurrentCover_contMDiff period hPeriod field test)
      |>.contMDiffAt.comp _ (hAt.localInverse_contMDiffAt.of_le (by simp))
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' :
      mappingTorusMk (cutBulkOpenCapData period hPeriod) (hAt.localInverse point) =
        point := by
    simpa [Function.comp_def] using hPoint
  calc
    smoothCutBulkOpenCapScalarCurrent period hPeriod field test point =
        smoothCutBulkOpenCapScalarCurrent period hPeriod field test
          (mappingTorusMk (cutBulkOpenCapData period hPeriod)
            (hAt.localInverse point)) := congrArg _ hPoint'.symm
    _ = cutBulkOpenCapScalarCurrentCover period hPeriod field test
        (hAt.localInverse point) := rfl

theorem smoothCutBulkOpenCapScalarCurrent_eq_bulk
    (field test : SmoothQuotientField period hPeriod Real)
    (cap : SmoothCutBulkOpenCap period hPeriod) :
    smoothCutBulkOpenCapScalarCurrent period hPeriod field test cap =
      cutBulkScalarCurrent period hPeriod field test
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

/-- The global bulk current is smooth after restriction to the intrinsic cap. -/
theorem cutBulkScalarCurrent_intrinsicOpenCap_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    letI : ChartedSpace CoverModel (CutBulkOpenCap period hPeriod) :=
      intrinsicCutBulkOpenCapChartedSpace period hPeriod
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun cap : CutBulkOpenCap period hPeriod ↦
        cutBulkScalarCurrent period hPeriod field test cap.1) := by
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
  have h := (smoothCutBulkOpenCapScalarCurrent_contMDiff
      period hPeriod field test).comp
    ((smoothCapHomeomorph_symm_contMDiff period hPeriod).of_le (by simp))
  apply h.congr
  intro cap
  change cutBulkScalarCurrent period hPeriod field test cap.1 =
    smoothCutBulkOpenCapScalarCurrent period hPeriod field test
      ((smoothCutBulkOpenCapHomeomorph period hPeriod).symm cap)
  rw [smoothCutBulkOpenCapScalarCurrent_eq_bulk]
  exact congrArg (cutBulkScalarCurrent period hPeriod field test)
    (smoothCutBulkOpenCapHomeomorph_symm_toCutBulk period hPeriod cap).symm

end
end P0EFTJanusMappingTorusCutBulkScalarCurrentOpenCapSmooth4D
end JanusFormal
