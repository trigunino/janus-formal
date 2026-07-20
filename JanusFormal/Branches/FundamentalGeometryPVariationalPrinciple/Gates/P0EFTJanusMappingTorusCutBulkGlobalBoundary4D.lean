import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatOpenCollarBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonBoundaryless4D

/-! # Exact manifold boundary of the global cut bulk -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkGlobalBoundary4D

set_option autoImplicit false
noncomputable section
local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusCutBulkCollarRemainderDecomposition4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatLatitudeCollarAttachment4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutThroatOpenCollarEmbedding4D
open P0EFTJanusMappingTorusCutThroatOpenCollarSmooth4D
open P0EFTJanusMappingTorusCutThroatOpenCollarBoundary4D
open P0EFTJanusMappingTorusCutBulkOpenAtlasCover4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonModel4D
open P0EFTJanusMappingTorusCutBulkIntrinsicCapCommonBoundaryless4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D

private theorem isBoundaryPoint_iff_of_liftedChart
    {E H A M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H] [TopologicalSpace A] [TopologicalSpace M]
    (I : ModelWithCorners Real E H)
    [ChartedSpace H A] [IsManifold I ∞ A]
    [ChartedSpace H M] [IsManifold I ∞ M]
    (embedding : OpenPartialHomeomorph A M)
    (hSource : embedding.source = Set.univ)
    (point : A) (target : M) (hTarget : embedding point = target)
    (hAtlas : embedding.symm.trans (chartAt H point) ∈ atlas H M) :
    I.IsBoundaryPoint target ↔ I.IsBoundaryPoint point := by
  have hPointSource : point ∈ embedding.source := by rw [hSource]; trivial
  have hInverse : embedding.symm target = point := by
    rw [← hTarget]
    exact embedding.left_inv hPointSource
  let lifted := embedding.symm.trans (chartAt H point)
  have hLiftedSource : target ∈ lifted.source := by
    change target ∈ (embedding.symm.trans (chartAt H point)).source
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rw [OpenPartialHomeomorph.symm_source]
      simpa [hTarget] using embedding.map_source hPointSource
    · change embedding.symm target ∈ (chartAt H point).source
      rw [hInverse]
      exact mem_chart_source H point
  have hLiftedTarget : lifted.target = (chartAt H point).target := by
    change (embedding.symm.trans (chartAt H point)).target = _
    rw [OpenPartialHomeomorph.trans_target]
    simp [hSource]
  have hLiftedApply : lifted target = chartAt H point point := by
    change chartAt H point (embedding.symm target) = chartAt H point point
    rw [hInverse]
  rw [I.isBoundaryPoint_iff_of_mem_atlas (n := ∞) (by simp)
      hAtlas hLiftedSource,
    I.isBoundaryPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas H point) (mem_chart_source H point)]
  rw [OpenPartialHomeomorph.extend_target,
    OpenPartialHomeomorph.extend_target, hLiftedTarget]
  change I (lifted target) ∈ _ ↔ I (chartAt H point point) ∈ _
  rw [hLiftedApply]

variable (period : Real) (hPeriod : period ≠ 0)

/-- A global point is a manifold-boundary point exactly when its intrinsic
latitude is zero. -/
theorem cutBulkGlobal_isBoundaryPoint_iff
    (bulk : PositiveHemisphereCutBulk period hPeriod) :
    letI := cutBulkGlobalChartedSpace period hPeriod
    cutCollarModelWithCorners.IsBoundaryPoint bulk ↔
      cutBulkLatitudeCoordinate period hPeriod bulk = 0 := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  letI : IsManifold cutCollarModelWithCorners ∞
      (PositiveHemisphereCutBulk period hPeriod) :=
    cutBulkGlobal_isManifold period hPeriod
  by_cases hCap : bulk ∈ cutBulkOpenCap period hPeriod
  · letI := intrinsicCutBulkOpenCapCommonChartedSpace period hPeriod
    letI : IsManifold cutCollarModelWithCorners ∞
        (CutBulkOpenCap period hPeriod) :=
      intrinsicCutBulkOpenCapCommon_isManifold period hPeriod
    letI : BoundarylessManifold cutCollarModelWithCorners
        (CutBulkOpenCap period hPeriod) :=
      intrinsicCutBulkOpenCapCommon_boundaryless period hPeriod
    let capPoint : CutBulkOpenCap period hPeriod := ⟨bulk, hCap⟩
    have hAtlas : liftedCutBulkCapChart period hPeriod capPoint ∈
        atlas CutCollarModel (PositiveHemisphereCutBulk period hPeriod) := by
      change liftedCutBulkCapChart period hPeriod capPoint ∈
        Set.range (cutBulkGlobalChartAt period hPeriod)
      exact ⟨bulk, by simp [cutBulkGlobalChartAt, hCap, capPoint]⟩
    have hBoundary := isBoundaryPoint_iff_of_liftedChart
      cutCollarModelWithCorners
      (cutBulkOpenCapInclusionPartialHomeomorph period hPeriod)
      (by simp [cutBulkOpenCapInclusionPartialHomeomorph])
      capPoint bulk rfl (by simpa [liftedCutBulkCapChart] using hAtlas)
    constructor
    · intro hBulk
      have hLocal := hBoundary.mp hBulk
      change capPoint ∈ cutCollarModelWithCorners.boundary
        (CutBulkOpenCap period hPeriod) at hLocal
      rw [ModelWithCorners.Boundaryless.boundary_eq_empty] at hLocal
      exact False.elim hLocal
    · intro hZero
      exact False.elim ((ne_of_gt hCap) hZero)
  · have hRange : bulk ∈
        Set.range (cutOpenCollarAttachment period hPeriod) := by
      have hCover := openCollar_union_openCap period hPeriod
      have hMembership : bulk ∈
          Set.range (cutOpenCollarAttachment period hPeriod) ∪
            cutBulkOpenCap period hPeriod := by rw [hCover]; trivial
      exact hMembership.resolve_right hCap
    let collarPoint : CutThroatOpenCollar period hPeriod :=
      (cutOpenCollarAttachmentPartialHomeomorph period hPeriod).symm bulk
    have hTargetRange : bulk ∈
        (cutOpenCollarAttachmentPartialHomeomorph period hPeriod).target := by
      rw [cutOpenCollarAttachmentPartialHomeomorph,
        IsOpenEmbedding.toOpenPartialHomeomorph_target]
      exact hRange
    have hAttach : cutOpenCollarAttachment period hPeriod collarPoint = bulk := by
      exact (cutOpenCollarAttachmentPartialHomeomorph period hPeriod).right_inv
        hTargetRange
    letI := cutThroatOpenCollarChartedSpace period hPeriod
    letI : IsManifold cutCollarModelWithCorners ∞
        (CutThroatOpenCollar period hPeriod) :=
      (cutThroatOpenCollar_isManifold period hPeriod).of_le le_top
    have hAtlas : liftedCutBulkCollarChart period hPeriod collarPoint ∈
        atlas CutCollarModel (PositiveHemisphereCutBulk period hPeriod) := by
      change liftedCutBulkCollarChart period hPeriod collarPoint ∈
        Set.range (cutBulkGlobalChartAt period hPeriod)
      exact ⟨bulk, by simp [cutBulkGlobalChartAt, hCap, collarPoint]⟩
    have hBoundary := isBoundaryPoint_iff_of_liftedChart
      cutCollarModelWithCorners
      (cutOpenCollarAttachmentPartialHomeomorph period hPeriod)
      (by simp [cutOpenCollarAttachmentPartialHomeomorph])
      collarPoint bulk (by
        simpa [cutOpenCollarAttachmentPartialHomeomorph] using hAttach)
      (by simpa [liftedCutBulkCollarChart] using hAtlas)
    have hZero : cutBulkLatitudeCoordinate period hPeriod bulk = 0 :=
      le_antisymm (le_of_not_gt hCap)
        (cutBulkLatitudeCoordinate_nonneg period hPeriod bulk)
    have hSin : Real.sin collarPoint.1.2.1 = 0 := by
      rw [← hZero, ← hAttach]
      exact (cutBulkLatitudeCoordinate_cutCollarAttachment period hPeriod
        collarPoint.1).symm
    have hNormal : collarPoint.1.2 = ⊥ := by
      apply Subtype.ext
      have hZeroRange : (0 : Real) ∈
          Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      have hNormalRange : collarPoint.1.2.1 ∈
          Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [collarPoint.1.2.2.1,
          collarPoint.1.2.2.2, Real.pi_gt_three]
      exact Real.strictMonoOn_sin.injOn hNormalRange hZeroRange (by
        simpa using hSin)
    have hLocalBoundary : cutCollarModelWithCorners.IsBoundaryPoint collarPoint := by
      change collarPoint ∈ cutCollarModelWithCorners.boundary
        (CutThroatOpenCollar period hPeriod)
      rw [cutThroatOpenCollar_boundary period hPeriod]
      exact hNormal
    constructor
    · exact fun _ => hZero
    · exact fun _ => hBoundary.mpr hLocalBoundary

theorem cutBulkGlobal_boundary_eq_zeroLatitude :
    letI := cutBulkGlobalChartedSpace period hPeriod
    cutCollarModelWithCorners.boundary
        (PositiveHemisphereCutBulk period hPeriod) =
      (cutBulkLatitudeCoordinate period hPeriod) ⁻¹' {0} := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  ext bulk
  exact cutBulkGlobal_isBoundaryPoint_iff period hPeriod bulk

theorem cutBulkLatitudeCoordinate_cutBoundaryInclusion
    (boundary : CutThroatBoundary period hPeriod) :
    cutBulkLatitudeCoordinate period hPeriod
      (cutBoundaryInclusion period hPeriod boundary) = 0 := by
  rw [← cutCollarAttachment_cutThroatFace period hPeriod boundary,
    cutBulkLatitudeCoordinate_cutCollarAttachment]
  simp [cutThroatFace]

theorem range_cutBoundaryInclusion_eq_zeroLatitude :
    Set.range (cutBoundaryInclusion period hPeriod) =
      (cutBulkLatitudeCoordinate period hPeriod) ⁻¹' {0} := by
  ext bulk
  constructor
  · rintro ⟨boundary, rfl⟩
    exact cutBulkLatitudeCoordinate_cutBoundaryInclusion period hPeriod boundary
  · intro hZero
    change cutBulkLatitudeCoordinate period hPeriod bulk = 0 at hZero
    have hCollar : bulk ∈
        Set.range (cutOpenCollarAttachment period hPeriod) := by
      rw [range_cutOpenCollarAttachment]
      change cutBulkLatitudeCoordinate period hPeriod bulk < Real.sin 1
      rw [hZero]
      exact Real.sin_pos_of_pos_of_lt_pi (by norm_num)
        (by linarith [Real.pi_gt_three])
    rcases hCollar with ⟨point, hAttach⟩
    have hSin : Real.sin point.1.2.1 = 0 := by
      rw [← hZero, ← hAttach]
      exact (cutBulkLatitudeCoordinate_cutCollarAttachment period hPeriod
        point.1).symm
    have hNormal : point.1.2 = ⊥ := by
      apply Subtype.ext
      have hZeroRange : (0 : Real) ∈
          Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [Real.pi_pos]
      have hNormalRange : point.1.2.1 ∈
          Icc (-(Real.pi / 2)) (Real.pi / 2) := by
        constructor <;> linarith [point.1.2.2.1, point.1.2.2.2,
          Real.pi_gt_three]
      exact Real.strictMonoOn_sin.injOn hNormalRange hZeroRange (by
        simpa using hSin)
    refine ⟨point.1.1, ?_⟩
    rw [← cutCollarAttachment_cutThroatFace period hPeriod point.1.1,
      ← hAttach]
    congr 1
    exact Prod.ext rfl hNormal.symm

/-- The intrinsic manifold boundary is exactly the embedded orientation-double
throat. -/
theorem cutBulkGlobal_boundary_eq_range_cutBoundaryInclusion :
    letI := cutBulkGlobalChartedSpace period hPeriod
    cutCollarModelWithCorners.boundary
        (PositiveHemisphereCutBulk period hPeriod) =
      Set.range (cutBoundaryInclusion period hPeriod) := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  rw [cutBulkGlobal_boundary_eq_zeroLatitude,
    range_cutBoundaryInclusion_eq_zeroLatitude]

end
end P0EFTJanusMappingTorusCutBulkGlobalBoundary4D
end JanusFormal
