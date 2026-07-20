import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkLatitudeGlobalSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Global smooth canonical cutoff on the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCanonicalCutoffGlobalSmooth4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkLatitudeBand4D
open P0EFTJanusMappingTorusCutBulkCollarRemainderDecomposition4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkLatitudeGlobalSmooth4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentCollarCoordinateBridge4D
open P0EFTJanusMappingTorusCutBulkScalarCurrentNormalDivergenceBridge4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem cutBulkLatitudeCoordinate_le_one
    (point : PositiveHemisphereCutBulk period hPeriod) :
    cutBulkLatitudeCoordinate period hPeriod point ≤ 1 := by
  refine Quotient.inductionOn point ?_
  intro cover
  change cover.fiber.1.1 0 ≤ 1
  have hTerm : (cover.fiber.1.1 0) ^ 2 ≤
      radiusSquared cover.fiber.1.1 := by
    unfold radiusSquared
    exact Finset.single_le_sum (fun index _ => sq_nonneg (cover.fiber.1.1 index))
      (Finset.mem_univ 0)
  have hSphere := cover.fiber.1.2
  unfold OnUnitThreeSphere at hSphere
  rw [hSphere] at hTerm
  nlinarith [cover.fiber.2]

/-- The global cutoff is the canonical latitude bump evaluated at the
positive normal coordinate `arcsin(latitude)`. -/
def cutBulkCanonicalCutoff
    (point : PositiveHemisphereCutBulk period hPeriod) : Real :=
  canonicalLatitudeCollarCutoff
    (Real.arcsin (cutBulkLatitudeCoordinate period hPeriod point))

theorem cutBulkCanonicalCutoff_canonicalLatitudeCutBulkCollarMap
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Icc (0 : Real) 1) :
    cutBulkCanonicalCutoff period hPeriod
        (canonicalLatitudeCutBulkCollarMap period hPeriod (base, normal)) =
      canonicalLatitudeCollarCutoff normal := by
  unfold cutBulkCanonicalCutoff canonicalLatitudeCutBulkCollarMap
    canonicalLatitudeCutBulkCollarPath canonicalLatitudeCutBulkCollarLift
  rw [cutBulkLatitudeCoordinate_cutCollarAttachment]
  simp only [Set.projIcc_of_mem zero_le_one hNormal]
  rw [Real.arcsin_sin (by linarith [hNormal.1, Real.pi_gt_three])
    (by linarith [hNormal.2, Real.pi_gt_three])]

private theorem sin_one_lt_one : Real.sin 1 < 1 := by
  have hOne : (1 : Real) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_gt_three]
  have hPi : Real.pi / 2 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  simpa using Real.strictMonoOn_sin hOne hPi
    (by linarith [Real.pi_gt_three])

private theorem cutBulkCanonicalCutoff_eq_zero_of_sin_one_lt_latitude
    (point : PositiveHemisphereCutBulk period hPeriod)
    (hPoint : Real.sin 1 < cutBulkLatitudeCoordinate period hPeriod point) :
    cutBulkCanonicalCutoff period hPeriod point = 0 := by
  apply canonicalLatitudeCollarCutoff_eq_zero_of_one_le_abs
  have hOne : (1 : Real) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_gt_three]
  have hRange : cutBulkLatitudeCoordinate period hPeriod point ∈ Icc (-1 : Real) 1 :=
    ⟨by linarith [cutBulkLatitudeCoordinate_nonneg period hPeriod point],
      cutBulkLatitudeCoordinate_le_one period hPeriod point⟩
  have hArc : 1 < Real.arcsin (cutBulkLatitudeCoordinate period hPeriod point) :=
    (Real.lt_arcsin_iff_sin_lt hOne hRange).2 hPoint
  exact hArc.le.trans (le_abs_self _)

/-- The canonical cutoff is `C∞` in the preferred global cut-bulk atlas. -/
theorem cutBulkCanonicalCutoff_contMDiff :
    letI := cutBulkGlobalChartedSpace period hPeriod
    ContMDiff cutCollarModelWithCorners (modelWithCornersSelf Real Real) ∞
      (cutBulkCanonicalCutoff period hPeriod) := by
  letI := cutBulkGlobalChartedSpace period hPeriod
  intro point
  by_cases hPole : cutBulkLatitudeCoordinate period hPeriod point = 1
  · have hLatitudeContinuous :=
      (cutBulkLatitudeCoordinate_contMDiff period hPeriod).continuous
    have hOpen : IsOpen
        {nearby : PositiveHemisphereCutBulk period hPeriod |
          Real.sin 1 < cutBulkLatitudeCoordinate period hPeriod nearby} :=
      isOpen_lt continuous_const hLatitudeContinuous
    have hThreshold : Real.sin 1 <
        cutBulkLatitudeCoordinate period hPeriod point := by
      rw [hPole]
      exact sin_one_lt_one
    have hEventuallyZero :
        cutBulkCanonicalCutoff period hPeriod =ᶠ[𝓝 point] (fun _ => 0) := by
      filter_upwards [hOpen.mem_nhds hThreshold] with nearby hNearby
      exact cutBulkCanonicalCutoff_eq_zero_of_sin_one_lt_latitude
        period hPeriod nearby hNearby
    exact contMDiffAt_const.congr_of_eventuallyEq hEventuallyZero
  · have hNonneg := cutBulkLatitudeCoordinate_nonneg period hPeriod point
    have hMinus : cutBulkLatitudeCoordinate period hPeriod point ≠ -1 := by
      intro h
      linarith
    have hArc : ContDiffAt Real ∞ Real.arcsin
        (cutBulkLatitudeCoordinate period hPeriod point) :=
      Real.contDiffAt_arcsin hMinus hPole
    have hArcComposite : ContMDiffAt cutCollarModelWithCorners
        (modelWithCornersSelf Real Real) ∞
        (Real.arcsin ∘ cutBulkLatitudeCoordinate period hPeriod) point :=
      hArc.contMDiffAt.comp point
        (cutBulkLatitudeCoordinate_contMDiff period hPeriod).contMDiffAt
    exact canonicalLatitudeCollarCutoff_contDiff.contMDiff.contMDiffAt.comp point
      hArcComposite

end
end P0EFTJanusMappingTorusCutBulkCanonicalCutoffGlobalSmooth4D
end JanusFormal
