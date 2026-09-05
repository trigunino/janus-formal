import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowEuclideanSpan4D

/-! # Exact Euclidean reconstruction by the ten canonical flows -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowEuclideanReconstruction4D

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open scoped BigOperators
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D
open P0EFTJanusMappingTorusCanonicalTenFlowEuclideanSpan4D

/-- The Euclidean frame operator of the radial direction, the three spatial
rotations and the six phased normal rotations. -/
def canonicalEuclideanFlowFrameOperator
    (period time : Real) (point vector : EuclideanR4) : EuclideanR4 :=
  inner Real vector point • point +
    ∑ axis : Fin 3,
      inner Real vector (euclideanSpatialFlowGenerator axis point) •
        euclideanSpatialFlowGenerator axis point +
    ∑ axis : Fin 3, ∑ phase : Fin 2,
      inner Real vector
          (canonicalNormalRotationPhase period phase time •
            euclideanNormalFlowGenerator axis point) •
        (canonicalNormalRotationPhase period phase time •
          euclideanNormalFlowGenerator axis point)

/-- The ten-flow frame operator is exactly the squared-radius scalar. -/
theorem canonicalEuclideanFlowFrameOperator_eq
    (period time : Real) (point vector : EuclideanR4) :
    canonicalEuclideanFlowFrameOperator period time point vector =
      inner Real point point • vector := by
  have hNormal (axis : Fin 3) :
      (∑ phase : Fin 2,
        inner Real vector
            (canonicalNormalRotationPhase period phase time •
              euclideanNormalFlowGenerator axis point) •
          (canonicalNormalRotationPhase period phase time •
            euclideanNormalFlowGenerator axis point)) =
        inner Real vector (euclideanNormalFlowGenerator axis point) •
          euclideanNormalFlowGenerator axis point := by
    rw [show (∑ phase : Fin 2,
        inner Real vector
            (canonicalNormalRotationPhase period phase time •
              euclideanNormalFlowGenerator axis point) •
          (canonicalNormalRotationPhase period phase time •
            euclideanNormalFlowGenerator axis point)) =
        inner Real vector
            (canonicalNormalRotationPhase period 0 time •
              euclideanNormalFlowGenerator axis point) •
          (canonicalNormalRotationPhase period 0 time •
            euclideanNormalFlowGenerator axis point) +
        inner Real vector
            (canonicalNormalRotationPhase period 1 time •
              euclideanNormalFlowGenerator axis point) •
          (canonicalNormalRotationPhase period 1 time •
            euclideanNormalFlowGenerator axis point) by
      simp [Fin.sum_univ_succ]]
    simp only [real_inner_smul_right, smul_smul]
    rw [← add_smul]
    congr 1
    have hPhase :
        canonicalNormalRotationPhase period 0 time ^ 2 +
          canonicalNormalRotationPhase period 1 time ^ 2 = 1 := by
      simpa [Fin.sum_univ_succ] using
        canonicalNormalRotationPhase_square_sum period time
    calc
      canonicalNormalRotationPhase period 0 time *
            inner Real vector (euclideanNormalFlowGenerator axis point) *
            canonicalNormalRotationPhase period 0 time +
          canonicalNormalRotationPhase period 1 time *
            inner Real vector (euclideanNormalFlowGenerator axis point) *
            canonicalNormalRotationPhase period 1 time =
          (canonicalNormalRotationPhase period 0 time ^ 2 +
            canonicalNormalRotationPhase period 1 time ^ 2) *
              inner Real vector
                (euclideanNormalFlowGenerator axis point) := by ring
      _ = inner Real vector
          (euclideanNormalFlowGenerator axis point) := by rw [hPhase, one_mul]
  rw [canonicalEuclideanFlowFrameOperator]
  simp_rw [hNormal]
  rw [show inner Real point point = ‖point‖ ^ 2 by simp]
  rw [EuclideanSpace.real_norm_sq_eq]
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  fin_cases index <;>
    simp [euclideanSpatialFlowGenerator, euclideanNormalFlowGenerator,
      PiLp.inner_apply, Fin.sum_univ_succ] <;>
    ring

/-- Dividing by the nonzero squared radius gives an explicit right inverse
for the ten Euclidean generators. -/
theorem canonicalEuclideanFlow_normalized_reconstruction
    (period time : Real) (point vector : EuclideanR4) (hPoint : point ≠ 0) :
    (inner Real vector point / inner Real point point) • point +
      ∑ axis : Fin 3,
        (inner Real vector (euclideanSpatialFlowGenerator axis point) /
            inner Real point point) •
          euclideanSpatialFlowGenerator axis point +
      ∑ axis : Fin 3, ∑ phase : Fin 2,
        (inner Real vector
              (canonicalNormalRotationPhase period phase time •
                euclideanNormalFlowGenerator axis point) /
            inner Real point point) •
          (canonicalNormalRotationPhase period phase time •
            euclideanNormalFlowGenerator axis point) = vector := by
  have hRadius : inner Real point point ≠ 0 :=
    ne_of_gt (real_inner_self_pos.mpr hPoint)
  have hFrame := canonicalEuclideanFlowFrameOperator_eq
    period time point vector
  rw [canonicalEuclideanFlowFrameOperator] at hFrame
  apply smul_right_injective EuclideanR4 hRadius
  have hCancel (value : Real) :
      inner Real point point * (value / inner Real point point) = value := by
    field_simp
  have hCancelMul (value factor : Real) :
      inner Real point point *
          (value / inner Real point point * factor) = value * factor := by
    field_simp
  simp only [smul_add, Finset.smul_sum, smul_smul, hCancel, hCancelMul]
  simpa only [smul_smul] using hFrame

/-- Gate marker: the ten canonical Euclidean generators carry a concrete
normalized dual, not merely a pointwise spanning certificate. -/
theorem canonical_ten_flow_euclidean_reconstruction_gate
    (period time : Real) (point : EuclideanR4) (hPoint : point ≠ 0) :
    ∀ vector : EuclideanR4,
      (inner Real vector point / inner Real point point) • point +
        ∑ axis : Fin 3,
          (inner Real vector (euclideanSpatialFlowGenerator axis point) /
              inner Real point point) •
            euclideanSpatialFlowGenerator axis point +
        ∑ axis : Fin 3, ∑ phase : Fin 2,
          (inner Real vector
                (canonicalNormalRotationPhase period phase time •
                  euclideanNormalFlowGenerator axis point) /
              inner Real point point) •
            (canonicalNormalRotationPhase period phase time •
              euclideanNormalFlowGenerator axis point) = vector :=
  fun vector => canonicalEuclideanFlow_normalized_reconstruction
    period time point vector hPoint

end
end P0EFTJanusMappingTorusCanonicalTenFlowEuclideanReconstruction4D
end JanusFormal
