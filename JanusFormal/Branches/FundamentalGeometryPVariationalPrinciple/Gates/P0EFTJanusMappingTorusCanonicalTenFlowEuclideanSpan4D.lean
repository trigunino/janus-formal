import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowIPP4D

/-! # Euclidean spanning identity for the ten canonical flow directions -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowEuclideanSpan4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set Module
open scoped BigOperators
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D
open P0EFTJanusMappingTorusCanonicalTenFlowIPP4D

/-- The three ordinary spatial rotation generators on Euclidean four-space. -/
def euclideanSpatialFlowGenerator
    (axis : Fin 3) (point : EuclideanR4) : EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm <| match axis with
  | 0 => ![0, 0,
      -(EuclideanSpace.equiv (Fin 4) Real point 3),
      EuclideanSpace.equiv (Fin 4) Real point 2]
  | 1 => ![0,
      EuclideanSpace.equiv (Fin 4) Real point 3,
      0, -(EuclideanSpace.equiv (Fin 4) Real point 1)]
  | 2 => ![0,
      -(EuclideanSpace.equiv (Fin 4) Real point 2),
      EuclideanSpace.equiv (Fin 4) Real point 1, 0]

/-- The three reflected-spatial rotation generators on Euclidean four-space. -/
def euclideanNormalFlowGenerator
    (axis : Fin 3) (point : EuclideanR4) : EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm <| match axis with
  | 0 => ![-(EuclideanSpace.equiv (Fin 4) Real point 1),
      EuclideanSpace.equiv (Fin 4) Real point 0, 0, 0]
  | 1 => ![-(EuclideanSpace.equiv (Fin 4) Real point 2), 0,
      EuclideanSpace.equiv (Fin 4) Real point 0, 0]
  | 2 => ![-(EuclideanSpace.equiv (Fin 4) Real point 3), 0, 0,
      EuclideanSpace.equiv (Fin 4) Real point 0]

/-- Euclidean model of the ten generators at one cover time. -/
def canonicalEuclideanFlowGenerator
    (period time : Real) (point : EuclideanR4)
    (index : CanonicalFlowIndex) : EuclideanR4 :=
  match index with
  | .time => point
  | .spatial axis => euclideanSpatialFlowGenerator axis point
  | .phasedNormal axis phase =>
      canonicalNormalRotationPhase period phase time •
        euclideanNormalFlowGenerator axis point

/-- The radial direction and all six coordinate-plane rotations span ambient
four-space; the two phases recover each reflected-spatial rotation. -/
theorem canonicalEuclideanFlowGenerator_spans
    (period time : Real) (point : EuclideanR4) (hPoint : point ≠ 0) :
    Submodule.span Real
      (Set.range (canonicalEuclideanFlowGenerator period time point)) = ⊤ := by
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro vector hVector
  have hOrthogonal (index : CanonicalFlowIndex) :
      inner Real vector
        (canonicalEuclideanFlowGenerator period time point index) = 0 :=
    (Submodule.mem_orthogonal'
      (Submodule.span Real
        (Set.range (canonicalEuclideanFlowGenerator period time point)))
      vector).mp hVector _
        (Submodule.subset_span (Set.mem_range_self index))
  have hRadial := hOrthogonal CanonicalFlowIndex.time
  have hSpatialZero := hOrthogonal (CanonicalFlowIndex.spatial 0)
  have hSpatialOne := hOrthogonal (CanonicalFlowIndex.spatial 1)
  have hSpatialTwo := hOrthogonal (CanonicalFlowIndex.spatial 2)
  have hNormal (axis : Fin 3) :
      inner Real vector (euclideanNormalFlowGenerator axis point) = 0 := by
    let cosine := canonicalNormalRotationPhase period (0 : Fin 2) time
    let sine := canonicalNormalRotationPhase period (1 : Fin 2) time
    have hCosine : cosine *
        inner Real vector (euclideanNormalFlowGenerator axis point) = 0 := by
      have hRaw := hOrthogonal (CanonicalFlowIndex.phasedNormal axis 0)
      change inner Real vector
        (cosine • euclideanNormalFlowGenerator axis point) = 0 at hRaw
      rwa [real_inner_smul_right] at hRaw
    have hSine : sine *
        inner Real vector (euclideanNormalFlowGenerator axis point) = 0 := by
      have hRaw := hOrthogonal (CanonicalFlowIndex.phasedNormal axis 1)
      change inner Real vector
        (sine • euclideanNormalFlowGenerator axis point) = 0 at hRaw
      rwa [real_inner_smul_right] at hRaw
    have hPhase : cosine ^ 2 + sine ^ 2 = 1 := by
      simpa [cosine, sine, Fin.sum_univ_succ] using
        canonicalNormalRotationPhase_square_sum period time
    calc
      inner Real vector (euclideanNormalFlowGenerator axis point) =
          (cosine ^ 2 + sine ^ 2) *
            inner Real vector (euclideanNormalFlowGenerator axis point) := by
        rw [hPhase]
        ring
      _ = cosine * (cosine *
            inner Real vector (euclideanNormalFlowGenerator axis point)) +
          sine * (sine *
            inner Real vector (euclideanNormalFlowGenerator axis point)) := by
        ring
      _ = 0 := by rw [hCosine, hSine]; ring
  have hNormalZero := hNormal 0
  have hNormalOne := hNormal 1
  have hNormalTwo := hNormal 2
  have hNorm : 0 < inner Real point point := real_inner_self_pos.mpr hPoint
  simp only [canonicalEuclideanFlowGenerator] at hRadial hSpatialZero hSpatialOne hSpatialTwo
  simp [euclideanSpatialFlowGenerator, euclideanNormalFlowGenerator,
    PiLp.inner_apply, Fin.sum_univ_succ] at hRadial hSpatialZero hSpatialOne hSpatialTwo hNormalZero hNormalOne hNormalTwo hNorm
  let x0 := point.ofLp 0
  let x1 := point.ofLp 1
  let x2 := point.ofLp 2
  let x3 := point.ofLp 3
  let y0 := vector.ofLp 0
  let y1 := vector.ofLp 1
  let y2 := vector.ofLp 2
  let y3 := vector.ofLp 3
  have hRadial' : y0 * x0 + y1 * x1 + y2 * x2 + y3 * x3 = 0 := by
    dsimp [x0, x1, x2, x3, y0, y1, y2, y3]
    convert hRadial using 1 <;> ring
  have hSpatialZero' : -(y2 * x3) + y3 * x2 = 0 := by
    dsimp [x0, x1, x2, x3, y0, y1, y2, y3]
    convert hSpatialZero using 1 <;> ring
  have hSpatialOne' : y1 * x3 - y3 * x1 = 0 := by
    dsimp [x0, x1, x2, x3, y0, y1, y2, y3]
    convert hSpatialOne using 1 <;> ring
  have hSpatialTwo' : -(y1 * x2) + y2 * x1 = 0 := by
    dsimp [x0, x1, x2, x3, y0, y1, y2, y3]
    convert hSpatialTwo using 1 <;> ring
  have hNormalZero' : -(y0 * x1) + y1 * x0 = 0 := by
    dsimp [x0, x1, x2, x3, y0, y1, y2, y3]
    convert hNormalZero using 1 <;> ring
  have hNormalOne' : -(y0 * x2) + y2 * x0 = 0 := by
    dsimp [x0, x1, x2, x3, y0, y1, y2, y3]
    convert hNormalOne using 1 <;> ring
  have hNormalTwo' : -(y0 * x3) + y3 * x0 = 0 := by
    dsimp [x0, x1, x2, x3, y0, y1, y2, y3]
    convert hNormalTwo using 1 <;> ring
  have hNorm' : 0 < x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3 := by
    rw [EuclideanSpace.real_norm_sq_eq] at hNorm
    simpa [x0, x1, x2, x3, Fin.sum_univ_succ, pow_two,
      add_assoc] using hNorm
  let radius := x0 * x0 + x1 * x1 + x2 * x2 + x3 * x3
  have hy0Scale : radius * y0 = 0 := by
    calc
      radius * y0 = x0 * (y0 * x0 + y1 * x1 + y2 * x2 + y3 * x3) -
          x1 * (-(y0 * x1) + y1 * x0) -
          x2 * (-(y0 * x2) + y2 * x0) -
          x3 * (-(y0 * x3) + y3 * x0) := by
        dsimp [radius]
        ring
      _ = 0 := by
        rw [hRadial', hNormalZero', hNormalOne', hNormalTwo']
        ring
  have hy1Scale : radius * y1 = 0 := by
    calc
      radius * y1 = x1 * (y0 * x0 + y1 * x1 + y2 * x2 + y3 * x3) +
          x0 * (-(y0 * x1) + y1 * x0) -
          x2 * (-(y1 * x2) + y2 * x1) +
          x3 * (y1 * x3 - y3 * x1) := by
        dsimp [radius]
        ring
      _ = 0 := by
        rw [hRadial', hNormalZero', hSpatialTwo', hSpatialOne']
        ring
  have hy2Scale : radius * y2 = 0 := by
    calc
      radius * y2 = x2 * (y0 * x0 + y1 * x1 + y2 * x2 + y3 * x3) +
          x0 * (-(y0 * x2) + y2 * x0) +
          x1 * (-(y1 * x2) + y2 * x1) -
          x3 * (-(y2 * x3) + y3 * x2) := by
        dsimp [radius]
        ring
      _ = 0 := by
        rw [hRadial', hNormalOne', hSpatialTwo', hSpatialZero']
        ring
  have hy3Scale : radius * y3 = 0 := by
    calc
      radius * y3 = x3 * (y0 * x0 + y1 * x1 + y2 * x2 + y3 * x3) +
          x0 * (-(y0 * x3) + y3 * x0) -
          x1 * (y1 * x3 - y3 * x1) +
          x2 * (-(y2 * x3) + y3 * x2) := by
        dsimp [radius]
        ring
      _ = 0 := by
        rw [hRadial', hNormalTwo', hSpatialOne', hSpatialZero']
        ring
  have hRadius : radius ≠ 0 := by
    exact ne_of_gt (by simpa [radius] using hNorm')
  have hy0 : y0 = 0 := (mul_eq_zero.mp hy0Scale).resolve_left hRadius
  have hy1 : y1 = 0 := (mul_eq_zero.mp hy1Scale).resolve_left hRadius
  have hy2 : y2 = 0 := (mul_eq_zero.mp hy2Scale).resolve_left hRadius
  have hy3 : y3 = 0 := (mul_eq_zero.mp hy3Scale).resolve_left hRadius
  apply PiLp.ext
  intro index
  fin_cases index
  · exact hy0
  · exact hy1
  · exact hy2
  · exact hy3

/-- Gate marker for pointwise Euclidean separation by all ten generators. -/
theorem canonical_ten_flow_euclidean_span_gate :
    ∀ (period time : Real) (point : EuclideanR4), point ≠ 0 →
      Submodule.span Real
        (Set.range (canonicalEuclideanFlowGenerator period time point)) = ⊤ :=
  canonicalEuclideanFlowGenerator_spans

end
end P0EFTJanusMappingTorusCanonicalTenFlowEuclideanSpan4D
end JanusFormal
