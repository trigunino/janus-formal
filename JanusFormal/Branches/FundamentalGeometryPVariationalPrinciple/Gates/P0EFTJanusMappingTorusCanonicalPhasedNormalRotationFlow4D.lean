import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

/-! # Canonical phased normal rotations on the reflected sphere cover -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusReflectionFixedThroat

/-- Infinitesimal rotation in the plane formed by reflected coordinate zero
and spatial coordinate one. -/
private def normalRotationOneLinear : R4Point →ₗ[Real] R4Point where
  toFun point := ![-point 1, point 0, 0, 0]
  map_add' first second := by
    funext index
    fin_cases index <;> simp [add_comm]
  map_smul' scalar point := by
    funext index
    fin_cases index <;> simp

/-- Infinitesimal rotation in the `0,2` coordinate plane. -/
private def normalRotationTwoLinear : R4Point →ₗ[Real] R4Point where
  toFun point := ![-point 2, 0, point 0, 0]
  map_add' first second := by
    funext index
    fin_cases index <;> simp [add_comm]
  map_smul' scalar point := by
    funext index
    fin_cases index <;> simp

/-- Infinitesimal rotation in the `0,3` coordinate plane. -/
private def normalRotationThreeLinear : R4Point →ₗ[Real] R4Point where
  toFun point := ![-point 3, 0, 0, point 0]
  map_add' first second := by
    funext index
    fin_cases index <;> simp [add_comm]
  map_smul' scalar point := by
    funext index
    fin_cases index <;> simp

/-- The three ambient rotations involving the reflected coordinate. -/
def ambientNormalRotation (axis : Fin 3) : R4Point →L[Real] R4Point :=
  (![normalRotationOneLinear, normalRotationTwoLinear,
      normalRotationThreeLinear] axis).toContinuousLinearMap

theorem ambientNormalRotation_apply (axis : Fin 3) (point : R4Point) :
    ambientNormalRotation axis point = match axis with
    | 0 => ![-point 1, point 0, 0, 0]
    | 1 => ![-point 2, 0, point 0, 0]
    | 2 => ![-point 3, 0, 0, point 0] := by
  fin_cases axis <;> rfl

theorem ambientNormalRotation_tangent
    (axis : Fin 3) (point : R4Point) :
    ∑ index : Fin 4, point index * ambientNormalRotation axis point index = 0 := by
  fin_cases axis <;>
    simp [ambientNormalRotation, normalRotationOneLinear,
      normalRotationTwoLinear, normalRotationThreeLinear,
      Fin.sum_univ_succ] <;> ring

/-- Complete rotation in one reflected-spatial coordinate plane. -/
def ambientNormalRotationFlow
    (axis : Fin 3) (input : Real × R4Point) : R4Point :=
  match axis with
  | 0 => ![
      Real.cos input.1 * input.2 0 - Real.sin input.1 * input.2 1,
      Real.sin input.1 * input.2 0 + Real.cos input.1 * input.2 1,
      input.2 2, input.2 3]
  | 1 => ![
      Real.cos input.1 * input.2 0 - Real.sin input.1 * input.2 2,
      input.2 1,
      Real.sin input.1 * input.2 0 + Real.cos input.1 * input.2 2,
      input.2 3]
  | 2 => ![
      Real.cos input.1 * input.2 0 - Real.sin input.1 * input.2 3,
      input.2 1, input.2 2,
      Real.sin input.1 * input.2 0 + Real.cos input.1 * input.2 3]

@[simp]
theorem ambientNormalRotationFlow_zero
    (axis : Fin 3) (point : R4Point) :
    ambientNormalRotationFlow axis (0, point) = point := by
  fin_cases axis <;> ext index <;> fin_cases index <;>
    simp [ambientNormalRotationFlow]

theorem ambientNormalRotationFlow_contDiff (axis : Fin 3) :
    ContDiff Real ∞ (ambientNormalRotationFlow axis) := by
  rw [contDiff_pi]
  intro index
  fin_cases axis <;> fin_cases index <;>
    simp [ambientNormalRotationFlow] <;> fun_prop

theorem ambientNormalRotationFlow_preserves_radius
    (axis : Fin 3) (input : Real × R4Point) :
    radiusSquared (ambientNormalRotationFlow axis input) =
      radiusSquared input.2 := by
  fin_cases axis <;>
    simp [ambientNormalRotationFlow, radiusSquared, Fin.sum_univ_succ] <;>
    nlinarith [Real.sin_sq_add_cos_sq input.1]

/-- Reflection conjugates every normal rotation to its inverse. -/
theorem ambientNormalRotationFlow_reflection_conjugates
    (axis : Fin 3) (input : Real × R4Point) :
    reflectPoint (ambientNormalRotationFlow axis input) =
      ambientNormalRotationFlow axis (-input.1, reflectPoint input.2) := by
  fin_cases axis <;> ext index <;> fin_cases index <;>
    simp [ambientNormalRotationFlow, reflectPoint] <;> ring

theorem ambientNormalRotationFlow_angle_add
    (axis : Fin 3) (first second : Real) (point : R4Point) :
    ambientNormalRotationFlow axis (first + second, point) =
      ambientNormalRotationFlow axis
        (first, ambientNormalRotationFlow axis (second, point)) := by
  fin_cases axis <;> ext index <;> fin_cases index <;>
    simp [ambientNormalRotationFlow, Real.sin_add, Real.cos_add] <;> ring

theorem ambientNormalRotationFlow_hasDerivAt_zero
    (axis : Fin 3) (point : R4Point) :
    HasDerivAt
      (fun angle : Real => ambientNormalRotationFlow axis (angle, point))
      (ambientNormalRotation axis point) 0 := by
  have hCosMul (value : Real) :
      HasDerivAt (fun angle : Real => Real.cos angle * value) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).mul_const value
  have hSinMul (value : Real) :
      HasDerivAt (fun angle : Real => Real.sin angle * value) value 0 := by
    simpa using (Real.hasDerivAt_sin 0).mul_const value
  have hFirst (first second : Real) :
      HasDerivAt (fun angle : Real =>
        Real.cos angle * first - Real.sin angle * second) (-second) 0 := by
    refine ((((hCosMul first).sub (hSinMul second)).congr_deriv (by simp))
      |>.congr_of_eventuallyEq ?_)
    exact Filter.Eventually.of_forall fun _ => rfl
  have hSecond (first second : Real) :
      HasDerivAt (fun angle : Real =>
        Real.sin angle * first + Real.cos angle * second) first 0 := by
    refine ((((hSinMul first).add (hCosMul second)).congr_deriv (by simp))
      |>.congr_of_eventuallyEq ?_)
    exact Filter.Eventually.of_forall fun _ => rfl
  rw [hasDerivAt_pi]
  intro index
  fin_cases axis
  · fin_cases index
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationOneLinear] using hFirst (point 0) (point 1)
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationOneLinear] using hSecond (point 0) (point 1)
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationOneLinear] using
          (hasDerivAt_const (x := (0 : Real)) (c := point 2))
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationOneLinear] using
          (hasDerivAt_const (x := (0 : Real)) (c := point 3))
  · fin_cases index
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationTwoLinear] using hFirst (point 0) (point 2)
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationTwoLinear] using
          (hasDerivAt_const (x := (0 : Real)) (c := point 1))
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationTwoLinear] using hSecond (point 0) (point 2)
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationTwoLinear] using
          (hasDerivAt_const (x := (0 : Real)) (c := point 3))
  · fin_cases index
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationThreeLinear] using hFirst (point 0) (point 3)
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationThreeLinear] using
          (hasDerivAt_const (x := (0 : Real)) (c := point 1))
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationThreeLinear] using
          (hasDerivAt_const (x := (0 : Real)) (c := point 2))
    · simpa [ambientNormalRotationFlow, ambientNormalRotation,
        normalRotationThreeLinear] using hSecond (point 0) (point 3)

/-- The two half-frequency phases used to compensate the reflected deck
action. -/
def canonicalNormalRotationPhase
    (period : Real) (phase : Fin 2) (time : Real) : Real :=
  ![Real.cos ((Real.pi / period) * time),
    Real.sin ((Real.pi / period) * time)] phase

theorem canonicalNormalRotationPhase_contDiff
    (period : Real) (phase : Fin 2) :
    ContDiff Real ∞ (canonicalNormalRotationPhase period phase) := by
  fin_cases phase
  · change ContDiff Real ∞
      (fun time => Real.cos ((Real.pi / period) * time))
    fun_prop
  · change ContDiff Real ∞
      (fun time => Real.sin ((Real.pi / period) * time))
    fun_prop

/-- Translation by one deck period changes both phases by the sign prescribed
by the winding parity. -/
theorem canonicalNormalRotationPhase_add_winding
    (period : Real) (hPeriod : period ≠ 0)
    (phase : Fin 2) (winding : Int) (time : Real) :
    canonicalNormalRotationPhase period phase
        (time + (winding : Real) * period) =
      (-1 : Real) ^ winding *
        canonicalNormalRotationPhase period phase time := by
  have hArgument :
      (Real.pi / period) * (time + (winding : Real) * period) =
        (Real.pi / period) * time + (winding : Real) * Real.pi := by
    field_simp [hPeriod]
  fin_cases phase
  · simp [canonicalNormalRotationPhase, hArgument,
      Real.cos_add_int_mul_pi]
  · simp [canonicalNormalRotationPhase, hArgument,
      Real.sin_add_int_mul_pi]

/-- The two phases never vanish simultaneously. -/
theorem canonicalNormalRotationPhase_square_sum
    (period time : Real) :
    ∑ phase : Fin 2,
      canonicalNormalRotationPhase period phase time ^ 2 = 1 := by
  simp [canonicalNormalRotationPhase, Fin.sum_univ_succ]

theorem exists_canonicalNormalRotationPhase_ne_zero
    (period time : Real) :
    ∃ phase : Fin 2,
      canonicalNormalRotationPhase period phase time ≠ 0 := by
  by_contra h
  push Not at h
  have hSum := canonicalNormalRotationPhase_square_sum period time
  simp [h] at hSum

/-- Gate marker for the complete normal rotations and their canonical
antiperiodic phase pair. -/
theorem canonical_phased_normal_rotation_flow_gate
    (period : Real) (hPeriod : period ≠ 0) :
    (∀ axis : Fin 3,
      ContDiff Real ∞ (ambientNormalRotationFlow axis)) ∧
      (∀ (phase : Fin 2) (winding : Int) (time : Real),
        canonicalNormalRotationPhase period phase
            (time + (winding : Real) * period) =
          (-1 : Real) ^ winding *
            canonicalNormalRotationPhase period phase time) ∧
      (∀ time : Real, ∃ phase : Fin 2,
        canonicalNormalRotationPhase period phase time ≠ 0) := by
  exact ⟨ambientNormalRotationFlow_contDiff,
    canonicalNormalRotationPhase_add_winding period hPeriod,
    exists_canonicalNormalRotationPhase_ne_zero period⟩

end
end P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D
end JanusFormal
