import Mathlib.LinearAlgebra.Pi
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D

/-!
# Natural projections from one finite orthogonal coordinate decomposition

A finite orthogonal sector decomposition should not carry five independently
chosen projectors.  One continuous linear equivalence

`T : E ≃L[ℝ] (∀ s, Component s)`

together with the inner-product decomposition determines them canonically:

`P_s = T⁻¹ ∘ single_s ∘ eval_s ∘ T`.

The coordinate projections automatically resolve the identity, are idempotent
and are self-adjoint.  Hence they produce the positive Pythagorean resolution
used by the finite-sector Gårding chain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteOrthogonalCoordinateResolution4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D

variable {Sector E : Type*}
  [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [InnerProductSpace Real E]

variable (Component : Sector → Type*)
  [∀ sector, NormedAddCommGroup (Component sector)]
  [∀ sector, InnerProductSpace Real (Component sector)]

/-- Evaluation of one component as a bounded linear map. -/
def finitePiEvaluation (sector : Sector) :
    (∀ current, Component current) →L[Real] Component sector where
  toLinearMap :=
    { toFun := fun vector => vector sector
      map_add' := by intro first second; rfl
      map_smul' := by intro scalar vector; rfl }
  cont := continuous_apply sector

/-- A continuous decomposition whose inner product is the finite sum of the
component inner products. -/
structure FiniteOrthogonalCoordinateDecompositionData where
  decomposition : E ≃L[Real] (∀ sector, Component sector)
  inner_decomposition : ∀ first second : E,
    inner Real first second =
      ∑ sector : Sector,
        inner Real (decomposition first sector) (decomposition second sector)

namespace FiniteOrthogonalCoordinateDecompositionData

/-- Keep only one coordinate in product coordinates. -/
def coordinateCut
    (data : FiniteOrthogonalCoordinateDecompositionData
      (Sector := Sector) (E := E) Component)
    (sector : Sector) :
    (∀ current, Component current) →L[Real]
      (∀ current, Component current) :=
  (ContinuousLinearMap.single (R := Real) (φ := Component) sector).comp
    (finitePiEvaluation Component sector)

@[simp]
theorem coordinateCut_apply
    (data : FiniteOrthogonalCoordinateDecompositionData
      (Sector := Sector) (E := E) Component)
    (sector : Sector)
    (vector : ∀ current, Component current) :
    data.coordinateCut Component sector vector =
      Pi.single sector (vector sector) :=
  rfl

/-- Canonical sector projector transported back to the ambient Hilbert space. -/
def projection
    (data : FiniteOrthogonalCoordinateDecompositionData
      (Sector := Sector) (E := E) Component)
    (sector : Sector) : E →L[Real] E :=
  data.decomposition.symm.toContinuousLinearMap.comp
    ((data.coordinateCut Component sector).comp
      data.decomposition.toContinuousLinearMap)

@[simp]
theorem decomposition_projection
    (data : FiniteOrthogonalCoordinateDecompositionData
      (Sector := Sector) (E := E) Component)
    (sector : Sector) (vector : E) :
    data.decomposition (data.projection Component sector vector) =
      Pi.single sector (data.decomposition vector sector) := by
  simp [projection]

/-- Coordinate projectors sum to the identity. -/
theorem sum_projection
    (data : FiniteOrthogonalCoordinateDecompositionData
      (Sector := Sector) (E := E) Component)
    (vector : E) :
    (∑ sector : Sector, data.projection Component sector vector) = vector := by
  apply data.decomposition.injective
  ext current
  simp [data.decomposition_projection Component]

/-- Each coordinate projector is idempotent. -/
theorem projection_idempotent
    (data : FiniteOrthogonalCoordinateDecompositionData
      (Sector := Sector) (E := E) Component)
    (sector : Sector) (vector : E) :
    data.projection Component sector
        (data.projection Component sector vector) =
      data.projection Component sector vector := by
  apply data.decomposition.injective
  ext current
  by_cases h : current = sector
  · subst current
    simp [data.decomposition_projection Component]
  · simp [data.decomposition_projection Component, h]

/-- Orthogonality of product coordinates makes every transported coordinate
projector self-adjoint. -/
theorem projection_symmetric
    (data : FiniteOrthogonalCoordinateDecompositionData
      (Sector := Sector) (E := E) Component)
    (sector : Sector) (first second : E) :
    inner Real (data.projection Component sector first) second =
      inner Real first (data.projection Component sector second) := by
  rw [data.inner_decomposition, data.inner_decomposition]
  classical
  simp only [data.decomposition_projection Component]
  calc
    (∑ x,
      ⟪Pi.single sector (data.decomposition first sector) x,
        data.decomposition second x⟫_Real) =
        ⟪data.decomposition first sector,
          data.decomposition second sector⟫_Real := by
      refine (Finset.sum_eq_single_of_mem sector (Finset.mem_univ _) ?_).trans ?_
      · intro other _ hOther
        simp [Pi.single_eq_of_ne hOther]
      · rw [Pi.single_eq_same]
    _ = ∑ x,
        ⟪data.decomposition first x,
          Pi.single sector (data.decomposition second sector) x⟫_Real := by
      symm
      refine (Finset.sum_eq_single_of_mem sector (Finset.mem_univ _) ?_).trans ?_
      · intro other _ hOther
        simp [Pi.single_eq_of_ne hOther]
      · rw [Pi.single_eq_same]

/-- Canonical self-adjoint resolution generated by the single orthogonal
coordinate decomposition. -/
def toSelfAdjointProjectionResolution
    (data : FiniteOrthogonalCoordinateDecompositionData
      (Sector := Sector) (E := E) Component) :
    FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E) where
  projection := data.projection Component
  sum_projection := data.sum_projection Component
  projection_idempotent := data.projection_idempotent Component
  projection_symmetric := data.projection_symmetric Component

/-- Pythagorean norm decomposition generated by the coordinate equivalence. -/
theorem norm_sq_decomposition
    (data : FiniteOrthogonalCoordinateDecompositionData
      (Sector := Sector) (E := E) Component)
    (vector : E) :
    ‖vector‖ ^ 2 =
      ∑ sector : Sector,
        ‖data.projection Component sector vector‖ ^ 2 :=
  (data.toSelfAdjointProjectionResolution Component).norm_sq_decomposition vector

/-- Public orthogonal-coordinate projection checkpoint. -/
theorem finite_orthogonal_coordinate_resolution_gate
    (data : FiniteOrthogonalCoordinateDecompositionData
      (Sector := Sector) (E := E) Component) :
    (∀ vector,
      (∑ sector : Sector, data.projection Component sector vector) = vector) ∧
    (∀ sector vector,
      data.projection Component sector
          (data.projection Component sector vector) =
        data.projection Component sector vector) ∧
    (∀ sector first second,
      inner Real (data.projection Component sector first) second =
        inner Real first (data.projection Component sector second)) ∧
    (∀ vector,
      ‖vector‖ ^ 2 =
        ∑ sector : Sector,
          ‖data.projection Component sector vector‖ ^ 2) :=
  ⟨data.sum_projection Component,
    data.projection_idempotent Component,
    data.projection_symmetric Component,
    data.norm_sq_decomposition Component⟩

end FiniteOrthogonalCoordinateDecompositionData

end
end P0EFTJanusProgramPFiniteOrthogonalCoordinateResolution4D
end JanusFormal
