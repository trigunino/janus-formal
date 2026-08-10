import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

/-!
# Restrict a commuting sector resolution to the actual kernel complement

A physical sector decomposition should be constructed once on the full Hilbert
space.  If each self-adjoint sector projector commutes with the displayed
Hessian, it preserves both the genuine kernel and its orthogonal complement.
Hence the same sector resolution descends canonically to `(ker H)ᗮ`.

This removes the need to choose a second five-sector decomposition solely for
the coercive H12 calculation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
noncomputable section

open Set
open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {Sector E : Type*}
  [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- A self-adjoint finite sector resolution on the full Hilbert space, with
each projector commuting with the actual Hessian. -/
structure FiniteCommutingProjectionResolutionData
    (operator : E →L[Real] E) where
  resolution : FiniteSelfAdjointProjectionResolutionData
    (Sector := Sector) (E := E)
  commute : ∀ sector vector,
    operator (resolution.projection sector vector) =
      resolution.projection sector (operator vector)

namespace FiniteCommutingProjectionResolutionData

/-- Every commuting sector projector preserves the genuine kernel. -/
theorem projection_mem_kernel
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (sector : Sector) {vector : E} (hVector : vector ∈ operator.ker) :
    data.resolution.projection sector vector ∈ operator.ker := by
  rw [LinearMap.mem_ker]
  rw [data.commute sector vector]
  rw [LinearMap.mem_ker.mp hVector, map_zero]

/-- Self-adjointness of a sector projector and commutation with `H` imply that
it preserves the orthogonal complement of the actual kernel. -/
theorem projection_mem_kernelComplement
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (sector : Sector)
    (vector : SelfAdjointKernelComplement operator) :
    data.resolution.projection sector vector.1 ∈ operator.kerᗮ := by
  rw [Submodule.mem_orthogonal']
  intro zeroMode hZeroMode
  rw [data.resolution.projection_symmetric sector]
  exact vector.2
    (data.resolution.projection sector zeroMode)
    (data.projection_mem_kernel sector hZeroMode)

/-- Canonical restriction of one sector projector to `(ker H)ᗮ`. -/
def complementProjection
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (sector : Sector) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator := by
  let linear : SelfAdjointKernelComplement operator →ₗ[Real]
      SelfAdjointKernelComplement operator :=
    { toFun := fun vector =>
        ⟨data.resolution.projection sector vector.1,
          data.projection_mem_kernelComplement sector vector⟩
      map_add' := by
        intro first second
        apply Subtype.ext
        exact map_add (data.resolution.projection sector) first.1 second.1
      map_smul' := by
        intro scalar vector
        apply Subtype.ext
        exact map_smul (data.resolution.projection sector) scalar vector.1 }
  exact linear.mkContinuous ‖data.resolution.projection sector‖ (by
    intro vector
    change ‖data.resolution.projection sector vector.1‖ ≤
      ‖data.resolution.projection sector‖ * ‖vector.1‖
    exact (data.resolution.projection sector).le_opNorm vector.1)

@[simp]
theorem complementProjection_apply_val
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (sector : Sector)
    (vector : SelfAdjointKernelComplement operator) :
    (data.complementProjection sector vector).1 =
      data.resolution.projection sector vector.1 :=
  rfl

/-- The restricted projectors still resolve the identity. -/
theorem sum_complementProjection
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (vector : SelfAdjointKernelComplement operator) :
    (∑ sector : Sector, data.complementProjection sector vector) = vector := by
  apply Subtype.ext
  simp only [map_sum, complementProjection_apply_val]
  exact data.resolution.sum_projection vector.1

/-- Idempotence descends to the actual kernel complement. -/
theorem complementProjection_idempotent
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (sector : Sector)
    (vector : SelfAdjointKernelComplement operator) :
    data.complementProjection sector
        (data.complementProjection sector vector) =
      data.complementProjection sector vector := by
  apply Subtype.ext
  simp only [complementProjection_apply_val]
  exact data.resolution.projection_idempotent sector vector.1

/-- Self-adjointness also descends. -/
theorem complementProjection_symmetric
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (sector : Sector)
    (first second : SelfAdjointKernelComplement operator) :
    inner Real (data.complementProjection sector first) second =
      inner Real first (data.complementProjection sector second) := by
  change inner Real (data.resolution.projection sector first.1) second.1 =
    inner Real first.1 (data.resolution.projection sector second.1)
  exact data.resolution.projection_symmetric sector first.1 second.1

/-- The full-space commuting resolution canonically becomes the exact
self-adjoint projection resolution needed by complement Gårding. -/
def toKernelComplementResolution
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator) :
    FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := SelfAdjointKernelComplement operator) where
  projection := data.complementProjection
  sum_projection := data.sum_complementProjection
  projection_idempotent := data.complementProjection_idempotent
  projection_symmetric := data.complementProjection_symmetric

/-- Public checkpoint: one commuting resolution on the physical Hilbert space
is enough for the actual-kernel complement. -/
theorem finite_commuting_projection_kernelComplement_gate
    (operator : E →L[Real] E)
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator) :
    let reduced := data.toKernelComplementResolution
    (∀ vector,
      (∑ sector : Sector, reduced.projection sector vector) = vector) ∧
    (∀ sector vector,
      reduced.projection sector (reduced.projection sector vector) =
        reduced.projection sector vector) ∧
    (∀ sector first second,
      inner Real (reduced.projection sector first) second =
        inner Real first (reduced.projection sector second)) ∧
    (∀ vector,
      ‖vector‖ ^ 2 =
        ∑ sector : Sector, ‖reduced.projection sector vector‖ ^ 2) := by
  dsimp only
  let reduced := data.toKernelComplementResolution
  exact
    ⟨reduced.sum_projection,
      reduced.projection_idempotent,
      reduced.projection_symmetric,
      reduced.norm_sq_decomposition⟩

end FiniteCommutingProjectionResolutionData

end
end P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D
end JanusFormal
