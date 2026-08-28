import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D

/-!
# Restrict a commuting sector resolution to the actual kernel

A self-adjoint finite sector resolution commuting with an operator preserves its
actual kernel as well as its orthogonal complement.  The complement restriction
already supports the H12 coercive route.  This companion layer constructs the
canonical restriction to the zero-mode space itself.

The resulting kernel projectors retain the identity resolution,
idempotence, symmetry and Pythagorean norm decomposition.  They provide the
correct typed objects for sector-preserving transports between kernels at
different family parameters.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
open P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D

variable {Sector E : Type*}
  [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

namespace FiniteCommutingProjectionResolutionData

/-- Canonical restriction of one commuting physical projector to the actual
kernel. -/
def kernelProjection
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (sector : Sector) : operator.ker →L[Real] operator.ker := by
  let linear : operator.ker →ₗ[Real] operator.ker :=
    { toFun := fun vector =>
        ⟨data.resolution.projection sector vector.1,
          data.projection_mem_kernel sector vector.2⟩
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
theorem kernelProjection_apply_val
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (sector : Sector) (vector : operator.ker) :
    (kernelProjection data sector vector).1 =
      data.resolution.projection sector vector.1 :=
  rfl

/-- The restricted kernel projectors still resolve the identity. -/
theorem sum_kernelProjection
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (vector : operator.ker) :
    (∑ sector : Sector, kernelProjection data sector vector) = vector := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  simp only [kernelProjection_apply_val]
  exact data.resolution.sum_projection vector.1

/-- Idempotence descends to the actual kernel. -/
theorem kernelProjection_idempotent
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (sector : Sector) (vector : operator.ker) :
    kernelProjection data sector
        (kernelProjection data sector vector) =
      kernelProjection data sector vector := by
  apply Subtype.ext
  simp only [kernelProjection_apply_val]
  exact data.resolution.projection_idempotent sector vector.1

/-- Symmetry descends to the actual kernel. -/
theorem kernelProjection_symmetric
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (sector : Sector) (first second : operator.ker) :
    inner Real (kernelProjection data sector first) second =
      inner Real first (kernelProjection data sector second) := by
  change inner Real (data.resolution.projection sector first.1) second.1 =
    inner Real first.1 (data.resolution.projection sector second.1)
  exact data.resolution.projection_symmetric sector first.1 second.1

/-- The full-space commuting resolution canonically restricts to one exact
self-adjoint projection resolution on the true zero-mode space. -/
def toKernelResolution
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator) :
    FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := operator.ker) where
  projection := kernelProjection data
  sum_projection := sum_kernelProjection data
  projection_idempotent := kernelProjection_idempotent data
  projection_symmetric := kernelProjection_symmetric data

/-- Pythagorean decomposition of every actual zero mode into its physical
kernel sectors. -/
theorem kernel_norm_sq_decomposition
    {operator : E →L[Real] E}
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator)
    (vector : operator.ker) :
    ‖vector‖ ^ 2 =
      ∑ sector : Sector, ‖kernelProjection data sector vector‖ ^ 2 :=
  (toKernelResolution data).norm_sq_decomposition vector

/-- Public actual-kernel sector-resolution checkpoint. -/
theorem finite_commuting_projection_kernel_gate
    (operator : E →L[Real] E)
    (data : FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator) :
    let kernelResolution := toKernelResolution data
    (∀ vector,
      (∑ sector : Sector, kernelResolution.projection sector vector) = vector) ∧
    (∀ sector vector,
      kernelResolution.projection sector
          (kernelResolution.projection sector vector) =
        kernelResolution.projection sector vector) ∧
    (∀ sector first second,
      inner Real (kernelResolution.projection sector first) second =
        inner Real first (kernelResolution.projection sector second)) ∧
    (∀ vector,
      ‖vector‖ ^ 2 =
        ∑ sector : Sector,
          ‖kernelResolution.projection sector vector‖ ^ 2) := by
  dsimp only
  let kernelResolution := toKernelResolution data
  exact
    ⟨kernelResolution.sum_projection,
      kernelResolution.projection_idempotent,
      kernelResolution.projection_symmetric,
      kernelResolution.norm_sq_decomposition⟩

end FiniteCommutingProjectionResolutionData

end
end P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D
end JanusFormal
