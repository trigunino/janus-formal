import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedComplementInverse4D

/-!
# Finite-dimensional kernel from a Gårding estimate modulo finite rank

A standard elliptic estimate has the form

`‖x - P x‖ ≤ C ‖H x‖`,

where `P` has finite-dimensional range.  For `x ∈ ker H` the right-hand side
vanishes, hence `x = P x`; the kernel embeds in `range P` and is finite
dimensional.  This is the kernel part of the H12 Fredholm estimate and does not
require a separately supplied finite-kernel certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAugmentedFiniteProjectionGarding4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Topology
open scoped InnerProductSpace

universe u

variable {Hilbert : Type u}
  [NormedAddCommGroup Hilbert]
  [NormedSpace Real Hilbert]

/-- A product estimate modulo a finite-dimensional projection.  Idempotence is
not needed for the kernel argument; only finite range and the estimate matter. -/
structure FiniteProjectionGardingData
    (operator : Hilbert →L[Real] Hilbert) : Prop where
  projection : Hilbert →L[Real] Hilbert
  projection_range_finite : FiniteDimensional Real projection.range
  constant : Real
  constant_nonneg : 0 ≤ constant
  estimate : ∀ vector,
    ‖vector - projection vector‖ ≤ constant * ‖operator vector‖

/-- A kernel vector is fixed by the finite-dimensional projection. -/
theorem FiniteProjectionGardingData.eq_projection_of_mem_ker
    {operator : Hilbert →L[Real] Hilbert}
    (data : FiniteProjectionGardingData operator)
    {vector : Hilbert}
    (hKernel : vector ∈ operator.ker) :
    vector = data.projection vector := by
  have hEstimate := data.estimate vector
  have hOperator : operator vector = 0 := hKernel
  rw [hOperator, norm_zero, mul_zero] at hEstimate
  have hZero : ‖vector - data.projection vector‖ = 0 :=
    le_antisymm hEstimate (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hZero)

/-- The kernel is contained in the range of the finite projection. -/
theorem FiniteProjectionGardingData.ker_le_projection_range
    {operator : Hilbert →L[Real] Hilbert}
    (data : FiniteProjectionGardingData operator) :
    operator.ker ≤ data.projection.range := by
  intro vector hKernel
  refine ⟨vector, ?_⟩
  exact (data.eq_projection_of_mem_ker hKernel).symm

/-- The kernel is finite dimensional. -/
theorem FiniteProjectionGardingData.kernel_finite
    {operator : Hilbert →L[Real] Hilbert}
    (data : FiniteProjectionGardingData operator) :
    FiniteDimensional Real operator.ker := by
  letI : FiniteDimensional Real data.projection.range :=
    data.projection_range_finite
  let inclusion : operator.ker →ₗ[Real] data.projection.range :=
    { toFun := fun vector =>
        ⟨vector.1, data.ker_le_projection_range vector.2⟩
      map_add' := by
        intro first second
        rfl
      map_smul' := by
        intro scalar vector
        rfl }
  have hInjective : Function.Injective inclusion := by
    intro first second hEq
    apply Subtype.ext
    exact congrArg Subtype.val hEq
  exact FiniteDimensional.of_injective inclusion hInjective

/-- Public finite-kernel Gårding gate. -/
theorem finite_projection_garding_kernel_gate
    (operator : Hilbert →L[Real] Hilbert)
    (data : FiniteProjectionGardingData operator) :
    operator.ker ≤ data.projection.range ∧
      FiniteDimensional Real operator.ker :=
  ⟨data.ker_le_projection_range, data.kernel_finite⟩

end
end P0EFTJanusProgramPAugmentedFiniteProjectionGarding4D
end JanusFormal
