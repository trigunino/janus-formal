import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Core bound from one completed Robin form and finitely many core blocks

The H10 Robin Hessian already lives as a continuous bilinear form on the common
Hilbert domain.  The remaining physical blocks need only be estimated on the
dense smooth core.  Their exact reconstruction with the Robin restriction
then gives one aggregate product bound, which can be fed to the existing
`LinearMap.extendOfNorm` construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRobinPlusFiniteCoreBound4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators

variable {Core Hilbert Block : Type*}
  [NormedAddCommGroup Core] [NormedSpace Real Core]
  [NormedAddCommGroup Hilbert] [NormedSpace Real Hilbert]
  [Fintype Block]

/-- Exact decomposition of a core Hessian into the restriction of one already
completed Robin form and finitely many remaining core forms. -/
structure RobinPlusFiniteCoreBoundData
    (embedding : Core →ₗ[Real] Hilbert)
    (totalCoreForm : Core →ₗ[Real] Core →ₗ[Real] Real) : Prop where
  robin : Hilbert →L[Real] Hilbert →L[Real] Real
  physical : Block → Core →ₗ[Real] Core →ₗ[Real] Real
  reconstruct : ∀ first second,
    totalCoreForm first second =
      robin (embedding first) (embedding second) +
        ∑ block : Block, physical block first second
  constant : Block → Real
  constant_nonneg : ∀ block, 0 ≤ constant block
  physical_estimate : ∀ block first second,
    ‖physical block first second‖ ≤
      constant block * ‖embedding first‖ * ‖embedding second‖

/-- Operator-norm estimate for the restriction of the completed Robin form. -/
theorem norm_completedRobin_on_core_le
    (embedding : Core →ₗ[Real] Hilbert)
    (robin : Hilbert →L[Real] Hilbert →L[Real] Real)
    (first second : Core) :
    ‖robin (embedding first) (embedding second)‖ ≤
      ‖robin‖ * ‖embedding first‖ * ‖embedding second‖ := by
  calc
    ‖robin (embedding first) (embedding second)‖
        ≤ ‖robin (embedding first)‖ * ‖embedding second‖ :=
      (robin (embedding first)).le_opNorm _
    _ ≤ (‖robin‖ * ‖embedding first‖) * ‖embedding second‖ := by
      exact mul_le_mul_of_nonneg_right (robin.le_opNorm _) (norm_nonneg _)
    _ = ‖robin‖ * ‖embedding first‖ * ‖embedding second‖ := rfl

/-- The aggregate smooth-core Hessian is bounded by the canonical Robin norm
plus the finite sum of the remaining physical constants. -/
theorem norm_totalCoreForm_le
    (embedding : Core →ₗ[Real] Hilbert)
    (totalCoreForm : Core →ₗ[Real] Core →ₗ[Real] Real)
    (data : RobinPlusFiniteCoreBoundData embedding totalCoreForm)
    (first second : Core) :
    ‖totalCoreForm first second‖ ≤
      (‖data.robin‖ + ∑ block : Block, data.constant block) *
        ‖embedding first‖ * ‖embedding second‖ := by
  rw [data.reconstruct first second]
  calc
    ‖data.robin (embedding first) (embedding second) +
        ∑ block : Block, data.physical block first second‖
        ≤ ‖data.robin (embedding first) (embedding second)‖ +
          ‖∑ block : Block, data.physical block first second‖ :=
      norm_add_le _ _
    _ ≤ ‖data.robin‖ * ‖embedding first‖ * ‖embedding second‖ +
          ∑ block : Block, ‖data.physical block first second‖ := by
      exact add_le_add
        (norm_completedRobin_on_core_le embedding data.robin first second)
        (norm_sum_le Finset.univ
          (fun block : Block => data.physical block first second))
    _ ≤ ‖data.robin‖ * ‖embedding first‖ * ‖embedding second‖ +
          ∑ block : Block,
            data.constant block * ‖embedding first‖ * ‖embedding second‖ := by
      exact add_le_add_left
        (Finset.sum_le_sum fun block _ =>
          data.physical_estimate block first second) _
    _ = (‖data.robin‖ + ∑ block : Block, data.constant block) *
          ‖embedding first‖ * ‖embedding second‖ := by
      simp only [Finset.sum_mul]
      ring

/-- The aggregate bound constant is nonnegative. -/
theorem robinPlusFiniteCoreBound_constant_nonneg
    (embedding : Core →ₗ[Real] Hilbert)
    (totalCoreForm : Core →ₗ[Real] Core →ₗ[Real] Real)
    (data : RobinPlusFiniteCoreBoundData embedding totalCoreForm) :
    0 ≤ ‖data.robin‖ + ∑ block : Block, data.constant block := by
  exact add_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun block _ => data.constant_nonneg block)

/-- Public aggregate-core-bound checkpoint. -/
theorem robin_plus_finite_core_bound_gate
    (embedding : Core →ₗ[Real] Hilbert)
    (totalCoreForm : Core →ₗ[Real] Core →ₗ[Real] Real)
    (data : RobinPlusFiniteCoreBoundData embedding totalCoreForm) :
    0 ≤ ‖data.robin‖ + ∑ block : Block, data.constant block ∧
    ∀ first second,
      ‖totalCoreForm first second‖ ≤
        (‖data.robin‖ + ∑ block : Block, data.constant block) *
          ‖embedding first‖ * ‖embedding second‖ :=
  ⟨robinPlusFiniteCoreBound_constant_nonneg embedding totalCoreForm data,
    norm_totalCoreForm_le embedding totalCoreForm data⟩

end
end P0EFTJanusProgramPRobinPlusFiniteCoreBound4D
end JanusFormal
