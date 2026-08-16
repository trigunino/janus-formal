import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Automatic bound for a pulled-back Robin Hessian

Once the H10 Robin Hessian is a continuous bilinear form and the common-domain
boundary projection is continuous linear, no extra Robin estimate is needed.
Its pullback is automatically bounded by the product of the operator norms.
This elementary gate is used to keep the H11 analytic frontier restricted to
the six non-Robin physical blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRobinHessianPullbackBound4D

set_option autoImplicit false
noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

/-- Pull back a continuous bilinear form along one bounded linear projection in
both arguments. -/
def robinHessianPullback
    (form : F →L[Real] F →L[Real] Real)
    (projection : E →L[Real] F) :
    E →L[Real] E →L[Real] Real :=
  form.bilinearComp projection projection

/-- Symmetry is preserved by the common-domain pullback. -/
theorem robinHessianPullback_symmetric
    (form : F →L[Real] F →L[Real] Real)
    (projection : E →L[Real] F)
    (hSymmetric : ∀ first second, form first second = form second first) :
    ∀ first second,
      robinHessianPullback form projection first second =
        robinHessianPullback form projection second first := by
  intro first second
  exact hSymmetric (projection first) (projection second)

/-- The Robin bound follows only from continuity of the H10 Hessian and of the
boundary projection. -/
theorem norm_robinHessianPullback_le
    (form : F →L[Real] F →L[Real] Real)
    (projection : E →L[Real] F)
    (first second : E) :
    ‖robinHessianPullback form projection first second‖ ≤
      (‖form‖ * ‖projection‖ * ‖projection‖) * ‖first‖ * ‖second‖ := by
  change ‖form (projection first) (projection second)‖ ≤ _
  calc
    ‖form (projection first) (projection second)‖
        ≤ ‖form (projection first)‖ * ‖projection second‖ :=
      (form (projection first)).le_opNorm _
    _ ≤ (‖form‖ * ‖projection first‖) * ‖projection second‖ := by
      exact mul_le_mul_of_nonneg_right (form.le_opNorm _) (norm_nonneg _)
    _ ≤ (‖form‖ * (‖projection‖ * ‖first‖)) *
          (‖projection‖ * ‖second‖) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (projection.le_opNorm _) (norm_nonneg _))
        (projection.le_opNorm _)
        (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖form‖ * ‖projection‖ * ‖projection‖) * ‖first‖ * ‖second‖ := by
      ring

/-- Public checkpoint: the pulled-back H10 Robin form is symmetric and bounded
without an independent Robin analytic datum. -/
theorem robin_hessian_pullback_bound_gate
    (form : F →L[Real] F →L[Real] Real)
    (projection : E →L[Real] F)
    (hSymmetric : ∀ first second, form first second = form second first) :
    (∀ first second,
      robinHessianPullback form projection first second =
        robinHessianPullback form projection second first) ∧
    (∀ first second,
      ‖robinHessianPullback form projection first second‖ ≤
        (‖form‖ * ‖projection‖ * ‖projection‖) * ‖first‖ * ‖second‖) :=
  ⟨robinHessianPullback_symmetric form projection hSymmetric,
    norm_robinHessianPullback_le form projection⟩

end
end P0EFTJanusProgramPRobinHessianPullbackBound4D
end JanusFormal
