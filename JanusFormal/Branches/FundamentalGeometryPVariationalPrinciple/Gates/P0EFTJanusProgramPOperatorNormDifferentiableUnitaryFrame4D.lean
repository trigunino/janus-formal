import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Operator-norm differentiable unitary frames

A family of unitary maps may be presented by pointwise differentiability of
`a ↦ F_a v` for every chosen vector.  For connection geometry the stronger and
more useful statement is differentiability of

```text
a ↦ F_a
```

in the normed space of continuous linear operators.

This file records that single operator-valued derivative and derives the
pointwise derivative, differentiability and continuity of every transported
vector.  Consequently finite kernel generators and arbitrary fixed complement
vectors need not carry separate C1 premises once an operator-norm frame is
available.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D

set_option autoImplicit false
noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- A unitary frame viewed as a family of continuous linear endomorphisms. -/
def unitaryFrameOperator
    (frame : Real → E ≃ₗᵢ[Real] E)
    (parameter : Real) : E →L[Real] E :=
  (frame parameter).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem unitaryFrameOperator_apply
    (frame : Real → E ≃ₗᵢ[Real] E)
    (parameter : Real) (vector : E) :
    unitaryFrameOperator frame parameter vector = frame parameter vector :=
  rfl

/-- Operator-norm C1 datum for one unitary frame. -/
structure OperatorNormDifferentiableUnitaryFrameData
    (frame : Real → E ≃ₗᵢ[Real] E) where
  derivative : Real → E →L[Real] E
  hasDerivAt_frame : ∀ parameter,
    HasDerivAt (unitaryFrameOperator frame) (derivative parameter) parameter

namespace OperatorNormDifferentiableUnitaryFrameData

/-- Evaluation on a fixed vector inherits the operator derivative. -/
theorem hasDerivAt_apply
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) (vector : E) :
    HasDerivAt
      (fun current : Real => frame current vector)
      (data.derivative parameter vector) parameter := by
  simpa [unitaryFrameOperator] using
    (data.hasDerivAt_frame parameter).clm_apply
      (hasDerivAt_const parameter vector)

/-- Every transported fixed vector is differentiable. -/
theorem differentiable_apply
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (vector : E) :
    Differentiable Real (fun parameter : Real => frame parameter vector) :=
  fun parameter => (data.hasDerivAt_apply parameter vector).differentiableAt

/-- Every transported fixed vector is continuous. -/
theorem continuous_apply
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (vector : E) :
    Continuous (fun parameter : Real => frame parameter vector) :=
  (data.differentiable_apply vector).continuous

/-- The operator-valued frame itself is differentiable. -/
theorem differentiable_frame
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame) :
    Differentiable Real (unitaryFrameOperator frame) :=
  fun parameter => (data.hasDerivAt_frame parameter).differentiableAt

/-- Public operator-norm frame checkpoint. -/
theorem operator_norm_differentiable_unitary_frame_gate
    (frame : Real → E ≃ₗᵢ[Real] E)
    (data : OperatorNormDifferentiableUnitaryFrameData frame) :
    (∀ parameter,
      HasDerivAt (unitaryFrameOperator frame)
        (data.derivative parameter) parameter) ∧
    Differentiable Real (unitaryFrameOperator frame) ∧
    (∀ vector,
      Differentiable Real (fun parameter : Real => frame parameter vector)) ∧
    (∀ vector,
      Continuous (fun parameter : Real => frame parameter vector)) :=
  ⟨data.hasDerivAt_frame,
    data.differentiable_frame,
    data.differentiable_apply,
    data.continuous_apply⟩

end OperatorNormDifferentiableUnitaryFrameData

end
end P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D
end JanusFormal
