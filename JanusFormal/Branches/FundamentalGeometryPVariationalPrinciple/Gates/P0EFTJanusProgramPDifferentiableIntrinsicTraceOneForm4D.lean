import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D

/-!
# Differentiable intrinsic Bismut--Freed trace one-forms

The multidimensional intrinsic trace layer already constructs a genuine
continuous-linear covector

`theta_b(v) = Tr(G_b DH_b[v])`.

To obtain curvature from the operator side, that covector field itself must be
Frechet differentiable in `b`.  This file records its actual derivative and
defines the real trace-part Bismut--Freed curvature by exterior differentiation.

No independent curvature function is supplied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D

variable {Base E : Type*}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Differentiable relative intrinsic logarithmic trace one-form. -/
structure DifferentiableRelativeIntrinsicTraceOneFormData
    (actual reference : Base → E →L[Real] E) where
  trace : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData actual reference
  traceOneFormDerivative : Base → Base →L[Real] (Base →L[Real] Real)
  hasFDerivAt_traceOneForm : ∀ base,
    HasFDerivAt trace.traceOneForm (traceOneFormDerivative base) base

namespace DifferentiableRelativeIntrinsicTraceOneFormData

/-- Derivative of the real BF one-form `-theta`. -/
def bismutFreedOneFormDerivative
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableRelativeIntrinsicTraceOneFormData actual reference)
    (base : Base) : Base →L[Real] (Base →L[Real] Real) :=
  -(data.traceOneFormDerivative base)

/-- The real BF one-form is Frechet differentiable with the negated trace-form
derivative. -/
theorem hasFDerivAt_bismutFreedRealOneForm
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableRelativeIntrinsicTraceOneFormData actual reference)
    (base : Base) :
    HasFDerivAt data.trace.bismutFreedRealOneForm
      (data.bismutFreedOneFormDerivative base) base := by
  unfold RelativeIntrinsicLogarithmicDerivativeTraceOneFormData.
    bismutFreedRealOneForm bismutFreedOneFormDerivative
  simpa using (data.hasFDerivAt_traceOneForm base).neg

/-- Real trace-part BF curvature derived from the operator one-form. -/
def bismutFreedTraceCurvature
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableRelativeIntrinsicTraceOneFormData actual reference)
    (base first second : Base) : Real :=
  data.bismutFreedOneFormDerivative base first second -
    data.bismutFreedOneFormDerivative base second first

/-- Operator trace curvature is antisymmetric by construction. -/
theorem bismutFreedTraceCurvature_antisymm
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableRelativeIntrinsicTraceOneFormData actual reference)
    (base first second : Base) :
    data.bismutFreedTraceCurvature base first second =
      -data.bismutFreedTraceCurvature base second first := by
  unfold bismutFreedTraceCurvature
  abel

/-- Additivity in the first tangent direction. -/
theorem bismutFreedTraceCurvature_add_left
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableRelativeIntrinsicTraceOneFormData actual reference)
    (base first second third : Base) :
    data.bismutFreedTraceCurvature base (first + second) third =
      data.bismutFreedTraceCurvature base first third +
        data.bismutFreedTraceCurvature base second third := by
  unfold bismutFreedTraceCurvature
  rw [map_add, map_add]
  abel

/-- Real homogeneity in the first tangent direction. -/
theorem bismutFreedTraceCurvature_smul_left
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableRelativeIntrinsicTraceOneFormData actual reference)
    (base : Base) (scalar : Real) (first second : Base) :
    data.bismutFreedTraceCurvature base (scalar • first) second =
      scalar * data.bismutFreedTraceCurvature base first second := by
  unfold bismutFreedTraceCurvature
  rw [map_smul, map_smul]
  ring

/-- Public differentiable intrinsic BF trace-one-form checkpoint. -/
theorem differentiable_intrinsic_trace_one_form_gate
    (actual reference : Base → E →L[Real] E)
    (data : DifferentiableRelativeIntrinsicTraceOneFormData actual reference) :
    (∀ base,
      HasFDerivAt data.trace.bismutFreedRealOneForm
        (data.bismutFreedOneFormDerivative base) base) ∧
    (∀ base first second,
      data.bismutFreedTraceCurvature base first second =
        -data.bismutFreedTraceCurvature base second first) ∧
    (∀ base first second third,
      data.bismutFreedTraceCurvature base (first + second) third =
        data.bismutFreedTraceCurvature base first third +
          data.bismutFreedTraceCurvature base second third) :=
  ⟨data.hasFDerivAt_bismutFreedRealOneForm,
    data.bismutFreedTraceCurvature_antisymm,
    data.bismutFreedTraceCurvature_add_left⟩

end DifferentiableRelativeIntrinsicTraceOneFormData

end
end P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D
end JanusFormal
