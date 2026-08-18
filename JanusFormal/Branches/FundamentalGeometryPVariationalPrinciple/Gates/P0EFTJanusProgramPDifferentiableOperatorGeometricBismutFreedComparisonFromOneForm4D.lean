import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D

/-!
# Differential Bismut--Freed comparison from the one-form identity

The pointwise equality of the differentiable geometric and operator one-forms
already forces equality of their Frechet derivatives.  This frontend therefore
constructs the full comparison packet without a separate derivative premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparisonFromOneForm4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D
open P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D
open P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D
open P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D

universe u v w

variable {Base : Type u} {E : Type v}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Minimal comparison data: differentiability on both sides and equality of
the one-forms.  Derivative equality is deliberately not an input. -/
structure DifferentiableOperatorGeometricBismutFreedFromOneFormData
    (actual reference : Base → E →L[Real] E) where
  operator : DifferentiableRelativeIntrinsicTraceOneFormData.{u, v, w}
    actual reference
  geometric : DifferentiableLinearGeometricBismutFreedOneFormData Base
  oneForm_agreement : ∀ base direction,
    geometric.geometry.oneForm base direction =
      ((operator.trace.bismutFreedRealOneForm base direction : Real) : Complex)

namespace DifferentiableOperatorGeometricBismutFreedFromOneFormData

/-- Equality of derivatives follows from uniqueness of the Frechet derivative
after evaluating the covector fields on a fixed tangent vector. -/
theorem derivative_agreement
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableOperatorGeometricBismutFreedFromOneFormData.{u, v, w}
      actual reference)
    (base first second : Base) :
    data.geometric.derivative base first second =
      ((data.operator.bismutFreedOneFormDerivative base first second : Real) :
        Complex) := by
  have hGeometric :
      HasFDerivAt
        (fun current ↦ data.geometric.geometry.oneForm current second)
        ((data.geometric.derivative base).flip second) base := by
    simpa using
      (data.geometric.hasFDerivAt_oneForm base).clm_apply
        (hasFDerivAt_const (x := base) (c := second))
  have hOperatorReal :
      HasFDerivAt
        (fun current ↦
          data.operator.trace.bismutFreedRealOneForm current second)
        ((data.operator.bismutFreedOneFormDerivative base).flip second) base := by
    simpa using
      (data.operator.hasFDerivAt_bismutFreedRealOneForm base).clm_apply
        (hasFDerivAt_const (x := base) (c := second))
  have hGeometricRe :
      HasFDerivAt
        (fun current ↦
          (data.geometric.geometry.oneForm current second).re)
        (Complex.reCLM.comp ((data.geometric.derivative base).flip second))
        base := by
    exact Complex.reCLM.hasFDerivAt.comp base hGeometric
  have hFunctionsRe :
      (fun current ↦ (data.geometric.geometry.oneForm current second).re) =
        (fun current ↦
          data.operator.trace.bismutFreedRealOneForm current second) := by
    funext current
    rw [data.oneForm_agreement current second]
    simp
  rw [hFunctionsRe] at hGeometricRe
  have hRealDerivativeMaps := hGeometricRe.unique hOperatorReal
  have hRealApplied := DFunLike.congr_fun hRealDerivativeMaps first
  have hGeometricIm :
      HasFDerivAt
        (fun current ↦
          (data.geometric.geometry.oneForm current second).im)
        (Complex.imCLM.comp ((data.geometric.derivative base).flip second))
        base := by
    exact Complex.imCLM.hasFDerivAt.comp base hGeometric
  have hFunctionsIm :
      (fun current ↦ (data.geometric.geometry.oneForm current second).im) =
        (fun _ ↦ (0 : Real)) := by
    funext current
    rw [data.oneForm_agreement current second]
    simp
  rw [hFunctionsIm] at hGeometricIm
  have hZero :
      HasFDerivAt (fun _ : Base ↦ (0 : Real))
        (0 : Base →L[Real] Real) base :=
    hasFDerivAt_const (x := base) (c := (0 : Real))
  have hImaginaryDerivativeMaps := hGeometricIm.unique hZero
  have hImaginaryApplied := DFunLike.congr_fun hImaginaryDerivativeMaps first
  rw [show (0 : Base →L[Real] Real) first = 0 by rfl] at hImaginaryApplied
  apply Complex.ext
  · simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, Complex.reCLM_apply,
      Complex.ofReal_re] using hRealApplied
  · simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, Complex.imCLM_apply,
      Complex.ofReal_im] using hImaginaryApplied

/-- Canonical full comparison packet. -/
def toDifferentiableOperatorGeometricBismutFreedComparisonData
    {actual reference : Base → E →L[Real] E}
    (data : DifferentiableOperatorGeometricBismutFreedFromOneFormData.{u, v, w}
      actual reference) :
    DifferentiableOperatorGeometricBismutFreedComparisonData.{u, v, w}
      actual reference where
  operator := data.operator
  geometric := data.geometric
  oneForm_agreement := data.oneForm_agreement
  derivative_agreement := data.derivative_agreement

/-- Public checkpoint: the one-form identity alone yields the full curvature
comparison with the intrinsic trace expression. -/
theorem differentiable_operator_geometric_bismut_freed_from_one_form_gate
    (actual reference : Base → E →L[Real] E)
    (data : DifferentiableOperatorGeometricBismutFreedFromOneFormData.{u, v, w}
      actual reference) :
    (∀ base first second,
      data.geometric.derivative base first second =
        ((data.operator.bismutFreedOneFormDerivative base first second : Real) :
          Complex)) ∧
    (∀ base first second,
      data.geometric.curvature base first second =
        ((data.operator.bismutFreedTraceCurvature base first second : Real) :
          Complex)) :=
  ⟨data.derivative_agreement,
    (data.toDifferentiableOperatorGeometricBismutFreedComparisonData).curvature_eq_operatorTrace⟩

end DifferentiableOperatorGeometricBismutFreedFromOneFormData

end
end P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparisonFromOneForm4D
end JanusFormal
