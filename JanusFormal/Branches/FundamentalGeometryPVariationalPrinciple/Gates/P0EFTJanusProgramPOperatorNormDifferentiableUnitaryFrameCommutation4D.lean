import Mathlib.Analysis.Calculus.Deriv.Mul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameInverse4D

/-!
# Fixed-operator commutation for a differentiable unitary frame

Suppose a unitary frame commutes with one fixed bounded operator `P`:

```text
F_a P = P F_a.
```

Differentiating this identity in operator norm gives

```text
F'_a P = P F'_a.
```

The inverse frame also commutes with `P`, and therefore both logarithmic
frame derivatives

```text
F_a⁻¹ F'_a,
F'_a F_a⁻¹
```

commute with `P`.  Applied to the five fixed Candidate-A sector projectors,
this says that the D11 connection cannot mix physical sectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameCommutation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameConnection4D
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameInverse4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- One fixed operator commuting with every member of a unitary frame. -/
structure FrameCommutesWithFixedOperatorData
    (frame : Real → E ≃ₗᵢ[Real] E)
    (fixedOperator : E →L[Real] E) : Prop where
  commute : ∀ parameter,
    (unitaryFrameOperator frame parameter).comp fixedOperator =
      fixedOperator.comp (unitaryFrameOperator frame parameter)

namespace OperatorNormDifferentiableUnitaryFrameData

/-- Differentiating exact frame commutation gives derivative commutation. -/
theorem derivative_commutes_fixedOperator
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (fixedOperator : E →L[Real] E)
    (commutation : FrameCommutesWithFixedOperatorData frame fixedOperator)
    (parameter : Real) :
    (data.derivative parameter).comp fixedOperator =
      fixedOperator.comp (data.derivative parameter) := by
  have hFixed :
      HasDerivAt (fun _ : Real => fixedOperator) 0 parameter :=
    hasDerivAt_const parameter fixedOperator
  have hLeft :
      HasDerivAt
        (fun current : Real =>
          (unitaryFrameOperator frame current).comp fixedOperator)
        ((data.derivative parameter).comp fixedOperator) parameter := by
    simpa using (data.hasDerivAt_frame parameter).clm_comp hFixed
  have hRight :
      HasDerivAt
        (fun current : Real =>
          fixedOperator.comp (unitaryFrameOperator frame current))
        (fixedOperator.comp (data.derivative parameter)) parameter := by
    simpa using hFixed.clm_comp (data.hasDerivAt_frame parameter)
  have hRightOnLeft :
      HasDerivAt
        (fun current : Real =>
          (unitaryFrameOperator frame current).comp fixedOperator)
        (fixedOperator.comp (data.derivative parameter)) parameter := by
    convert hRight using 1
    funext current
    exact (commutation.commute current).symm
  exact hLeft.unique hRightOnLeft

/-- The inverse frame commutes with every fixed operator commuting with the
forward frame. -/
theorem inverseFrame_commutes_fixedOperator
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (fixedOperator : E →L[Real] E)
    (commutation : FrameCommutesWithFixedOperatorData frame fixedOperator)
    (parameter : Real) :
    (inverseUnitaryFrameOperator frame parameter).comp fixedOperator =
      fixedOperator.comp (inverseUnitaryFrameOperator frame parameter) := by
  ext vector
  apply (frame parameter).injective
  rw [(frame parameter).apply_symm_apply]
  have hCommute := congrArg
    (fun operator : E →L[Real] E =>
      operator ((frame parameter).symm vector))
    (commutation.commute parameter)
  simp only [ContinuousLinearMap.comp_apply,
    unitaryFrameOperator_apply] at hCommute
  rw [hCommute, (frame parameter).apply_symm_apply]

/-- The left Maurer--Cartan coefficient preserves the same fixed operator. -/
theorem leftLogDerivative_commutes_fixedOperator
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (fixedOperator : E →L[Real] E)
    (commutation : FrameCommutesWithFixedOperatorData frame fixedOperator)
    (parameter : Real) :
    (data.leftLogDerivative parameter).comp fixedOperator =
      fixedOperator.comp (data.leftLogDerivative parameter) := by
  have hDerivative :=
    data.derivative_commutes_fixedOperator fixedOperator commutation parameter
  have hInverse :=
    data.inverseFrame_commutes_fixedOperator fixedOperator commutation parameter
  ext vector
  have hDerivativeApply := congrArg
    (fun operator : E →L[Real] E => operator vector) hDerivative
  have hInverseApply := congrArg
    (fun operator : E →L[Real] E =>
      operator (data.derivative parameter vector)) hInverse
  simp only [ContinuousLinearMap.comp_apply] at hDerivativeApply hInverseApply ⊢
  rw [hDerivativeApply]
  exact hInverseApply

/-- The right Maurer--Cartan coefficient also preserves the fixed operator. -/
theorem rightLogDerivative_commutes_fixedOperator
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (fixedOperator : E →L[Real] E)
    (commutation : FrameCommutesWithFixedOperatorData frame fixedOperator)
    (parameter : Real) :
    (data.rightLogDerivative parameter).comp fixedOperator =
      fixedOperator.comp (data.rightLogDerivative parameter) := by
  have hDerivative :=
    data.derivative_commutes_fixedOperator fixedOperator commutation parameter
  have hInverse :=
    data.inverseFrame_commutes_fixedOperator fixedOperator commutation parameter
  ext vector
  have hInverseApply := congrArg
    (fun operator : E →L[Real] E => operator vector) hInverse
  have hDerivativeApply := congrArg
    (fun operator : E →L[Real] E =>
      operator (inverseUnitaryFrameOperator frame parameter vector)) hDerivative
  simp only [ContinuousLinearMap.comp_apply] at hInverseApply hDerivativeApply ⊢
  rw [← hInverseApply]
  exact hDerivativeApply

/-- Public fixed-operator commutation checkpoint. -/
theorem operator_norm_differentiable_unitary_frame_commutation_gate
    (frame : Real → E ≃ₗᵢ[Real] E)
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (fixedOperator : E →L[Real] E)
    (commutation : FrameCommutesWithFixedOperatorData frame fixedOperator) :
    (∀ parameter,
      (data.derivative parameter).comp fixedOperator =
        fixedOperator.comp (data.derivative parameter)) ∧
    (∀ parameter,
      (inverseUnitaryFrameOperator frame parameter).comp fixedOperator =
        fixedOperator.comp (inverseUnitaryFrameOperator frame parameter)) ∧
    (∀ parameter,
      (data.leftLogDerivative parameter).comp fixedOperator =
        fixedOperator.comp (data.leftLogDerivative parameter)) ∧
    (∀ parameter,
      (data.rightLogDerivative parameter).comp fixedOperator =
        fixedOperator.comp (data.rightLogDerivative parameter)) :=
  ⟨data.derivative_commutes_fixedOperator fixedOperator commutation,
    data.inverseFrame_commutes_fixedOperator fixedOperator commutation,
    data.leftLogDerivative_commutes_fixedOperator fixedOperator commutation,
    data.rightLogDerivative_commutes_fixedOperator fixedOperator commutation⟩

end OperatorNormDifferentiableUnitaryFrameData

end
end P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameCommutation4D
end JanusFormal
