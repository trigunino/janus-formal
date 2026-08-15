import Mathlib.Analysis.Calculus.Deriv.Mul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameInverse4D

/-!
# Derivative of an operator family obtained by unitary conjugation

Let `F_a` be an operator-norm differentiable unitary frame and let `B` be a
fixed bounded operator.  Define

```text
C_a = F_a B F_a⁻¹.
```

Using the inverse derivative from the preceding layer and the bilinear
composition rule for continuous linear maps, this file proves

```text
C'_a = F'_a B F_a⁻¹ + F_a B (F_a⁻¹)'.
```

Writing

```text
A_a = F'_a F_a⁻¹
```

for the right Maurer--Cartan coefficient, the derivative becomes the exact
commutator

```text
C'_a = A_a C_a - C_a A_a.
```
-/

namespace JanusFormal
namespace P0EFTJanusProgramPOperatorNormDifferentiableUnitaryConjugation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameConnection4D
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameInverse4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Commutator convention `[first, second] = first ∘ second - second ∘ first`. -/
def continuousLinearMapCommutator
    (first second : E →L[Real] E) : E →L[Real] E :=
  first.comp second - second.comp first

/-- Unitary conjugation of one fixed bounded operator. -/
def conjugatedConstantOperator
    (frame : Real → E ≃ₗᵢ[Real] E)
    (baseOperator : E →L[Real] E)
    (parameter : Real) : E →L[Real] E :=
  (unitaryFrameOperator frame parameter).comp
    (baseOperator.comp (inverseUnitaryFrameOperator frame parameter))

@[simp]
theorem conjugatedConstantOperator_apply
    (frame : Real → E ≃ₗᵢ[Real] E)
    (baseOperator : E →L[Real] E)
    (parameter : Real) (vector : E) :
    conjugatedConstantOperator frame baseOperator parameter vector =
      frame parameter
        (baseOperator ((frame parameter).symm vector)) :=
  rfl

namespace OperatorNormDifferentiableUnitaryFrameData

/-- Product-rule derivative of the conjugated operator family. -/
def conjugatedDerivative
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (baseOperator : E →L[Real] E)
    (parameter : Real) : E →L[Real] E :=
  (data.derivative parameter).comp
      (baseOperator.comp (inverseUnitaryFrameOperator frame parameter)) +
    (unitaryFrameOperator frame parameter).comp
      (baseOperator.comp (data.inverseDerivative parameter))

/-- The conjugated constant operator is differentiable with the displayed
product-rule derivative. -/
theorem hasDerivAt_conjugatedConstantOperator
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (baseOperator : E →L[Real] E)
    (parameter : Real) :
    HasDerivAt (conjugatedConstantOperator frame baseOperator)
      (data.conjugatedDerivative baseOperator parameter) parameter := by
  have hBase :
      HasDerivAt (fun _ : Real => baseOperator) 0 parameter :=
    hasDerivAt_const parameter baseOperator
  have hInverse := data.hasDerivAt_inverseUnitaryFrameOperator parameter
  have hInner :
      HasDerivAt
        (fun current : Real =>
          baseOperator.comp (inverseUnitaryFrameOperator frame current))
        (baseOperator.comp (data.inverseDerivative parameter)) parameter := by
    convert hBase.clm_comp hInverse using 1
    simp
  have hOuter := data.hasDerivAt_frame parameter
  exact hOuter.clm_comp hInner

/-- The product-rule derivative is the commutator with the moving-frame
connection coefficient. -/
theorem conjugatedDerivative_eq_commutator
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (baseOperator : E →L[Real] E)
    (parameter : Real) :
    data.conjugatedDerivative baseOperator parameter =
      continuousLinearMapCommutator
        (data.rightLogDerivative parameter)
        (conjugatedConstantOperator frame baseOperator parameter) := by
  ext vector
  simp [conjugatedDerivative, continuousLinearMapCommutator,
    conjugatedConstantOperator, rightLogDerivative, inverseDerivative]

/-- Direct commutator-valued derivative statement. -/
theorem hasDerivAt_conjugatedConstantOperator_commutator
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (baseOperator : E →L[Real] E)
    (parameter : Real) :
    HasDerivAt (conjugatedConstantOperator frame baseOperator)
      (continuousLinearMapCommutator
        (data.rightLogDerivative parameter)
        (conjugatedConstantOperator frame baseOperator parameter)) parameter := by
  rw [← data.conjugatedDerivative_eq_commutator baseOperator parameter]
  exact data.hasDerivAt_conjugatedConstantOperator baseOperator parameter

/-- Public unitary-conjugation derivative checkpoint. -/
theorem operator_norm_differentiable_unitary_conjugation_gate
    (frame : Real → E ≃ₗᵢ[Real] E)
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (baseOperator : E →L[Real] E) :
    (∀ parameter,
      HasDerivAt (conjugatedConstantOperator frame baseOperator)
        (data.conjugatedDerivative baseOperator parameter) parameter) ∧
    (∀ parameter,
      data.conjugatedDerivative baseOperator parameter =
        continuousLinearMapCommutator
          (data.rightLogDerivative parameter)
          (conjugatedConstantOperator frame baseOperator parameter)) ∧
    (∀ parameter,
      HasDerivAt (conjugatedConstantOperator frame baseOperator)
        (continuousLinearMapCommutator
          (data.rightLogDerivative parameter)
          (conjugatedConstantOperator frame baseOperator parameter)) parameter) :=
  ⟨data.hasDerivAt_conjugatedConstantOperator baseOperator,
    data.conjugatedDerivative_eq_commutator baseOperator,
    data.hasDerivAt_conjugatedConstantOperator_commutator baseOperator⟩

end OperatorNormDifferentiableUnitaryFrameData

end
end P0EFTJanusProgramPOperatorNormDifferentiableUnitaryConjugation4D
end JanusFormal
