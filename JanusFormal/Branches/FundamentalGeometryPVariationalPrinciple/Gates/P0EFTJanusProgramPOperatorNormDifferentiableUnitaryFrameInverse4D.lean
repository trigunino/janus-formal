import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Comp
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameConnection4D

/-!
# Derivative of the inverse unitary frame

Let `F_a` be an operator-norm differentiable unitary frame with derivative
`K_a`.  The inverse frame is the Hilbert adjoint:

```text
F_a⁻¹ = F_a†.
```

Over the real field, taking the adjoint is a continuous linear operation on the
operator space, hence

```text
(F_a⁻¹)' = K_a†.
```

The differentiated metric identity then identifies this derivative with the
standard inverse formula

```text
(F_a⁻¹)' = -F_a⁻¹ K_a F_a⁻¹.
```
-/

namespace JanusFormal
namespace P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- The inverse unitary frame as a continuous linear operator. -/
def inverseUnitaryFrameOperator
    (frame : Real → E ≃ₗᵢ[Real] E)
    (parameter : Real) : E →L[Real] E :=
  (frame parameter).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem inverseUnitaryFrameOperator_apply
    (frame : Real → E ≃ₗᵢ[Real] E)
    (parameter : Real) (vector : E) :
    inverseUnitaryFrameOperator frame parameter vector =
      (frame parameter).symm vector :=
  rfl

/-- Over `Real`, the Hilbert adjoint is an ordinary linear map of operator
spaces. -/
def realAdjointLinearMap :
    (E →L[Real] E) →ₗ[Real] (E →L[Real] E) where
  toFun := ContinuousLinearMap.adjoint
  map_add' := by
    intro first second
    exact map_add ContinuousLinearMap.adjoint first second
  map_smul' := by
    intro scalar operator
    simpa using
      map_smulₛₗ ContinuousLinearMap.adjoint scalar operator

/-- Continuous-linear packaging of the real adjoint operation. -/
def realAdjointContinuousLinearMap :
    (E →L[Real] E) →L[Real] (E →L[Real] E) :=
  realAdjointLinearMap.mkContinuous 1 (by
    intro operator
    change ‖ContinuousLinearMap.adjoint operator‖ ≤ 1 * ‖operator‖
    rw [ContinuousLinearMap.adjoint.norm_map, one_mul])

@[simp]
theorem realAdjointContinuousLinearMap_apply
    (operator : E →L[Real] E) :
    realAdjointContinuousLinearMap operator =
      ContinuousLinearMap.adjoint operator :=
  rfl

/-- The inverse of a unitary map is its Hilbert adjoint. -/
theorem inverseUnitaryFrameOperator_eq_adjoint
    (frame : Real → E ≃ₗᵢ[Real] E)
    (parameter : Real) :
    inverseUnitaryFrameOperator frame parameter =
      ContinuousLinearMap.adjoint (unitaryFrameOperator frame parameter) := by
  apply ContinuousLinearMap.ext
  intro vector
  apply ext_inner_right Real
  intro test
  calc
    inner Real (inverseUnitaryFrameOperator frame parameter vector) test =
        inner Real
          (frame parameter
            (inverseUnitaryFrameOperator frame parameter vector))
          (frame parameter test) :=
      ((frame parameter).inner_map_map
        (inverseUnitaryFrameOperator frame parameter vector) test).symm
    _ = inner Real vector (frame parameter test) := by
      rw [inverseUnitaryFrameOperator_apply,
        (frame parameter).apply_symm_apply]
    _ = inner Real
        (ContinuousLinearMap.adjoint
          (unitaryFrameOperator frame parameter) vector) test :=
      (ContinuousLinearMap.adjoint_inner_left
        (unitaryFrameOperator frame parameter) test vector).symm

namespace OperatorNormDifferentiableUnitaryFrameData

/-- Standard inverse derivative written using the frame and its derivative. -/
def inverseDerivative
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) : E →L[Real] E :=
  -((inverseUnitaryFrameOperator frame parameter).comp
      ((data.derivative parameter).comp
        (inverseUnitaryFrameOperator frame parameter)))

@[simp]
theorem inverseDerivative_apply
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) (vector : E) :
    data.inverseDerivative parameter vector =
      -(frame parameter).symm
        (data.derivative parameter ((frame parameter).symm vector)) :=
  rfl

/-- The adjoint of the frame derivative is the standard inverse derivative. -/
theorem adjoint_derivative_eq_inverseDerivative
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) :
    ContinuousLinearMap.adjoint (data.derivative parameter) =
      data.inverseDerivative parameter := by
  apply ContinuousLinearMap.ext
  intro vector
  apply ext_inner_right Real
  intro test
  have hMetric := data.frameDerivative_metric parameter
    ((frame parameter).symm vector) test
  rw [(frame parameter).apply_symm_apply] at hMetric
  calc
    inner Real
        (ContinuousLinearMap.adjoint (data.derivative parameter) vector) test =
      inner Real vector (data.derivative parameter test) :=
        ContinuousLinearMap.adjoint_inner_left
          (data.derivative parameter) test vector
    _ = -inner Real
        (data.derivative parameter ((frame parameter).symm vector))
        (frame parameter test) := by
      linarith
    _ = -inner Real
        ((frame parameter).symm
          (data.derivative parameter ((frame parameter).symm vector))) test := by
      have hInner := (frame parameter).inner_map_map
        ((frame parameter).symm
          (data.derivative parameter ((frame parameter).symm vector))) test
      rw [(frame parameter).apply_symm_apply] at hInner
      rw [hInner]
    _ = inner Real (data.inverseDerivative parameter vector) test := by
      rw [inverseDerivative_apply, inner_neg_left]

/-- The inverse frame is operator-norm differentiable with the standard inverse
formula. -/
theorem hasDerivAt_inverseUnitaryFrameOperator
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) :
    HasDerivAt (inverseUnitaryFrameOperator frame)
      (data.inverseDerivative parameter) parameter := by
  have hAdjoint :
      HasDerivAt
        (realAdjointContinuousLinearMap ∘ unitaryFrameOperator frame)
        (realAdjointContinuousLinearMap (data.derivative parameter))
        parameter :=
    realAdjointContinuousLinearMap.hasFDerivAt.comp_hasDerivAt parameter
      (data.hasDerivAt_frame parameter)
  have hInverse :
      HasDerivAt (inverseUnitaryFrameOperator frame)
        (ContinuousLinearMap.adjoint (data.derivative parameter)) parameter := by
    convert hAdjoint using 1
    · funext current
      exact inverseUnitaryFrameOperator_eq_adjoint frame current
    · rfl
  rw [data.adjoint_derivative_eq_inverseDerivative parameter] at hInverse
  exact hInverse

/-- Public inverse-frame derivative checkpoint. -/
theorem operator_norm_differentiable_unitary_frame_inverse_gate
    (frame : Real → E ≃ₗᵢ[Real] E)
    (data : OperatorNormDifferentiableUnitaryFrameData frame) :
    (∀ parameter,
      HasDerivAt (inverseUnitaryFrameOperator frame)
        (data.inverseDerivative parameter) parameter) ∧
    (∀ parameter,
      data.inverseDerivative parameter =
        -((inverseUnitaryFrameOperator frame parameter).comp
          ((data.derivative parameter).comp
            (inverseUnitaryFrameOperator frame parameter)))) ∧
    (∀ parameter,
      ContinuousLinearMap.adjoint (data.derivative parameter) =
        data.inverseDerivative parameter) :=
  ⟨data.hasDerivAt_inverseUnitaryFrameOperator,
    fun _ => rfl,
    data.adjoint_derivative_eq_inverseDerivative⟩

end OperatorNormDifferentiableUnitaryFrameData

end
end P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D
end JanusFormal
