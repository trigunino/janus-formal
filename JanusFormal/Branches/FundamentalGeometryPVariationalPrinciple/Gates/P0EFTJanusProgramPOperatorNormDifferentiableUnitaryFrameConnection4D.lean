import Mathlib.Analysis.InnerProductSpace.Calculus
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D

/-!
# Connection generator of an operator-norm differentiable unitary frame

Let `F_a` be a unitary frame and let `K_a = F'_a` be its derivative in operator
norm.  Differentiating

```text
⟪F_a x, F_a y⟫ = ⟪x, y⟫
```

gives the first-order metric identity

```text
⟪K_a x, F_a y⟫ + ⟪F_a x, K_a y⟫ = 0.
```

Hence both Maurer--Cartan coefficients

```text
omega_left(a)  = F_a⁻¹ K_a,
omega_right(a) = K_a F_a⁻¹
```

are skew-adjoint.  The left convention agrees with the existing moving-frame
connection convention in the geometric layers of JanusFormal.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameConnection4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Real skew-adjointness written directly as the metric identity needed by the
frame connection. -/
def IsRealSkewAdjointOperator (operator : E →L[Real] E) : Prop :=
  ∀ first second,
    inner Real (operator first) second =
      -inner Real first (operator second)

namespace OperatorNormDifferentiableUnitaryFrameData

/-- Differentiated metric identity of the unitary frame. -/
theorem frameDerivative_metric
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) (first second : E) :
    inner Real (data.derivative parameter first) (frame parameter second) +
      inner Real (frame parameter first) (data.derivative parameter second) = 0 := by
  have hInner :=
    (data.hasDerivAt_apply parameter first).inner Real
      (data.hasDerivAt_apply parameter second)
  have hTransported :
      HasDerivAt
        (fun _ : Real => inner Real first second)
        (inner Real (frame parameter first) (data.derivative parameter second) +
          inner Real (data.derivative parameter first) (frame parameter second))
        parameter := by
    convert hInner using 1
    funext current
    exact (frame current).inner_map_map first second
  have hConstant :
      HasDerivAt (fun _ : Real => inner Real first second) 0 parameter :=
    hasDerivAt_const parameter (inner Real first second)
  have hDerivative := hTransported.unique hConstant
  linarith

/-- Left Maurer--Cartan coefficient `F_a⁻¹ F'_a` on the fixed Hilbert model. -/
def leftLogDerivative
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) : E →L[Real] E :=
  (frame parameter).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (data.derivative parameter)

@[simp]
theorem leftLogDerivative_apply
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) (vector : E) :
    data.leftLogDerivative parameter vector =
      (frame parameter).symm (data.derivative parameter vector) :=
  rfl

/-- The left logarithmic derivative is skew-adjoint. -/
theorem leftLogDerivative_skew
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) :
    IsRealSkewAdjointOperator (data.leftLogDerivative parameter) := by
  intro first second
  have hMetric := data.frameDerivative_metric parameter first second
  calc
    inner Real (data.leftLogDerivative parameter first) second =
        inner Real
          (frame parameter (data.leftLogDerivative parameter first))
          (frame parameter second) :=
      ((frame parameter).inner_map_map
        (data.leftLogDerivative parameter first) second).symm
    _ = inner Real (data.derivative parameter first)
        (frame parameter second) := by
      rw [leftLogDerivative_apply, (frame parameter).apply_symm_apply]
    _ = -inner Real (frame parameter first)
        (data.derivative parameter second) := by
      linarith
    _ = -inner Real first
        (data.leftLogDerivative parameter second) := by
      rw [leftLogDerivative_apply]
      have hInner := (frame parameter).inner_map_map first
        ((frame parameter).symm (data.derivative parameter second))
      rw [(frame parameter).apply_symm_apply] at hInner
      rw [hInner]

/-- Right Maurer--Cartan coefficient `F'_a F_a⁻¹` on the moving Hilbert model. -/
def rightLogDerivative
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) : E →L[Real] E :=
  (data.derivative parameter).comp
    (frame parameter).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem rightLogDerivative_apply
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) (vector : E) :
    data.rightLogDerivative parameter vector =
      data.derivative parameter ((frame parameter).symm vector) :=
  rfl

/-- The right logarithmic derivative is also skew-adjoint. -/
theorem rightLogDerivative_skew
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) :
    IsRealSkewAdjointOperator (data.rightLogDerivative parameter) := by
  intro first second
  have hMetric := data.frameDerivative_metric parameter
    ((frame parameter).symm first) ((frame parameter).symm second)
  simpa [rightLogDerivative] using hMetric

/-- The two coefficients are conjugate by the unitary frame. -/
theorem rightLogDerivative_eq_conjugate_left
    {frame : Real → E ≃ₗᵢ[Real] E}
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (parameter : Real) :
    data.rightLogDerivative parameter =
      (frame parameter).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((data.leftLogDerivative parameter).comp
          (frame parameter).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext vector
  simp [rightLogDerivative, leftLogDerivative]

/-- Public unitary-frame connection checkpoint. -/
theorem operator_norm_differentiable_unitary_frame_connection_gate
    (frame : Real → E ≃ₗᵢ[Real] E)
    (data : OperatorNormDifferentiableUnitaryFrameData frame) :
    (∀ parameter first second,
      inner Real (data.derivative parameter first) (frame parameter second) +
        inner Real (frame parameter first) (data.derivative parameter second) = 0) ∧
    (∀ parameter,
      IsRealSkewAdjointOperator (data.leftLogDerivative parameter)) ∧
    (∀ parameter,
      IsRealSkewAdjointOperator (data.rightLogDerivative parameter)) ∧
    (∀ parameter,
      data.rightLogDerivative parameter =
        (frame parameter).toContinuousLinearEquiv.toContinuousLinearMap.comp
          ((data.leftLogDerivative parameter).comp
            (frame parameter).symm.toContinuousLinearEquiv.toContinuousLinearMap)) :=
  ⟨data.frameDerivative_metric,
    data.leftLogDerivative_skew,
    data.rightLogDerivative_skew,
    data.rightLogDerivative_eq_conjugate_left⟩

end OperatorNormDifferentiableUnitaryFrameData

end
end P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameConnection4D
end JanusFormal
