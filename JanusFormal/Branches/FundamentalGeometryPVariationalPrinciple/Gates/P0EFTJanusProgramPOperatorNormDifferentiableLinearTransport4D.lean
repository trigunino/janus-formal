import Mathlib.Analysis.Calculus.Deriv.Mul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D

/-!
# Operator-norm differentiable linear transport

A possibly unbounded algebraic presentation of transport can be accompanied by
a continuous-linear representative.  One operator-valued derivative then
implies differentiability of every transported fixed vector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPOperatorNormDifferentiableLinearTransport4D

set_option autoImplicit false
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D

/-- Operator-norm regularity for an algebraically presented linear transport. -/
structure OperatorNormDifferentiableLinearTransportData
    (transport : Real → E → E) where
  operator : Real → E →L[Real] E
  operator_apply : ∀ parameter vector,
    operator parameter vector = transport parameter vector
  derivative : Real → E →L[Real] E
  hasDerivAt_operator : ∀ parameter,
    HasDerivAt operator (derivative parameter) parameter

namespace OperatorNormDifferentiableLinearTransportData

/-- A unitary operator-norm frame represents any pointwise equal algebraic
transport. -/
def ofUnitaryFrameAgreement
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace Real U]
    {transport : Real → U → U}
    (frame : Real → U ≃ₗᵢ[Real] U)
    (data : OperatorNormDifferentiableUnitaryFrameData frame)
    (agreement : ∀ parameter vector,
      frame parameter vector = transport parameter vector) :
    OperatorNormDifferentiableLinearTransportData transport where
  operator := unitaryFrameOperator frame
  operator_apply := agreement
  derivative := data.derivative
  hasDerivAt_operator := data.hasDerivAt_frame

/-- Specialization when the algebraic transport is the unitary frame itself. -/
def ofUnitaryFrame
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace Real U]
    (frame : Real → U ≃ₗᵢ[Real] U)
    (data : OperatorNormDifferentiableUnitaryFrameData frame) :
    OperatorNormDifferentiableLinearTransportData
      (fun parameter vector => frame parameter vector) :=
  ofUnitaryFrameAgreement frame data (fun _ _ => rfl)

/-- Evaluation on a fixed vector inherits the operator derivative. -/
theorem hasDerivAt_apply
    {transport : Real → E → E}
    (data : OperatorNormDifferentiableLinearTransportData transport)
    (parameter : Real) (vector : E) :
    HasDerivAt (fun current => transport current vector)
      (data.derivative parameter vector) parameter := by
  have hzero : transport parameter 0 = 0 := by
    rw [← data.operator_apply]
    exact map_zero (data.operator parameter)
  simpa only [data.operator_apply, hzero, add_zero] using
    (data.hasDerivAt_operator parameter).clm_apply
      (hasDerivAt_const parameter vector)

/-- Every fixed vector transported by an operator-norm differentiable family is
differentiable. -/
theorem differentiable_apply
    {transport : Real → E → E}
    (data : OperatorNormDifferentiableLinearTransportData transport)
    (vector : E) :
    Differentiable Real (fun parameter => transport parameter vector) :=
  fun parameter => (data.hasDerivAt_apply parameter vector).differentiableAt

/-- Public operator-norm linear-transport checkpoint. -/
theorem operator_norm_differentiable_linear_transport_gate
    (transport : Real → E → E)
    (data : OperatorNormDifferentiableLinearTransportData transport) :
    Differentiable Real data.operator ∧
      ∀ vector, Differentiable Real (fun parameter => transport parameter vector) :=
  ⟨fun parameter => (data.hasDerivAt_operator parameter).differentiableAt,
    data.differentiable_apply⟩

end OperatorNormDifferentiableLinearTransportData

end
end P0EFTJanusProgramPOperatorNormDifferentiableLinearTransport4D
end JanusFormal
