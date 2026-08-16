import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Intrinsic traces of logarithmic operator derivatives

For a differentiable invertible family `H_a`, the local logarithmic determinant
variation is represented by

`G_a H'_a`,

where `G_a = H_a⁻¹`.  In infinite dimension this expression may be traced only
after a genuine nuclear theorem.  The packet below therefore requires an
`IntrinsicNuclearTraceData` certificate for this exact operator at every
parameter.

For a relative determinant the Bismut--Freed one-form is the difference of the
actual and reference logarithmic traces.  No scalar zeta family is involved at
this stage.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- A differentiable uniformly invertible family whose logarithmic derivative
is intrinsically nuclear at every parameter. -/
structure IntrinsicLogarithmicDerivativeTraceData
    (operator : Real → E →L[Real] E) where
  family : DifferentiableSelfAdjointUniformGapFamilyData operator
  inverse : family.GreenDifferentiabilityData
  traceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v}
      (family.logarithmicDerivativeOperator parameter)

namespace IntrinsicLogarithmicDerivativeTraceData

/-- Canonical scalar trace `Tr(G_a H'_a)`. -/
def trace
    {operator : Real → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceData.{u, v} operator)
    (parameter : Real) : Real :=
  intrinsicNuclearTrace (data.traceClass parameter)

/-- Every certified expansion of `G_a H'_a` computes the same scalar. -/
theorem expansionTrace_eq
    {operator : Real → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceData.{u, v} operator)
    (parameter : Real)
    (expansion : SummableRankOneOperatorExpansion.{v, u}
      (data.family.logarithmicDerivativeOperator parameter)) :
    expansion.expansionTrace = data.trace parameter :=
  (data.traceClass parameter).expansionTrace_eq expansion

/-- The logarithmic derivative operator is compact. -/
theorem logarithmicDerivative_compact
    {operator : Real → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceData.{u, v} operator)
    (parameter : Real) :
    IsCompactOperator
      (data.family.logarithmicDerivativeOperator parameter) :=
  (data.traceClass parameter).operator_compact

/-- The derivative of the Green family remains the canonical `-G H' G`. -/
theorem greenDerivative_formula
    {operator : Real → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceData.{u, v} operator)
    (parameter : Real) :
    data.inverse.greenDerivative parameter =
      -((data.family.analytic.green parameter).comp
        ((data.family.derivative parameter).comp
          (data.family.analytic.green parameter))) :=
  data.inverse.derivative_formula parameter

/-- Public logarithmic-trace checkpoint. -/
theorem intrinsic_logarithmic_derivative_trace_gate
    (operator : Real → E →L[Real] E)
    (data : IntrinsicLogarithmicDerivativeTraceData.{u, v} operator) :
    (∀ parameter,
      IsCompactOperator
        (data.family.logarithmicDerivativeOperator parameter)) ∧
      (∀ parameter,
        ∀ expansion : SummableRankOneOperatorExpansion.{v, u}
          (data.family.logarithmicDerivativeOperator parameter),
          expansion.expansionTrace = data.trace parameter) ∧
      (∀ parameter,
        data.inverse.greenDerivative parameter =
          -((data.family.analytic.green parameter).comp
            ((data.family.derivative parameter).comp
              (data.family.analytic.green parameter)))) :=
  ⟨data.logarithmicDerivative_compact,
    data.expansionTrace_eq,
    data.greenDerivative_formula⟩

end IntrinsicLogarithmicDerivativeTraceData

/-- Actual-minus-reference logarithmic trace packet.  Both families act on the
same fixed reduced Hilbert space, as required after a kernel-complement
trivialization. -/
structure RelativeIntrinsicLogarithmicDerivativeTraceData
    (actual reference : Real → E →L[Real] E) where
  actualTrace : IntrinsicLogarithmicDerivativeTraceData.{u, v} actual
  referenceTrace : IntrinsicLogarithmicDerivativeTraceData.{u, v} reference

namespace RelativeIntrinsicLogarithmicDerivativeTraceData

/-- Relative logarithmic trace
`Tr(G_actual H'_actual) - Tr(G_ref H'_ref)`. -/
def trace
    {actual reference : Real → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceData.{u, v} actual reference)
    (parameter : Real) : Real :=
  data.actualTrace.trace parameter - data.referenceTrace.trace parameter

/-- Complex Bismut--Freed coefficient in the zeta-prime convention.

The determinant coordinate is `exp (-zetaPrimeAtZero)`, so the connection
coefficient is the negative of the logarithmic determinant variation. -/
def bismutFreedCoefficient
    {actual reference : Real → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceData.{u, v} actual reference)
    (parameter : Real) : Complex :=
  (-(data.trace parameter) : Real)

/-- Real part of the coefficient. -/
@[simp]
theorem bismutFreedCoefficient_re
    {actual reference : Real → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceData.{u, v} actual reference)
    (parameter : Real) :
    (data.bismutFreedCoefficient parameter).re = -data.trace parameter := by
  rfl

/-- Public relative logarithmic-trace checkpoint. -/
theorem relative_intrinsic_logarithmic_derivative_trace_gate
    (actual reference : Real → E →L[Real] E)
    (data : RelativeIntrinsicLogarithmicDerivativeTraceData.{u, v} actual reference) :
    (∀ parameter,
      data.trace parameter =
        data.actualTrace.trace parameter -
          data.referenceTrace.trace parameter) ∧
      (∀ parameter,
        data.bismutFreedCoefficient parameter =
          (-(data.trace parameter) : Real)) ∧
      (∀ parameter,
        (data.bismutFreedCoefficient parameter).re = -data.trace parameter) :=
  ⟨fun _ => rfl, fun _ => rfl, data.bismutFreedCoefficient_re⟩

end RelativeIntrinsicLogarithmicDerivativeTraceData

end
end P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
end JanusFormal
