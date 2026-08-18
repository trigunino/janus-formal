import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D

/-!
# Restriction of intrinsic trace one-forms to the real parameter line

For a Frechet-differentiable family already based on `Real`, the ordinary
one-parameter derivative is evaluation of its Frechet derivative on `1`.
Consequently the scalar intrinsic logarithmic trace is exactly the directional
trace one-form evaluated on `1`; no extra trace-comparison hypothesis is needed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRealLineIntrinsicTraceOneFormRestriction4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointUniformGapBaseFamily4D
open P0EFTJanusProgramPSelfAdjointUniformGapFamily4D
open P0EFTJanusProgramPFrechetDifferentiableSelfAdjointGreenBaseFamily4D
open P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- The arbitrary-base gap packet, specialized to `Real`, is the ordinary
one-parameter gap packet. -/
def toScalarGapFamily
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator) :
    SelfAdjointUniformGapFamilyData operator where
  selfAdjoint := data.selfAdjoint
  gap := data.gap
  gap_pos := data.gap_pos
  lowerBound := data.lowerBound

/-- The two canonical Green constructions agree pointwise. -/
theorem toScalarGapFamily_green_eq
    {operator : Real → E →L[Real] E}
    (data : SelfAdjointUniformGapBaseFamilyData operator)
    (parameter : Real) :
    (toScalarGapFamily data).green parameter = data.green parameter := by
  ext vector
  apply (data.bijective parameter).1
  rw [(toScalarGapFamily data).operator_green parameter vector,
    data.operator_green parameter vector]

/-- Evaluation of the Frechet derivative on `1` gives the ordinary derivative
packet. -/
def toScalarDifferentiableFamily
    {operator : Real → E →L[Real] E}
    (data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator) :
    DifferentiableSelfAdjointUniformGapFamilyData operator where
  analytic := toScalarGapFamily data.analytic
  derivative := fun parameter ↦ data.derivative parameter 1
  hasDerivAt_operator := fun parameter ↦ by
    simpa using (data.hasFDerivAt_operator parameter).hasDerivAt

/-- The Frechet Green derivative restricts to the ordinary Green derivative. -/
def toScalarGreenDifferentiability
    {operator : Real → E →L[Real] E}
    {data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator}
    (inverse : data.GreenFrechetDifferentiabilityData) :
    (toScalarDifferentiableFamily data).GreenDifferentiabilityData where
  greenDerivative := fun parameter ↦ inverse.greenDerivative parameter 1
  hasDerivAt_green := fun parameter ↦ by
    have hDerivative := (inverse.hasFDerivAt_green parameter).hasDerivAt
    have hGreen :
        (toScalarDifferentiableFamily data).analytic.green =
          data.analytic.green := by
      funext current
      exact toScalarGapFamily_green_eq data.analytic current
    rw [hGreen]
    exact hDerivative
  greenDerivative_eq := by
    intro parameter
    rw [inverse.greenDerivative_eq]
    unfold DifferentiableSelfAdjointUniformGapFamilyData.canonicalGreenDerivative
      FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData.canonicalGreenDirectionalDerivative
    simp only [toScalarDifferentiableFamily]
    rw [toScalarGapFamily_green_eq]

/-- Canonical one-parameter intrinsic trace packet obtained from the real-line
trace one-form packet. -/
def toScalarIntrinsicTrace
    {operator : Real → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceOneFormData.{0, u, v} operator) :
    IntrinsicLogarithmicDerivativeTraceData.{u, v} operator where
  family := toScalarDifferentiableFamily data.family
  inverse := toScalarGreenDifferentiability data.inverse
  traceClass := fun parameter ↦ by
    simpa [DifferentiableSelfAdjointUniformGapFamilyData.logarithmicDerivativeOperator,
      FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData.logarithmicDerivativeOperator,
      toScalarDifferentiableFamily, toScalarGapFamily_green_eq] using
      data.traceClass parameter 1

/-- The scalar intrinsic trace is exactly evaluation of the trace one-form in
the unit direction. -/
theorem toScalarIntrinsicTrace_trace_eq_directionalTrace
    {operator : Real → E →L[Real] E}
    (data : IntrinsicLogarithmicDerivativeTraceOneFormData.{0, u, v} operator)
    (parameter : Real) :
    (toScalarIntrinsicTrace data).trace parameter =
      data.directionalTrace parameter 1 := by
  unfold IntrinsicLogarithmicDerivativeTraceData.trace
    IntrinsicLogarithmicDerivativeTraceOneFormData.directionalTrace
    toScalarIntrinsicTrace
  rfl

/-- Relative scalar trace packet obtained without an independent presentation
or compatibility premise. -/
def toScalarRelativeIntrinsicTrace
    {actual reference : Real → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData.{0, u, v}
      actual reference) :
    RelativeIntrinsicLogarithmicDerivativeTraceData.{u, v}
      actual reference where
  actualTrace := toScalarIntrinsicTrace data.actualTrace
  referenceTrace := toScalarIntrinsicTrace data.referenceTrace

/-- Relative trace compatibility in the unit direction is automatic. -/
theorem toScalarRelativeIntrinsicTrace_trace_eq_directionalTrace
    {actual reference : Real → E →L[Real] E}
    (data : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData.{0, u, v}
      actual reference)
    (parameter : Real) :
    (toScalarRelativeIntrinsicTrace data).trace parameter =
      data.directionalTrace parameter 1 := by
  unfold RelativeIntrinsicLogarithmicDerivativeTraceData.trace
    RelativeIntrinsicLogarithmicDerivativeTraceOneFormData.directionalTrace
    toScalarRelativeIntrinsicTrace
  rw [toScalarIntrinsicTrace_trace_eq_directionalTrace,
    toScalarIntrinsicTrace_trace_eq_directionalTrace]

/-- Public real-line restriction checkpoint. -/
theorem real_line_intrinsic_trace_one_form_restriction_gate
    (actual reference : Real → E →L[Real] E)
    (data : RelativeIntrinsicLogarithmicDerivativeTraceOneFormData.{0, u, v}
      actual reference) :
    ∀ parameter,
      (toScalarRelativeIntrinsicTrace data).trace parameter =
        data.directionalTrace parameter 1 :=
  toScalarRelativeIntrinsicTrace_trace_eq_directionalTrace data

end
end P0EFTJanusProgramPRealLineIntrinsicTraceOneFormRestriction4D
end JanusFormal
