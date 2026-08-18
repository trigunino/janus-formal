import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRealLineIntrinsicTraceOneFormRestriction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedFinitePartOneFormTerminal4D

/-!
# Relative BF terminal with canonical real-line trace restriction

This frontend removes the scalar/unit-direction trace compatibility premise
from the finite-part/one-form terminal.  The scalar trace packet is constructed
canonically by restricting the real-line Frechet trace one-form to direction
`1`.  The geometric one-form comparison remains genuine input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeBismutFreedRealLineRestrictionTerminal4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeBismutFreedTraceConnectionFromFinitePart4D
open P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparisonFromOneForm4D
open P0EFTJanusProgramPRealLineIntrinsicTraceOneFormRestriction4D
open P0EFTJanusProgramPRelativeBismutFreedFinitePartOneFormTerminal4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Real finite-part outputs together with the genuine geometric one-form
comparison.  No scalar trace packet or scalar/directional compatibility is
supplied independently. -/
structure RelativeBismutFreedRealLineRestrictionTerminalData
    (actual reference : Real → E →L[Real] E) where
  differential :
    DifferentiableOperatorGeometricBismutFreedFromOneFormData.{0, u, v}
      actual reference
  zetaFamily : RelativeHeatMellinZetaFamilyData
  finitePartLogDerivative_eq_trace : ∀ parameter,
    zetaFamily.finitePartFamily.logDerivative parameter =
      (toScalarRelativeIntrinsicTrace differential.operator.trace).trace
        parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (zetaFamily.zetaPrimeAtZero parameter).im = 0

namespace RelativeBismutFreedRealLineRestrictionTerminalData

/-- Finite-part trace-connection packet using the canonical scalar
restriction. -/
def toFinitePartTraceConnection
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedRealLineRestrictionTerminalData.{u, v}
      actual reference) :
    RelativeBismutFreedFinitePartTraceConnectionData.{u, v}
      actual reference where
  operatorTrace :=
    toScalarRelativeIntrinsicTrace data.differential.operator.trace
  zetaFamily := data.zetaFamily
  finitePartLogDerivative_eq_trace := data.finitePartLogDerivative_eq_trace
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The earlier terminal packet, now with its unit-direction compatibility
proved rather than supplied. -/
def toFinitePartOneFormTerminal
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedRealLineRestrictionTerminalData.{u, v}
      actual reference) :
    RelativeBismutFreedFinitePartOneFormTerminalData.{u, v, v}
      actual reference where
  finitePart := data.toFinitePartTraceConnection
  differential := data.differential
  unit_direction_trace_agreement := fun parameter ↦
    (toScalarRelativeIntrinsicTrace_trace_eq_directionalTrace
      data.differential.operator.trace parameter).symm

/-- The zeta connection coefficient is the genuine geometric BF one-form in
the unit parameter direction. -/
theorem connectionCoefficient_eq_geometricOneForm
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedRealLineRestrictionTerminalData.{u, v}
      actual reference)
    (parameter : Real) :
    relativeZetaConnectionCoefficient data.zetaFamily.toZetaFamily parameter =
      data.differential.geometric.geometry.oneForm parameter 1 :=
  data.toFinitePartOneFormTerminal.connectionCoefficient_eq_geometricOneForm
    parameter

/-- Public checkpoint: scalar trace compatibility has disappeared, while the
geometric one-form comparison remains explicit in `differential`. -/
theorem relative_bismut_freed_real_line_restriction_terminal_gate
    (actual reference : Real → E →L[Real] E)
    (data : RelativeBismutFreedRealLineRestrictionTerminalData.{u, v}
      actual reference) :
    (∀ parameter,
      relativeZetaConnectionCoefficient data.zetaFamily.toZetaFamily parameter =
        data.differential.geometric.geometry.oneForm parameter 1) ∧
    (∀ parameter first second,
      data.differential.geometric.derivative parameter first second =
        ((data.differential.operator.bismutFreedOneFormDerivative
          parameter first second : Real) : Complex)) ∧
    (∀ parameter first second,
      data.differential.geometric.curvature parameter first second =
        ((data.differential.operator.bismutFreedTraceCurvature
          parameter first second : Real) : Complex)) :=
  ⟨data.connectionCoefficient_eq_geometricOneForm,
    data.toFinitePartOneFormTerminal.derivative_agreement,
    data.toFinitePartOneFormTerminal.curvature_eq_operatorTrace⟩

end RelativeBismutFreedRealLineRestrictionTerminalData

end
end P0EFTJanusProgramPRelativeBismutFreedRealLineRestrictionTerminal4D
end JanusFormal
