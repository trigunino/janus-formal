import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedTraceConnectionFromFinitePart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparisonFromOneForm4D

/-!
# Relative Bismut--Freed terminal from finite parts and one-forms

The real finite-part identity reconstructs the scalar BF connection
coefficient.  Independently, equality of the differentiable geometric and
operator one-forms forces equality of their derivatives and curvatures.  The
single compatibility below identifies the scalar trace with evaluation of the
operator trace one-form on the unit parameter direction.

No local families-index comparison is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeBismutFreedFinitePartOneFormTerminal4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D
open P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D
open P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeBismutFreedTraceConnectionFromFinitePart4D
open P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparisonFromOneForm4D

universe u v w

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Honest terminal input.  The two analytic packets may use different nuclear
presentations; only their intrinsic scalar traces in the unit direction must
agree. -/
structure RelativeBismutFreedFinitePartOneFormTerminalData
    (actual reference : Real → E →L[Real] E) where
  finitePart : RelativeBismutFreedFinitePartTraceConnectionData.{u, v}
    actual reference
  differential :
    DifferentiableOperatorGeometricBismutFreedFromOneFormData.{0, u, w}
      actual reference
  unit_direction_trace_agreement : ∀ parameter,
    differential.operator.trace.directionalTrace parameter 1 =
      finitePart.operatorTrace.trace parameter

namespace RelativeBismutFreedFinitePartOneFormTerminalData

/-- The zeta connection coefficient is the geometric BF one-form evaluated on
the unit tangent direction. -/
theorem connectionCoefficient_eq_geometricOneForm
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedFinitePartOneFormTerminalData.{u, v, w}
      actual reference)
    (parameter : Real) :
    relativeZetaConnectionCoefficient
        data.finitePart.zetaFamily.toZetaFamily parameter =
      data.differential.geometric.geometry.oneForm parameter 1 := by
  calc
    relativeZetaConnectionCoefficient
        data.finitePart.zetaFamily.toZetaFamily parameter =
      data.finitePart.operatorTrace.bismutFreedCoefficient parameter :=
        data.finitePart.coefficient_agreement parameter
    _ = ((-data.finitePart.operatorTrace.trace parameter : Real) : Complex) :=
      rfl
    _ = ((-data.differential.operator.trace.directionalTrace
          parameter 1 : Real) : Complex) := by
      rw [data.unit_direction_trace_agreement parameter]
    _ = ((data.differential.operator.trace.bismutFreedRealOneForm
          parameter 1 : Real) : Complex) := by
      rw [data.differential.operator.trace.bismutFreedRealOneForm_apply]
      rfl
    _ = data.differential.geometric.geometry.oneForm parameter 1 :=
      (data.differential.oneForm_agreement parameter 1).symm

/-- The geometric one-form derivative is not an extra terminal hypothesis. -/
theorem derivative_agreement
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedFinitePartOneFormTerminalData.{u, v, w}
      actual reference)
    (parameter first second : Real) :
    data.differential.geometric.derivative parameter first second =
      ((data.differential.operator.bismutFreedOneFormDerivative
        parameter first second : Real) : Complex) :=
  data.differential.derivative_agreement parameter first second

/-- The derived geometric curvature equals the intrinsic trace curvature. -/
theorem curvature_eq_operatorTrace
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedFinitePartOneFormTerminalData.{u, v, w}
      actual reference)
    (parameter first second : Real) :
    data.differential.geometric.curvature parameter first second =
      ((data.differential.operator.bismutFreedTraceCurvature
        parameter first second : Real) : Complex) :=
  (data.differential.toDifferentiableOperatorGeometricBismutFreedComparisonData).curvature_eq_operatorTrace
    parameter first second

/-- Public terminal checkpoint, deliberately stopping before the local
families-index theorem. -/
theorem relative_bismut_freed_finite_part_one_form_terminal_gate
    (actual reference : Real → E →L[Real] E)
    (data : RelativeBismutFreedFinitePartOneFormTerminalData.{u, v, w}
      actual reference) :
    (∀ parameter,
      data.finitePart.zetaFamily.finitePartFamily.logDerivative parameter =
        data.finitePart.operatorTrace.trace parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient
          data.finitePart.zetaFamily.toZetaFamily parameter =
        data.differential.geometric.geometry.oneForm parameter 1) ∧
    (∀ parameter first second,
      data.differential.geometric.derivative parameter first second =
        ((data.differential.operator.bismutFreedOneFormDerivative
          parameter first second : Real) : Complex)) ∧
    (∀ parameter first second,
      data.differential.geometric.curvature parameter first second =
        ((data.differential.operator.bismutFreedTraceCurvature
          parameter first second : Real) : Complex)) :=
  ⟨data.finitePart.finitePartLogDerivative_eq_trace,
    data.connectionCoefficient_eq_geometricOneForm,
    data.derivative_agreement,
    data.curvature_eq_operatorTrace⟩

end RelativeBismutFreedFinitePartOneFormTerminalData

end
end P0EFTJanusProgramPRelativeBismutFreedFinitePartOneFormTerminal4D
end JanusFormal
