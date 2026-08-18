import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedRealLineRestrictionTerminal4D

/-!
# Relative BF terminal from the unit-direction geometric comparison

On the real parameter line, two real-linear covectors agree everywhere once
they agree on `1`.  This frontend reduces the remaining geometric BF input to
that single comparison at each parameter and then reuses the real-line trace
restriction terminal.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeBismutFreedRealLineUnitOneFormTerminal4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D
open P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D
open P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparisonFromOneForm4D
open P0EFTJanusProgramPRealLineIntrinsicTraceOneFormRestriction4D
open P0EFTJanusProgramPRelativeBismutFreedRealLineRestrictionTerminal4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Minimal real-line geometric terminal input.  The comparison of covectors
is supplied only on the basis direction `1`. -/
structure RelativeBismutFreedRealLineUnitOneFormTerminalData
    (actual reference : Real → E →L[Real] E) where
  operator : DifferentiableRelativeIntrinsicTraceOneFormData.{0, u, v}
    actual reference
  geometric : DifferentiableLinearGeometricBismutFreedOneFormData Real
  oneForm_agreement_unit : ∀ parameter,
    geometric.geometry.oneForm parameter 1 =
      ((operator.trace.bismutFreedRealOneForm parameter 1 : Real) : Complex)
  zetaFamily : RelativeHeatMellinZetaFamilyData
  finitePartLogDerivative_eq_trace : ∀ parameter,
    zetaFamily.finitePartFamily.logDerivative parameter =
      (toScalarRelativeIntrinsicTrace operator.trace).trace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (zetaFamily.zetaPrimeAtZero parameter).im = 0

namespace RelativeBismutFreedRealLineUnitOneFormTerminalData

/-- Agreement on `1` extends to every real tangent direction by linearity. -/
theorem oneForm_agreement
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedRealLineUnitOneFormTerminalData.{u, v}
      actual reference)
    (parameter direction : Real) :
    data.geometric.geometry.oneForm parameter direction =
      ((data.operator.trace.bismutFreedRealOneForm
        parameter direction : Real) : Complex) := by
  calc
    data.geometric.geometry.oneForm parameter direction =
        direction • data.geometric.geometry.oneForm parameter 1 := by
      rw [← map_smul]
      simp
    _ = direction •
        ((data.operator.trace.bismutFreedRealOneForm
          parameter 1 : Real) : Complex) := by
      rw [data.oneForm_agreement_unit parameter]
    _ = ((direction •
        data.operator.trace.bismutFreedRealOneForm parameter 1 : Real) :
          Complex) := by
      simp [Complex.real_smul]
    _ = ((data.operator.trace.bismutFreedRealOneForm
        parameter direction : Real) : Complex) := by
      rw [← map_smul]
      simp

/-- Full differentiable one-form comparison reconstructed from the unit
direction. -/
def toDifferentiableFromOneForm
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedRealLineUnitOneFormTerminalData.{u, v}
      actual reference) :
    DifferentiableOperatorGeometricBismutFreedFromOneFormData.{0, u, v}
      actual reference where
  operator := data.operator
  geometric := data.geometric
  oneForm_agreement := data.oneForm_agreement

/-- Canonical real-line terminal with both scalar and all-direction
compatibilities proved. -/
def toRealLineRestrictionTerminal
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedRealLineUnitOneFormTerminalData.{u, v}
      actual reference) :
    RelativeBismutFreedRealLineRestrictionTerminalData.{u, v}
      actual reference where
  differential := data.toDifferentiableFromOneForm
  zetaFamily := data.zetaFamily
  finitePartLogDerivative_eq_trace := data.finitePartLogDerivative_eq_trace
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- Public minimal real-line BF checkpoint.  No families-index comparison is
part of this statement. -/
theorem relative_bismut_freed_real_line_unit_one_form_terminal_gate
    (actual reference : Real → E →L[Real] E)
    (data : RelativeBismutFreedRealLineUnitOneFormTerminalData.{u, v}
      actual reference) :
    (∀ parameter direction,
      data.geometric.geometry.oneForm parameter direction =
        ((data.operator.trace.bismutFreedRealOneForm
          parameter direction : Real) : Complex)) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient data.zetaFamily.toZetaFamily parameter =
        data.geometric.geometry.oneForm parameter 1) ∧
    (∀ parameter first second,
      data.geometric.derivative parameter first second =
        ((data.operator.bismutFreedOneFormDerivative
          parameter first second : Real) : Complex)) ∧
    (∀ parameter first second,
      data.geometric.curvature parameter first second =
        ((data.operator.bismutFreedTraceCurvature
          parameter first second : Real) : Complex)) :=
  ⟨data.oneForm_agreement,
    data.toRealLineRestrictionTerminal.connectionCoefficient_eq_geometricOneForm,
    (data.toRealLineRestrictionTerminal.toFinitePartOneFormTerminal).derivative_agreement,
    (data.toRealLineRestrictionTerminal.toFinitePartOneFormTerminal).curvature_eq_operatorTrace⟩

end RelativeBismutFreedRealLineUnitOneFormTerminalData

end
end P0EFTJanusProgramPRelativeBismutFreedRealLineUnitOneFormTerminal4D
end JanusFormal
