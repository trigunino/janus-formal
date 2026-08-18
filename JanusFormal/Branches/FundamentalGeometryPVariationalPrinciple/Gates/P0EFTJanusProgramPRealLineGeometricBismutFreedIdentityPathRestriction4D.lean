import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedRealLineUnitOneFormTerminal4D

/-!
# Identity-path restriction of the geometric BF coefficient

The older pathwise comparison uses an arbitrary base, tangent type and stored
path.  This file isolates the additional specialization needed on the real
parameter line: the path is `gamma(a) = a`, its velocity is `1`, and the
operator coefficient is the canonical scalar restriction of the intrinsic
trace one-form.  Under exactly these conditions, coefficient agreement is the
unit-direction one-form agreement required by the real-line terminal.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRealLineGeometricBismutFreedIdentityPathRestriction4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTraceOneForm4D
open P0EFTJanusProgramPDifferentiableIntrinsicTraceOneForm4D
open P0EFTJanusProgramPLinearGeometricBismutFreedOneForm4D
open P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D
open P0EFTJanusProgramPRealLineIntrinsicTraceOneFormRestriction4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeBismutFreedRealLineUnitOneFormTerminal4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- The identity path on the real parameter line with its true velocity. -/
def identityRealLinePath : DifferentiableGeometricFamilyPathData Real where
  point := fun parameter => parameter
  velocity := fun _ => 1
  hasDerivAt_point := fun parameter => hasDerivAt_id parameter

/-- On the identity path, the pulled coefficient is evaluation on the unit
tangent direction. -/
@[simp]
theorem pulledGeometricCoefficient_identityRealLinePath
    (geometry : DifferentiableLinearGeometricBismutFreedOneFormData Real)
    (parameter : Real) :
    pulledLinearGeometricCoefficient geometry.geometry identityRealLinePath
        parameter =
      geometry.geometry.oneForm parameter 1 := by
  rfl

/-- Minimal compatibility packet missing from the abstract D11 path data. -/
structure RealLineIdentityPathCoefficientRestrictionData
    (actual reference : Real → E →L[Real] E) where
  operator : DifferentiableRelativeIntrinsicTraceOneFormData.{0, u, v}
    actual reference
  geometric : DifferentiableLinearGeometricBismutFreedOneFormData Real
  coefficient_agreement : ∀ parameter,
    pulledLinearGeometricCoefficient geometric.geometry identityRealLinePath
        parameter =
      RelativeIntrinsicLogarithmicDerivativeTraceData.bismutFreedCoefficient
        (toScalarRelativeIntrinsicTrace operator.trace) parameter

namespace RealLineIdentityPathCoefficientRestrictionData

/-- The canonical scalar BF coefficient is the intrinsic one-form evaluated
on `1`. -/
theorem scalarCoefficient_eq_unitOneForm
    {actual reference : Real → E →L[Real] E}
    (data : RealLineIdentityPathCoefficientRestrictionData.{u, v}
      actual reference)
    (parameter : Real) :
    RelativeIntrinsicLogarithmicDerivativeTraceData.bismutFreedCoefficient
        (toScalarRelativeIntrinsicTrace data.operator.trace) parameter =
      ((data.operator.trace.bismutFreedRealOneForm parameter 1 : Real) :
        Complex) := by
  unfold RelativeIntrinsicLogarithmicDerivativeTraceData.bismutFreedCoefficient
  rw [toScalarRelativeIntrinsicTrace_trace_eq_directionalTrace]
  rw [data.operator.trace.bismutFreedRealOneForm_apply]
  rfl

/-- Identity-path coefficient agreement supplies the unit-direction one-form
agreement required by the real-line BF terminal. -/
theorem oneForm_agreement_unit
    {actual reference : Real → E →L[Real] E}
    (data : RealLineIdentityPathCoefficientRestrictionData.{u, v}
      actual reference)
    (parameter : Real) :
    data.geometric.geometry.oneForm parameter 1 =
      ((data.operator.trace.bismutFreedRealOneForm parameter 1 : Real) :
        Complex) := by
  calc
    data.geometric.geometry.oneForm parameter 1 =
        pulledLinearGeometricCoefficient data.geometric.geometry
          identityRealLinePath parameter := by rfl
    _ = RelativeIntrinsicLogarithmicDerivativeTraceData.bismutFreedCoefficient
          (toScalarRelativeIntrinsicTrace data.operator.trace) parameter :=
      data.coefficient_agreement parameter
    _ = ((data.operator.trace.bismutFreedRealOneForm parameter 1 : Real) :
          Complex) := data.scalarCoefficient_eq_unitOneForm parameter

/-- Fill the existing real-line terminal once its independent zeta inputs are
available. -/
def toRealLineUnitOneFormTerminal
    {actual reference : Real → E →L[Real] E}
    (data : RealLineIdentityPathCoefficientRestrictionData.{u, v}
      actual reference)
    (zetaFamily : RelativeHeatMellinZetaFamilyData)
    (finitePartLogDerivative_eq_trace : ∀ parameter,
      zetaFamily.finitePartFamily.logDerivative parameter =
        RelativeIntrinsicLogarithmicDerivativeTraceData.trace
          (toScalarRelativeIntrinsicTrace data.operator.trace) parameter)
    (zetaPrimeAtZero_real : ∀ parameter,
      (zetaFamily.zetaPrimeAtZero parameter).im = 0) :
    RelativeBismutFreedRealLineUnitOneFormTerminalData.{u, v}
      actual reference where
  operator := data.operator
  geometric := data.geometric
  oneForm_agreement_unit := data.oneForm_agreement_unit
  zetaFamily := zetaFamily
  finitePartLogDerivative_eq_trace := finitePartLogDerivative_eq_trace
  zetaPrimeAtZero_real := zetaPrimeAtZero_real

/-- Public identity-path restriction checkpoint. -/
theorem real_line_geometric_bismut_freed_identity_path_restriction_gate
    (actual reference : Real → E →L[Real] E)
    (data : RealLineIdentityPathCoefficientRestrictionData.{u, v}
      actual reference) :
    (∀ parameter,
      pulledLinearGeometricCoefficient data.geometric.geometry
          identityRealLinePath parameter =
        RelativeIntrinsicLogarithmicDerivativeTraceData.bismutFreedCoefficient
          (toScalarRelativeIntrinsicTrace data.operator.trace) parameter) ∧
    (∀ parameter,
      data.geometric.geometry.oneForm parameter 1 =
        ((data.operator.trace.bismutFreedRealOneForm parameter 1 : Real) :
          Complex)) :=
  ⟨data.coefficient_agreement, data.oneForm_agreement_unit⟩

end RealLineIdentityPathCoefficientRestrictionData

end
end P0EFTJanusProgramPRealLineGeometricBismutFreedIdentityPathRestriction4D
end JanusFormal
