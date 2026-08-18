import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceZetaTraceCoefficient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D

/-!
# Bismut--Freed trace connection from real finite-part data

The full complex coefficient comparison follows from the real finite-part
trace identity and reality of the zeta derivative at zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeBismutFreedTraceConnectionFromFinitePart4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPReferenceZetaTraceCoefficient4D
open P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- The two real analytic conclusions needed to reconstruct the full
Bismut--Freed coefficient comparison. -/
structure RelativeBismutFreedFinitePartTraceConnectionData
    (actual reference : Real → E →L[Real] E) where
  operatorTrace :
    RelativeIntrinsicLogarithmicDerivativeTraceData.{u, v} actual reference
  zetaFamily : RelativeHeatMellinZetaFamilyData
  finitePartLogDerivative_eq_trace : ∀ parameter,
    zetaFamily.finitePartFamily.logDerivative parameter =
      operatorTrace.trace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (zetaFamily.zetaPrimeAtZero parameter).im = 0

namespace RelativeBismutFreedFinitePartTraceConnectionData

/-- Package the real finite-part inputs as a standalone reference
coefficient certificate. -/
def toReferenceZetaTraceCoefficientData
    {actual reference : Real → E →L[Real] E}
    (data :
      RelativeBismutFreedFinitePartTraceConnectionData.{u, v}
        actual reference) :
    ReferenceZetaTraceCoefficientData data.zetaFamily where
  logarithmicTrace := data.operatorTrace.trace
  finitePartLogDerivative_eq_trace :=
    data.finitePartLogDerivative_eq_trace
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The real finite-part inputs determine the full complex coefficient. -/
theorem coefficient_agreement
    {actual reference : Real → E →L[Real] E}
    (data :
      RelativeBismutFreedFinitePartTraceConnectionData.{u, v}
        actual reference)
    (parameter : Real) :
    relativeZetaConnectionCoefficient data.zetaFamily.toZetaFamily parameter =
      data.operatorTrace.bismutFreedCoefficient parameter := by
  rw [data.toReferenceZetaTraceCoefficientData.connectionCoefficient_eq_neg_trace]
  simp [toReferenceZetaTraceCoefficientData,
    RelativeIntrinsicLogarithmicDerivativeTraceData.bismutFreedCoefficient]

/-- Recover the existing intrinsic Bismut--Freed connection packet without a
separate complex coefficient hypothesis. -/
def toRelativeBismutFreedTraceConnectionData
    {actual reference : Real → E →L[Real] E}
    (data :
      RelativeBismutFreedFinitePartTraceConnectionData.{u, v}
        actual reference) :
    RelativeBismutFreedTraceConnectionData.{u, v} actual reference where
  operatorTrace := data.operatorTrace
  zetaFamily := data.zetaFamily
  coefficient_agreement := data.coefficient_agreement

/-- Public checkpoint: the two real inputs reconstruct the coefficient and
the determinant is parallel for the intrinsic connection. -/
theorem relative_bismut_freed_trace_connection_from_finite_part_gate
    (actual reference : Real → E →L[Real] E)
    (data :
      RelativeBismutFreedFinitePartTraceConnectionData.{u, v}
        actual reference) :
    (∀ parameter,
      relativeZetaConnectionCoefficient data.zetaFamily.toZetaFamily parameter =
        data.operatorTrace.bismutFreedCoefficient parameter) ∧
    (∀ parameter,
      data.toRelativeBismutFreedTraceConnectionData.connectionAt parameter
          (relativeHeatMellinZetaFamilyDeterminant data.zetaFamily parameter)
          (relativeZetaDeterminantCoordinateDerivative
            data.zetaFamily.toZetaFamily parameter) = 0) :=
  ⟨data.coefficient_agreement,
    data.toRelativeBismutFreedTraceConnectionData.determinant_parallel⟩

end RelativeBismutFreedFinitePartTraceConnectionData

end
end P0EFTJanusProgramPRelativeBismutFreedTraceConnectionFromFinitePart4D
end JanusFormal
