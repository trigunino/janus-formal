import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

/-!
# Bismut--Freed connection from intrinsic logarithmic traces

The zeta family already supplies a scalar connection coefficient
`d/da zeta'_a(0)`.  The operator-theoretic family-index statement is the
identification of that coefficient with the intrinsic relative logarithmic
trace

`-Tr(G_a H'_a - G^ref_a (H^ref_a)')`.

This file makes that identification the only bridge.  Once it is available,
the zeta determinant is parallel for the operator-defined Bismut--Freed
connection and the finite-part metric variation is expressed directly by the
relative logarithmic trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- One differentiable actual/reference reduced pair and one Mellin/zeta family
whose connection coefficient is the intrinsic operator trace. -/
structure RelativeBismutFreedTraceConnectionData
    (actual reference : Real → E →L[Real] E) where
  operatorTrace :
    RelativeIntrinsicLogarithmicDerivativeTraceData actual reference
  zetaFamily : RelativeHeatMellinZetaFamilyData
  coefficient_agreement : ∀ parameter,
    relativeZetaConnectionCoefficient zetaFamily.toZetaFamily parameter =
      operatorTrace.bismutFreedCoefficient parameter

namespace RelativeBismutFreedTraceConnectionData

/-- Operator-defined Bismut--Freed connection on a scalar first jet. -/
def connectionAt
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedTraceConnectionData actual reference)
    (parameter : Real) (value derivative : Complex) : Complex :=
  derivative + data.operatorTrace.bismutFreedCoefficient parameter * value

/-- The operator trace connection and the zeta connection coincide. -/
theorem connectionAt_eq_zeta
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedTraceConnectionData actual reference)
    (parameter : Real) (value derivative : Complex) :
    data.connectionAt parameter value derivative =
      relativeZetaConnectionAt data.zetaFamily.toZetaFamily parameter value
        derivative := by
  unfold connectionAt relativeZetaConnectionAt
  rw [data.coefficient_agreement parameter]

/-- The relative zeta determinant is parallel for the intrinsic
Bismut--Freed trace connection. -/
theorem determinant_parallel
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedTraceConnectionData actual reference)
    (parameter : Real) :
    data.connectionAt parameter
        (relativeHeatMellinZetaFamilyDeterminant data.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          data.zetaFamily.toZetaFamily parameter) = 0 := by
  rw [data.connectionAt_eq_zeta]
  exact relativeZetaDeterminantCoordinate_parallel
    data.zetaFamily.toZetaFamily parameter

/-- The finite-part logarithmic derivative equals the intrinsic relative
logarithmic trace. -/
theorem finitePart_logDerivative_eq_trace
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedTraceConnectionData actual reference)
    (parameter : Real) :
    data.zetaFamily.finitePartFamily.logDerivative parameter =
      data.operatorTrace.trace parameter := by
  calc
    data.zetaFamily.finitePartFamily.logDerivative parameter =
        -(data.zetaFamily.parameterDerivative parameter).re :=
      data.zetaFamily.connection_realPart parameter
    _ = -(data.operatorTrace.bismutFreedCoefficient parameter).re := by
      rw [data.coefficient_agreement parameter]
      rfl
    _ = data.operatorTrace.trace parameter := by
      rw [data.operatorTrace.bismutFreedCoefficient_re]
      ring

/-- The positive determinant magnitude varies by the relative logarithmic
trace. -/
theorem finitePartDeterminant_hasDerivAt
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedTraceConnectionData actual reference)
    (parameter : Real) :
    HasDerivAt
      (relativeHeatFinitePartDeterminantFamily
        data.zetaFamily.finitePartFamily)
      (data.operatorTrace.trace parameter *
        relativeHeatFinitePartDeterminantFamily
          data.zetaFamily.finitePartFamily parameter)
      parameter := by
  have hDerivative :=
    relativeHeatFinitePartDeterminantFamily_hasDerivAt
      data.zetaFamily.finitePartFamily parameter
  simpa [relativeHeatFinitePartDeterminantFamilyDerivative,
    data.finitePart_logDerivative_eq_trace parameter] using hDerivative

/-- Quillen metric variation expressed entirely by the intrinsic relative
logarithmic trace. -/
theorem metricWeightDerivative_eq_trace
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedTraceConnectionData actual reference)
    (parameter : Real) :
    relativeHeatFinitePartMetricWeightDerivative
        data.zetaFamily.finitePartFamily parameter =
      2 * data.operatorTrace.trace parameter *
        relativeHeatFinitePartMetricWeight
          data.zetaFamily.finitePartFamily parameter := by
  unfold relativeHeatFinitePartMetricWeightDerivative
  rw [data.finitePart_logDerivative_eq_trace parameter]

/-- The spectral-asymmetry phase remains unitary. -/
theorem phase_norm_one
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedTraceConnectionData actual reference)
    (parameter : Real) :
    ‖relativeZetaFinitePartPhase
      data.zetaFamily.toFinitePartComparison parameter‖ = 1 :=
  relativeHeatMellinZetaFamily_phase_norm_one data.zetaFamily parameter

/-- Public intrinsic Bismut--Freed connection checkpoint. -/
theorem relative_bismut_freed_trace_connection_gate
    (actual reference : Real → E →L[Real] E)
    (data : RelativeBismutFreedTraceConnectionData actual reference) :
    (∀ parameter,
      relativeZetaConnectionCoefficient data.zetaFamily.toZetaFamily parameter =
        data.operatorTrace.bismutFreedCoefficient parameter) ∧
      (∀ parameter,
        data.connectionAt parameter
            (relativeHeatMellinZetaFamilyDeterminant data.zetaFamily parameter)
            (relativeZetaDeterminantCoordinateDerivative
              data.zetaFamily.toZetaFamily parameter) = 0) ∧
      (∀ parameter,
        data.zetaFamily.finitePartFamily.logDerivative parameter =
          data.operatorTrace.trace parameter) ∧
      (∀ parameter,
        relativeHeatFinitePartMetricWeightDerivative
            data.zetaFamily.finitePartFamily parameter =
          2 * data.operatorTrace.trace parameter *
            relativeHeatFinitePartMetricWeight
              data.zetaFamily.finitePartFamily parameter) ∧
      (∀ parameter,
        ‖relativeZetaFinitePartPhase
          data.zetaFamily.toFinitePartComparison parameter‖ = 1) :=
  ⟨data.coefficient_agreement,
    data.determinant_parallel,
    data.finitePart_logDerivative_eq_trace,
    data.metricWeightDerivative_eq_trace,
    data.phase_norm_one⟩

end RelativeBismutFreedTraceConnectionData

end
end P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D
end JanusFormal
