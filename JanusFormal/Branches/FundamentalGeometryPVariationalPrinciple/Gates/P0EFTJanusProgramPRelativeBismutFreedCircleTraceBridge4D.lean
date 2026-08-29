import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaCircleConnectionBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaCircleHolonomyPhase4D

/-!
# Circle Quillen connection from intrinsic Bismut--Freed traces

The earlier circle bridge compared two scalar connection coefficients.  This
file strengthens it by requiring the circle coefficient to be the intrinsic
actual-minus-reference logarithmic trace of a differentiable reduced operator
family.

Thus the chain is now

`H_a, H^ref_a -> Tr(G H' - G_ref H'_ref) -> zeta connection -> circle connection`.

The endpoint clutching condition is retained unchanged.  All parallelism,
metric compatibility and phase-holonomy consequences of the existing circle
bridge are then recovered without a second scalar connection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeBismutFreedCircleTraceBridge4D

set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option synthInstance.maxHeartbeats 2300000

noncomputable section

open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDeterminantTopologicalBundle
open P0EFTJanusProgramPRelativeBismutFreedTraceConnection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaCircleConnectionBridge4D
open P0EFTJanusProgramPRelativeZetaCircleHolonomyPhase4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Intrinsic operator trace identified with the explicit circle Quillen
connection coefficient. -/
structure RelativeBismutFreedCircleTraceBridgeData
    (actual reference : Real → E →L[Real] E)
    (fold : Fold) where
  bismutFreed :
    RelativeBismutFreedTraceConnectionData.{u, v} actual reference
  coefficient_eq_circle : ∀ parameter,
    bismutFreed.operatorTrace.bismutFreedCoefficient parameter =
      (circleQuillenConnectionCoefficient fold : Complex)
  endpoint_clutching :
    circleLargeGaugeFrameCoordinateTransition fold
        (relativeHeatMellinZetaFamilyDeterminant bismutFreed.zetaFamily 1) =
      relativeHeatMellinZetaFamilyDeterminant bismutFreed.zetaFamily 0

namespace RelativeBismutFreedCircleTraceBridgeData

/-- Forget only the operator-trace origin and recover the established scalar
zeta/circle bridge. -/
def toZetaCircleBridge
    {actual reference : Real → E →L[Real] E}
    {fold : Fold}
    (data : RelativeBismutFreedCircleTraceBridgeData.{u, v}
      actual reference fold) :
    RelativeZetaCircleConnectionBridgeData fold
      data.bismutFreed.zetaFamily.toZetaFamily where
  coefficient_agreement := by
    intro parameter
    calc
      relativeZetaConnectionCoefficient
          data.bismutFreed.zetaFamily.toZetaFamily parameter =
        data.bismutFreed.operatorTrace.bismutFreedCoefficient parameter :=
      data.bismutFreed.coefficient_agreement parameter
      _ = (circleQuillenConnectionCoefficient fold : Complex) :=
        data.coefficient_eq_circle parameter
  endpoint_clutching := data.endpoint_clutching

/-- The intrinsic relative logarithmic trace is the negative of the explicit
circle connection coefficient. -/
theorem relativeTrace_eq_neg_circleCoefficient
    {actual reference : Real → E →L[Real] E}
    {fold : Fold}
    (data : RelativeBismutFreedCircleTraceBridgeData.{u, v}
      actual reference fold)
    (parameter : Real) :
    data.bismutFreed.operatorTrace.trace parameter =
      -circleQuillenConnectionCoefficient fold := by
  have hReal := congrArg Complex.re (data.coefficient_eq_circle parameter)
  rw [data.bismutFreed.operatorTrace.bismutFreedCoefficient_re] at hReal
  norm_num at hReal ⊢
  linarith

/-- The finite-part logarithmic derivative has the same explicit circle
spelling. -/
theorem finitePart_logDerivative_eq_neg_circleCoefficient
    {actual reference : Real → E →L[Real] E}
    {fold : Fold}
    (data : RelativeBismutFreedCircleTraceBridgeData.{u, v}
      actual reference fold)
    (parameter : Real) :
    data.bismutFreed.zetaFamily.finitePartFamily.logDerivative parameter =
      -circleQuillenConnectionCoefficient fold := by
  rw [data.bismutFreed.finitePart_logDerivative_eq_trace parameter]
  exact data.relativeTrace_eq_neg_circleCoefficient parameter

/-- The zeta determinant is parallel for the explicit circle connection. -/
theorem circle_parallel
    {actual reference : Real → E →L[Real] E}
    {fold : Fold}
    (data : RelativeBismutFreedCircleTraceBridgeData.{u, v}
      actual reference fold)
    (parameter : Real) :
    circleQuillenConnectionAt fold
        (relativeHeatMellinZetaFamilyDeterminant
          data.bismutFreed.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          data.bismutFreed.zetaFamily.toZetaFamily parameter) = 0 :=
  data.toZetaCircleBridge.circle_parallel parameter

/-- Metric compatibility of the parallel determinant section. -/
theorem circle_metricFirstVariation_zero
    {actual reference : Real → E →L[Real] E}
    {fold : Fold}
    (data : RelativeBismutFreedCircleTraceBridgeData.{u, v}
      actual reference fold)
    (parameter : Real) :
    circleQuillenCoordinateMetricFirstVariation fold parameter
        (relativeHeatMellinZetaFamilyDeterminant
          data.bismutFreed.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          data.bismutFreed.zetaFamily.toZetaFamily parameter)
        (relativeHeatMellinZetaFamilyDeterminant
          data.bismutFreed.zetaFamily parameter)
        (relativeZetaDeterminantCoordinateDerivative
          data.bismutFreed.zetaFamily.toZetaFamily parameter) = 0 :=
  data.toZetaCircleBridge.metricFirstVariation_zero parameter

/-- Closed-loop phase holonomy in operator-trace form. -/
theorem closedHolonomy_eq_phase_ratio
    {actual reference : Real → E →L[Real] E}
    {fold : Fold}
    (data : RelativeBismutFreedCircleTraceBridgeData.{u, v}
      actual reference fold) :
    circleQuillenClosedHolonomy fold =
      relativeZetaFinitePartPhase
          data.bismutFreed.zetaFamily.toFinitePartComparison 0 /
        relativeZetaFinitePartPhase
          data.bismutFreed.zetaFamily.toFinitePartComparison 1 :=
  circleQuillenClosedHolonomy_eq_zetaPhase_ratio fold
    data.bismutFreed.zetaFamily data.toZetaCircleBridge

/-- Public operator-trace/circle checkpoint. -/
theorem relative_bismut_freed_circle_trace_bridge_gate
    (actual reference : Real → E →L[Real] E)
    (fold : Fold)
    (data : RelativeBismutFreedCircleTraceBridgeData.{u, v}
      actual reference fold) :
    (∀ parameter,
      data.bismutFreed.operatorTrace.trace parameter =
        -circleQuillenConnectionCoefficient fold) ∧
      (∀ parameter,
        circleQuillenConnectionAt fold
            (relativeHeatMellinZetaFamilyDeterminant
              data.bismutFreed.zetaFamily parameter)
            (relativeZetaDeterminantCoordinateDerivative
              data.bismutFreed.zetaFamily.toZetaFamily parameter) = 0) ∧
      circleLargeGaugeFrameCoordinateTransition fold
          (relativeHeatMellinZetaFamilyDeterminant
            data.bismutFreed.zetaFamily 1) =
        relativeHeatMellinZetaFamilyDeterminant
          data.bismutFreed.zetaFamily 0 ∧
      circleQuillenClosedHolonomy fold =
        relativeZetaFinitePartPhase
            data.bismutFreed.zetaFamily.toFinitePartComparison 0 /
          relativeZetaFinitePartPhase
            data.bismutFreed.zetaFamily.toFinitePartComparison 1 :=
  ⟨data.relativeTrace_eq_neg_circleCoefficient,
    data.circle_parallel,
    data.endpoint_clutching,
    data.closedHolonomy_eq_phase_ratio⟩

end RelativeBismutFreedCircleTraceBridgeData

end
end P0EFTJanusProgramPRelativeBismutFreedCircleTraceBridge4D
end JanusFormal
