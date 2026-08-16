import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleQuillenMetricFlatConnection

/-!
# Bridge from the zeta variation to the circle Quillen connection

The local zeta connection agrees with the explicit circle Quillen connection
when their scalar one-forms agree.  Under that identification the zeta
determinant is parallel, its Hermitian metric has zero first variation, and an
explicit endpoint condition makes it a section of the clutched circle line.

The difficult global family-index statement is now precisely the construction
of this coefficient and endpoint agreement from the Janus Hessian family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeZetaCircleConnectionBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-- Exact family-level bridge data. -/
structure RelativeZetaCircleConnectionBridgeData
    (fold : Fold)
    (family : RelativeZetaDeterminantFamilyData) : Prop where
  coefficient_agreement : ∀ parameter,
    relativeZetaConnectionCoefficient family parameter =
      (circleQuillenConnectionCoefficient fold : Complex)
  endpoint_clutching :
    circleLargeGaugeFrameCoordinateTransition fold
        (relativeZetaDeterminantCoordinate family 1) =
      relativeZetaDeterminantCoordinate family 0

/-- The two covariant-derivative formulas are identical. -/
theorem RelativeZetaCircleConnectionBridgeData.connectionAt_eq
    {fold : Fold}
    {family : RelativeZetaDeterminantFamilyData}
    (bridge : RelativeZetaCircleConnectionBridgeData fold family)
    (parameter : Real) (value derivative : Complex) :
    relativeZetaConnectionAt family parameter value derivative =
      circleQuillenConnectionAt fold value derivative := by
  unfold relativeZetaConnectionAt circleQuillenConnectionAt
  rw [bridge.coefficient_agreement parameter]

/-- The zeta determinant is parallel for the circle Quillen connection. -/
theorem RelativeZetaCircleConnectionBridgeData.circle_parallel
    {fold : Fold}
    {family : RelativeZetaDeterminantFamilyData}
    (bridge : RelativeZetaCircleConnectionBridgeData fold family)
    (parameter : Real) :
    circleQuillenConnectionAt fold
        (relativeZetaDeterminantCoordinate family parameter)
        (relativeZetaDeterminantCoordinateDerivative family parameter) = 0 := by
  rw [← bridge.connectionAt_eq]
  exact relativeZetaDeterminantCoordinate_parallel family parameter

/-- Metric compatibility makes the first variation of the squared norm vanish
along the bridged zeta section. -/
theorem RelativeZetaCircleConnectionBridgeData.metricFirstVariation_zero
    {fold : Fold}
    {family : RelativeZetaDeterminantFamilyData}
    (bridge : RelativeZetaCircleConnectionBridgeData fold family)
    (parameter : Real) :
    circleQuillenCoordinateMetricFirstVariation fold parameter
        (relativeZetaDeterminantCoordinate family parameter)
        (relativeZetaDeterminantCoordinateDerivative family parameter)
        (relativeZetaDeterminantCoordinate family parameter)
        (relativeZetaDeterminantCoordinateDerivative family parameter) = 0 := by
  rw [circleQuillenConnection_metric_compatible]
  rw [bridge.circle_parallel parameter, bridge.circle_parallel parameter]
  simp [circleQuillenCoordinateMetric]

/-- Public family-level circle-connection checkpoint. -/
theorem relative_zeta_circle_connection_bridge_gate
    (fold : Fold)
    (family : RelativeZetaDeterminantFamilyData)
    (bridge : RelativeZetaCircleConnectionBridgeData fold family) :
    (∀ parameter,
      circleQuillenConnectionAt fold
          (relativeZetaDeterminantCoordinate family parameter)
          (relativeZetaDeterminantCoordinateDerivative family parameter) = 0) ∧
      (∀ parameter,
        circleQuillenCoordinateMetricFirstVariation fold parameter
            (relativeZetaDeterminantCoordinate family parameter)
            (relativeZetaDeterminantCoordinateDerivative family parameter)
            (relativeZetaDeterminantCoordinate family parameter)
            (relativeZetaDeterminantCoordinateDerivative family parameter) =
          0) ∧
      circleLargeGaugeFrameCoordinateTransition fold
          (relativeZetaDeterminantCoordinate family 1) =
        relativeZetaDeterminantCoordinate family 0 :=
  ⟨bridge.circle_parallel, bridge.metricFirstVariation_zero,
    bridge.endpoint_clutching⟩

end
end P0EFTJanusProgramPRelativeZetaCircleConnectionBridge4D
end JanusFormal
