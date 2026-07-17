import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusScalarStressCovariantJetConservation4D

/-!
# Scalar stress conservation in a coordinate connection jet

This gate transports the normal-frame second-jet identity to arbitrary local
coordinates.  The pointwise connection interface contains a symmetric
nondegenerate metric and inverse, their coordinate derivatives, Christoffel
coefficients, metric compatibility and vanishing torsion.  The covariant
Hessian is constructed from the raw scalar second jet and proved symmetric.

A coordinate realization records the tensor law
`nabla T = partial T + Gamma*T + Gamma*T`.  Its exact transport to the normal
jet exposes cancellation of all Christoffel corrections and yields
`nabla_mu T^{mu nu} = Euler * sharp(d phi)`.  This remains pointwise jet
algebra: no smooth global connection or global divergence theorem is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusScalarStressCoordinateConnectionJet4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressCovariantJetConservation4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

/-- Metric-compatible torsion-free connection data at one coordinate point.
Both covariant and inverse-metric compatibility equations are retained so an
actual coordinate derivative realization can be checked without hidden
geometric assumptions. -/
structure MetricCompatibleTorsionFreeConnectionJet4 where
  metric : FixedSignMetric4
  christoffel : Index4 → Index4 → Index4 → Real
  metricDerivative : Index4 → Index4 → Index4 → Real
  inverseMetricDerivative : Index4 → Index4 → Index4 → Real
  metricDerivative_symmetric : ∀ derivative first second,
    metricDerivative derivative first second =
      metricDerivative derivative second first
  torsionFree : ∀ upper first second,
    christoffel upper first second = christoffel upper second first
  metricCompatible : ∀ derivative first second,
    metricDerivative derivative first second =
      (∑ upper : Index4,
        christoffel upper derivative first * metric.metric upper second) +
      ∑ upper : Index4,
        christoffel upper derivative second * metric.metric first upper
  inverseMetricCompatible : ∀ derivative first second,
    inverseMetricDerivative derivative first second +
        (∑ lower : Index4,
          christoffel first derivative lower * metric.metric⁻¹ lower second) +
      (∑ lower : Index4,
        christoffel second derivative lower * metric.metric⁻¹ first lower) = 0

/-- Coordinate scalar second jet before subtracting Christoffel terms. -/
structure CoordinateScalarJet2 where
  field : Real
  gradient : Vector4
  partialGradient : Matrix4
  partialGradient_symmetric : partialGradient.transpose = partialGradient

/-- Covariant Hessian `partial_mu p_nu - Gamma^rho_{mu nu} p_rho`. -/
def coordinateCovariantHessian
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (jet : CoordinateScalarJet2) : Matrix4 :=
  fun first second =>
    jet.partialGradient first second -
      ∑ upper : Index4,
        connection.christoffel upper first second * jet.gradient upper

/-- Torsion freedom converts symmetry of raw scalar partial derivatives into
symmetry of the covariant Hessian. -/
theorem coordinateCovariantHessian_symmetric
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (jet : CoordinateScalarJet2) :
    (coordinateCovariantHessian connection jet).transpose =
      coordinateCovariantHessian connection jet := by
  ext first second
  have hPartial := congrArg
    (fun matrix : Matrix4 => matrix first second)
    jet.partialGradient_symmetric
  simp only [Matrix.transpose_apply] at hPartial ⊢
  unfold coordinateCovariantHessian
  rw [hPartial]
  apply congrArg (jet.partialGradient first second - ·)
  apply Finset.sum_congr rfl
  intro upper _
  rw [connection.torsionFree upper second first]

/-- Tensorial normal representative of the coordinate scalar jet. -/
def coordinateScalarJetNormalForm
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (jet : CoordinateScalarJet2) : CovariantScalarJet2 where
  field := jet.field
  gradient := jet.gradient
  hessian := coordinateCovariantHessian connection jet
  hessian_symmetric := coordinateCovariantHessian_symmetric connection jet

/-- Coordinate stress formed from the tensorial scalar jet. -/
def coordinateCovariantScalarStress
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (potentialValue : Real) (jet : CoordinateScalarJet2) : Matrix4 :=
  covariantScalarJetStress connection.metric potentialValue
    (coordinateScalarJetNormalForm connection jet)

/-- The two Christoffel corrections in the covariant derivative of a
contravariant rank-two tensor. -/
def coordinateStressChristoffelCorrection
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (potentialValue : Real) (jet : CoordinateScalarJet2)
    (derivative first second : Index4) : Real :=
  (∑ lower : Index4,
      connection.christoffel first derivative lower *
        coordinateCovariantScalarStress connection potentialValue jet
          lower second) +
    ∑ lower : Index4,
      connection.christoffel second derivative lower *
        coordinateCovariantScalarStress connection potentialValue jet
          first lower

/-- Typed realization of the coordinate tensor law.  For an actual local
field this law is proved from metric compatibility and the Leibniz rule; here
it is isolated as the exact pointwise interface, rather than postulated as a
global smooth connection theorem. -/
structure CoordinateStressDerivativeRealization
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (potentialValue potentialSlope : Real)
    (jet : CoordinateScalarJet2) where
  partialStressDerivative : Index4 → Index4 → Index4 → Real
  partial_add_christoffel : ∀ derivative first second,
    partialStressDerivative derivative first second +
        coordinateStressChristoffelCorrection connection potentialValue jet
          derivative first second =
      covariantScalarJetStressDerivative connection.metric potentialSlope
        (coordinateScalarJetNormalForm connection jet)
        derivative first second

/-- Reconstructed coordinate partial derivative obtained by subtracting the
two Christoffel terms from the tensorial normal representative. -/
def canonicalCoordinateStressDerivativeRealization
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (potentialValue potentialSlope : Real)
    (jet : CoordinateScalarJet2) :
    CoordinateStressDerivativeRealization connection
      potentialValue potentialSlope jet where
  partialStressDerivative := fun derivative first second =>
    covariantScalarJetStressDerivative connection.metric potentialSlope
        (coordinateScalarJetNormalForm connection jet)
        derivative first second -
      coordinateStressChristoffelCorrection connection potentialValue jet
        derivative first second
  partial_add_christoffel := by
    intro derivative first second
    ring

/-- Arbitrary-coordinate covariant derivative
`partial T + Gamma*T + Gamma*T`. -/
def coordinateCovariantStressDerivative
    {connection : MetricCompatibleTorsionFreeConnectionJet4}
    {potentialValue potentialSlope : Real}
    {jet : CoordinateScalarJet2}
    (realization : CoordinateStressDerivativeRealization connection
      potentialValue potentialSlope jet)
    (derivative first second : Index4) : Real :=
  realization.partialStressDerivative derivative first second +
    coordinateStressChristoffelCorrection connection potentialValue jet
      derivative first second

/-- Exact cancellation/transport of all explicit Christoffel corrections. -/
theorem coordinateCovariantStressDerivative_transport_normal
    {connection : MetricCompatibleTorsionFreeConnectionJet4}
    {potentialValue potentialSlope : Real}
    {jet : CoordinateScalarJet2}
    (realization : CoordinateStressDerivativeRealization connection
      potentialValue potentialSlope jet)
    (derivative first second : Index4) :
    coordinateCovariantStressDerivative realization derivative first second =
      covariantScalarJetStressDerivative connection.metric potentialSlope
        (coordinateScalarJetNormalForm connection jet)
        derivative first second :=
  realization.partial_add_christoffel derivative first second

/-- Coordinate covariant divergence `nabla_mu T^{mu nu}`. -/
def coordinateCovariantStressDivergence
    {connection : MetricCompatibleTorsionFreeConnectionJet4}
    {potentialValue potentialSlope : Real}
    {jet : CoordinateScalarJet2}
    (realization : CoordinateStressDerivativeRealization connection
      potentialValue potentialSlope jet)
    (index : Index4) : Real :=
  ∑ derivative : Index4,
    coordinateCovariantStressDerivative realization derivative derivative index

theorem coordinateCovariantStressDivergence_transport_normal
    {connection : MetricCompatibleTorsionFreeConnectionJet4}
    {potentialValue potentialSlope : Real}
    {jet : CoordinateScalarJet2}
    (realization : CoordinateStressDerivativeRealization connection
      potentialValue potentialSlope jet)
    (index : Index4) :
    coordinateCovariantStressDivergence realization index =
      covariantScalarJetStressDivergence connection.metric potentialSlope
        (coordinateScalarJetNormalForm connection jet) index := by
  unfold coordinateCovariantStressDivergence
    covariantScalarJetStressDivergence
  apply Finset.sum_congr rfl
  intro derivative _
  exact coordinateCovariantStressDerivative_transport_normal
    realization derivative derivative index

/-- Arbitrary-coordinate stress identity transported from the tensorial
normal representative. -/
theorem coordinateCovariantStressDivergence_eq_euler_mul_raisedGradient
    {connection : MetricCompatibleTorsionFreeConnectionJet4}
    {potentialValue potentialSlope : Real}
    {jet : CoordinateScalarJet2}
    (realization : CoordinateStressDerivativeRealization connection
      potentialValue potentialSlope jet)
    (index : Index4) :
    coordinateCovariantStressDivergence realization index =
      covariantScalarStressEulerResidual connection.metric potentialSlope
          (coordinateScalarJetNormalForm connection jet) *
        covariantScalarJetRaisedGradient connection.metric
          (coordinateScalarJetNormalForm connection jet) index := by
  rw [coordinateCovariantStressDivergence_transport_normal]
  exact covariantScalarJetStressDivergence_eq_euler_mul_raisedGradient
    connection.metric potentialSlope
      (coordinateScalarJetNormalForm connection jet) index

/-- Coordinate stress conservation under the covariant scalar Euler
equation at the same point. -/
theorem coordinateCovariantStressDivergence_eq_zero_of_euler
    {connection : MetricCompatibleTorsionFreeConnectionJet4}
    {potentialValue potentialSlope : Real}
    {jet : CoordinateScalarJet2}
    (realization : CoordinateStressDerivativeRealization connection
      potentialValue potentialSlope jet)
    (hEuler : covariantScalarStressEulerResidual connection.metric
      potentialSlope (coordinateScalarJetNormalForm connection jet) = 0) :
    coordinateCovariantStressDivergence realization = 0 := by
  funext index
  rw [coordinateCovariantStressDivergence_eq_euler_mul_raisedGradient,
    hEuler]
  simp

end

end P0EFTJanusScalarStressCoordinateConnectionJet4D
end JanusFormal
