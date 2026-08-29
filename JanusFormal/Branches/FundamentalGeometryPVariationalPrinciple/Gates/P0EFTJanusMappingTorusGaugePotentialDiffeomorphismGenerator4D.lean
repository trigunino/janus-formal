import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMetricMatterGaugeNoetherOperator4D

/-!
# Infinitesimal diffeomorphism action on intrinsic Maxwell one-forms

The metric two-tensor analogue already exists through
`covariantTensorDiffeomorphismGeneratorAt`,
`SmoothMetricPairPullbackFlow`, and `MetricPairFlowToGhostContract`.
This gate supplies the missing one-form layer with the same scope: a genuine
pointwise derivative, a smooth global realization, and an explicit
flow-to-ghost linearity contract.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGaugePotentialDiffeomorphismGenerator4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusMetricMatterGaugeNoetherOperator4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev GaugeCovectorFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point →L[Real] Real

private instance gaugeCovectorFiberNormedAddCommGroup
    (point : EffectiveQuotient period hPeriod) :
    NormedAddCommGroup (GaugeCovectorFiber period hPeriod point) :=
  inferInstanceAs (NormedAddCommGroup
    (CoverCoordinates →L[Real] Real))

private instance gaugeCovectorFiberNormedSpace
    (point : EffectiveQuotient period hPeriod) :
    NormedSpace Real (GaugeCovectorFiber period hPeriod point) :=
  inferInstanceAs (NormedSpace Real
    (CoverCoordinates →L[Real] Real))

/-- Pullback orbit of one gauge component at one quotient point. -/
def gaugePotentialPullbackCurveValue
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    Real → GaugeCovectorFiber period hPeriod point :=
  fun parameter =>
    (pullbackGaugePotential period hPeriod (curve parameter) potential).toFun
      component point

/-- Maxwell pullback curves are additive in the potential slot. -/
theorem gaugePotentialPullbackCurveValue_add
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    gaugePotentialPullbackCurveValue period hPeriod curve
        (first + second) component point =
      gaugePotentialPullbackCurveValue period hPeriod curve first component point +
        gaugePotentialPullbackCurveValue
          period hPeriod curve second component point := by
  funext parameter
  rw [gaugePotentialPullbackCurveValue,
    pullbackGaugePotential_add]
  rfl

/-- Maxwell pullback curves are homogeneous in the potential slot. -/
theorem gaugePotentialPullbackCurveValue_smul
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (coefficient : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    gaugePotentialPullbackCurveValue period hPeriod curve
        (coefficient • potential) component point =
      coefficient •
        gaugePotentialPullbackCurveValue period hPeriod curve
          potential component point := by
  funext parameter
  rw [gaugePotentialPullbackCurveValue,
    pullbackGaugePotential_smul]
  rfl

/-- Genuine fiber-valued derivative of the Maxwell pullback orbit. -/
def gaugePotentialDiffeomorphismGeneratorAt
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    GaugeCovectorFiber period hPeriod point :=
  deriv
    (gaugePotentialPullbackCurveValue period hPeriod
      curve potential component point) 0

theorem gaugePotentialDiffeomorphismGeneratorAt_eq_of_hasFDerivAt
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod)
    (derivative :
      Real →L[Real] GaugeCovectorFiber period hPeriod point)
    (hDerivative : HasFDerivAt
      (gaugePotentialPullbackCurveValue period hPeriod
        curve potential component point) derivative 0) :
    gaugePotentialDiffeomorphismGeneratorAt period hPeriod
        curve potential component point =
      derivative 1 := by
  simp [gaugePotentialDiffeomorphismGeneratorAt, deriv, hDerivative.fderiv]

theorem gaugePotentialDiffeomorphismGeneratorAt_apply_of_hasFDerivAt
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod)
    (derivative :
      Real →L[Real] GaugeCovectorFiber period hPeriod point)
    (hDerivative : HasFDerivAt
      (gaugePotentialPullbackCurveValue period hPeriod
        curve potential component point) derivative 0)
    (tangent : TangentSpace coverModelWithCorners point) :
    gaugePotentialDiffeomorphismGeneratorAt period hPeriod
        curve potential component point tangent =
      derivative 1 tangent := by
  rw [gaugePotentialDiffeomorphismGeneratorAt_eq_of_hasFDerivAt
    period hPeriod curve potential component point derivative hDerivative]

/-- The infinitesimal Maxwell generator is additive whenever both pullback
orbits are differentiable at the identity. -/
theorem gaugePotentialDiffeomorphismGeneratorAt_add
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod)
    (hFirst : DifferentiableAt Real
      (gaugePotentialPullbackCurveValue period hPeriod
        curve first component point) 0)
    (hSecond : DifferentiableAt Real
      (gaugePotentialPullbackCurveValue period hPeriod
        curve second component point) 0) :
    gaugePotentialDiffeomorphismGeneratorAt period hPeriod curve
        (first + second) component point =
      gaugePotentialDiffeomorphismGeneratorAt period hPeriod curve
          first component point +
        gaugePotentialDiffeomorphismGeneratorAt period hPeriod curve
          second component point := by
  simpa only [gaugePotentialDiffeomorphismGeneratorAt,
    gaugePotentialPullbackCurveValue_add] using
      (deriv_add (𝕜 := Real) hFirst hSecond)

/-- The infinitesimal Maxwell generator is unconditionally homogeneous in
the potential slot. -/
theorem gaugePotentialDiffeomorphismGeneratorAt_smul
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (coefficient : Real)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    gaugePotentialDiffeomorphismGeneratorAt period hPeriod curve
        (coefficient • potential) component point =
      coefficient •
        gaugePotentialDiffeomorphismGeneratorAt period hPeriod curve
          potential component point := by
  simpa only [gaugePotentialDiffeomorphismGeneratorAt,
    gaugePotentialPullbackCurveValue_smul] using
      (deriv_const_smul_field (𝕜 := Real) coefficient
        (gaugePotentialPullbackCurveValue period hPeriod
          curve potential component point)
        (x := 0))

/-- Exact regularity needed to bundle one Maxwell pullback curve as an action
linear in the potential. -/
structure GaugePotentialPullbackCurveDifferentiability
    (curve : Real → SpacetimeDiffeomorphism period hPeriod) : Prop where
  differentiableAt :
    ∀ potential component point,
      DifferentiableAt Real
        (gaugePotentialPullbackCurveValue period hPeriod
          curve potential component point) 0

/-- For one differentiable diffeomorphism curve, the fiber Maxwell generator
is a genuine linear map in the potential. -/
def gaugePotentialDiffeomorphismGeneratorLinearAt
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (regularity :
      GaugePotentialPullbackCurveDifferentiability period hPeriod curve)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    SmoothAbelianGaugePotential period hPeriod →ₗ[Real]
      GaugeCovectorFiber period hPeriod point where
  toFun := fun potential =>
    gaugePotentialDiffeomorphismGeneratorAt
      period hPeriod curve potential component point
  map_add' := fun first second =>
    gaugePotentialDiffeomorphismGeneratorAt_add
      period hPeriod curve first second component point
      (regularity.differentiableAt first component point)
      (regularity.differentiableAt second component point)
  map_smul' := fun coefficient potential =>
    gaugePotentialDiffeomorphismGeneratorAt_smul
      period hPeriod curve coefficient potential component point

/-- A supplied diffeomorphism flow whose one-form derivative is realized by
a genuine smooth global Maxwell variation. -/
structure SmoothGaugePotentialPullbackFlow
    (potential : SmoothAbelianGaugePotential period hPeriod) where
  curve : Real → SpacetimeDiffeomorphism period hPeriod
  atZero :
    curve 0 = Diffeomorph.refl coverModelWithCorners
      (EffectiveQuotient period hPeriod) ω
  map_add : ∀ first second,
    curve (first + second) = (curve first).trans (curve second)
  variation : SmoothAbelianGaugePotential period hPeriod
  realizes : ∀ component point,
    variation.toFun component point =
      gaugePotentialDiffeomorphismGeneratorAt period hPeriod
        curve potential component point

@[simp]
theorem SmoothGaugePotentialPullbackFlow.variation_apply
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (flow : SmoothGaugePotentialPullbackFlow period hPeriod potential)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    flow.variation.toFun component point =
      gaugePotentialDiffeomorphismGeneratorAt period hPeriod
        flow.curve potential component point :=
  flow.realizes component point

/-- Exact analogue of `MetricPairFlowToGhostContract` for Maxwell one-forms.
The contract isolates completeness and linear dependence on an arbitrary
smooth tangent ghost. -/
structure GaugePotentialFlowToGhostContract
    (potential : SmoothAbelianGaugePotential period hPeriod) where
  flow : SmoothDiffeomorphismGhost period hPeriod →
    SmoothGaugePotentialPullbackFlow period hPeriod potential
  linearizedGaugeVariation :
    SmoothDiffeomorphismGhost period hPeriod →ₗ[Real]
      SmoothAbelianGaugePotential period hPeriod
  agreesWithFlow : ∀ ghost,
    linearizedGaugeVariation ghost = (flow ghost).variation

theorem GaugePotentialFlowToGhostContract.flowVariation_add
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (contract :
      GaugePotentialFlowToGhostContract period hPeriod potential)
    (first second : SmoothDiffeomorphismGhost period hPeriod) :
    (contract.flow (first + second)).variation =
      (contract.flow first).variation +
        (contract.flow second).variation := by
  rw [← contract.agreesWithFlow, ← contract.agreesWithFlow,
    ← contract.agreesWithFlow]
  exact contract.linearizedGaugeVariation.map_add first second

theorem GaugePotentialFlowToGhostContract.flowVariation_smul
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (contract :
      GaugePotentialFlowToGhostContract period hPeriod potential)
    (coefficient : Real)
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    (contract.flow (coefficient • ghost)).variation =
      coefficient • (contract.flow ghost).variation := by
  rw [← contract.agreesWithFlow, ← contract.agreesWithFlow]
  exact contract.linearizedGaugeVariation.map_smul coefficient ghost

/-- One combined inventory for the already existing metric flow bridge and
the new Maxwell bridge. -/
structure TensorialFlowToGhostData
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) where
  metric :
    MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric
  gauge :
    GaugePotentialFlowToGhostContract period hPeriod potential

end
end P0EFTJanusMappingTorusGaugePotentialDiffeomorphismGenerator4D
end JanusFormal
