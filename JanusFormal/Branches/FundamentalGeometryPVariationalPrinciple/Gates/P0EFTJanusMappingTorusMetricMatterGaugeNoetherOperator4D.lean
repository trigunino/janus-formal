import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCovariantTensorDiffeomorphismGenerator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMatterGaugeNoetherOperator4D

/-!
# Conditional global metric, matter and gauge R/B blocks on D8

The existing tensor gate constructs the infinitesimal pullback only in one
fiber.  Here a genuine one-parameter diffeomorphism flow is required to carry
those fiber derivatives into smooth global covariant two-tensor sections.

Mathlib does not currently turn an arbitrary smooth tangent ghost into a
complete flow, nor prove linear dependence of that flow derivative on the
ghost.  `MetricPairFlowToGhostContract` isolates exactly those two missing
inputs.  Conditional on that contract, both metric blocks combine
type-correctly with the already concrete matter and `U(1)^2` blocks, and the
corresponding algebraic B/Noether operator is constructed.  It is not called
an unconditional full gauge generator.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMetricMatterGaugeNoetherOperator4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCovariantTensorDiffeomorphismGenerator4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusMatterGaugeNoetherOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- One honest complete one-parameter diffeomorphism flow acting on a pair of
intrinsic metrics.  The two infinitesimal variations are genuine smooth
global sections and are required to realize the fiberwise pullback derivative
already constructed in the pointwise tensor gate.

The `realizes` fields are the exact parameter-differentiation-to-section
regularity input; orbit smoothness alone does not currently imply them through
Mathlib's dependent bundle API. -/
structure SmoothMetricPairPullbackFlow
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod) where
  curve : Real → SpacetimeDiffeomorphism period hPeriod
  atZero :
    curve 0 = Diffeomorph.refl coverModelWithCorners
      (EffectiveQuotient period hPeriod) ω
  map_add : ∀ first second,
    curve (first + second) = (curve first).trans (curve second)
  orbit_smooth : ∀ point,
    ContMDiff 𝓘(Real, Real) coverModelWithCorners ω
      (fun parameter ↦ curve parameter point)
  plusVariation : SmoothCovariantTwoTensor period hPeriod
  minusVariation : SmoothCovariantTwoTensor period hPeriod
  plus_realizes : ∀ point,
    plusVariation point =
      covariantTensorDiffeomorphismGeneratorAt period hPeriod curve
        plusMetric.tensor.toTensorField point
  minus_realizes : ∀ point,
    minusVariation point =
      covariantTensorDiffeomorphismGeneratorAt period hPeriod curve
        minusMetric.tensor.toTensorField point
  plusVariation_symmetric : IsSymmetric period hPeriod plusVariation
  minusVariation_symmetric : IsSymmetric period hPeriod minusVariation

/-- Each point of a global flow gives the smooth spacetime orbit used by the
existing intrinsic infinitesimal-generator definition. -/
def SmoothMetricPairPullbackFlow.orbit
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (flow : SmoothMetricPairPullbackFlow period hPeriod plusMetric minusMetric)
    (point : EffectiveQuotient period hPeriod) :
    SmoothSpacetimeOrbit period hPeriod point where
  orbit := fun parameter ↦ flow.curve parameter point
  smooth := flow.orbit_smooth point
  atZero := by
    rw [flow.atZero]
    rfl

/-- Velocity of a supplied flow, transported from its definitionally
dependent fiber at time zero to the original tangent fiber. -/
def SmoothMetricPairPullbackFlow.velocityAt
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (flow : SmoothMetricPairPullbackFlow period hPeriod plusMetric minusMetric)
    (point : EffectiveQuotient period hPeriod) :
    TangentSpace coverModelWithCorners point :=
  (flow.orbit period hPeriod plusMetric minusMetric point).atZero ▸
    infinitesimalGenerator period hPeriod
      (flow.orbit period hPeriod plusMetric minusMetric point)

/-- The plus variation packaged as a genuine smooth symmetric covariant
two-tensor section. -/
def SmoothMetricPairPullbackFlow.plusSymmetricVariation
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (flow : SmoothMetricPairPullbackFlow period hPeriod plusMetric minusMetric) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor := flow.plusVariation
  symmetric := flow.plusVariation_symmetric

/-- The minus variation packaged as a genuine smooth symmetric covariant
two-tensor section. -/
def SmoothMetricPairPullbackFlow.minusSymmetricVariation
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (flow : SmoothMetricPairPullbackFlow period hPeriod plusMetric minusMetric) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor := flow.minusVariation
  symmetric := flow.minusVariation_symmetric

@[simp]
theorem SmoothMetricPairPullbackFlow.plusVariation_apply
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (flow : SmoothMetricPairPullbackFlow period hPeriod plusMetric minusMetric)
    (point : EffectiveQuotient period hPeriod) :
    flow.plusVariation point =
      covariantTensorDiffeomorphismGeneratorAt period hPeriod flow.curve
        plusMetric.tensor.toTensorField point :=
  flow.plus_realizes point

@[simp]
theorem SmoothMetricPairPullbackFlow.minusVariation_apply
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (flow : SmoothMetricPairPullbackFlow period hPeriod plusMetric minusMetric)
    (point : EffectiveQuotient period hPeriod) :
    flow.minusVariation point =
      covariantTensorDiffeomorphismGeneratorAt period hPeriod flow.curve
        minusMetric.tensor.toTensorField point :=
  flow.minus_realizes point

/-- Exact bridge still needed to integrate arbitrary smooth ghosts.  It says:
each ghost has a complete flow with that velocity, and the resulting pair of
global metric variations depends linearly on the ghost. -/
structure MetricPairFlowToGhostContract
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod) where
  flow : SmoothDiffeomorphismGhost period hPeriod →
    SmoothMetricPairPullbackFlow period hPeriod plusMetric minusMetric
  generatesGhost : ∀ ghost point,
    (flow ghost).velocityAt period hPeriod plusMetric minusMetric point = ghost point
  linearizedMetricVariation :
    SmoothDiffeomorphismGhost period hPeriod →ₗ[Real]
      (SmoothCovariantTwoTensor period hPeriod ×
        SmoothCovariantTwoTensor period hPeriod)
  agreesWithFlow : ∀ ghost,
    linearizedMetricVariation ghost =
      ((flow ghost).plusVariation, (flow ghost).minusVariation)

/-- The supplied flow variations obey addition because the contract supplies
the otherwise-missing linear dependence on the ghost. -/
theorem MetricPairFlowToGhostContract.flowVariation_add
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (first second : SmoothDiffeomorphismGhost period hPeriod) :
    ((contract.flow (first + second)).plusVariation,
        (contract.flow (first + second)).minusVariation) =
      ((contract.flow first).plusVariation,
          (contract.flow first).minusVariation) +
        ((contract.flow second).plusVariation,
          (contract.flow second).minusVariation) := by
  rw [← contract.agreesWithFlow, ← contract.agreesWithFlow,
    ← contract.agreesWithFlow]
  exact contract.linearizedMetricVariation.map_add first second

/-- The analogous scalar law for supplied flow variations. -/
theorem MetricPairFlowToGhostContract.flowVariation_smul
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (scalar : Real) (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    ((contract.flow (scalar • ghost)).plusVariation,
        (contract.flow (scalar • ghost)).minusVariation) =
      scalar • ((contract.flow ghost).plusVariation,
        (contract.flow ghost).minusVariation) := by
  rw [← contract.agreesWithFlow, ← contract.agreesWithFlow]
  exact contract.linearizedMetricVariation.map_smul scalar ghost

/-- Variations of two intrinsic metric tensors, eight matter scalars and two
abelian gauge potentials. -/
abbrev MetricMatterGaugeVariationSpace :=
  (SmoothCovariantTwoTensor period hPeriod ×
      SmoothCovariantTwoTensor period hPeriod) ×
    MatterGaugeVariationSpace period hPeriod

/-- Conditional combined linearized variation.  This is not an
unconditional full `R`: its metric block depends explicitly on the supplied
flow-to-ghost contract. -/
def metricMatterGaugeLinearizedVariation
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric) :
    MatterGaugeParameterSpace period hPeriod →ₗ[Real]
      MetricMatterGaugeVariationSpace period hPeriod where
  toFun parameters :=
    (contract.linearizedMetricVariation parameters.1,
      matterGaugeGenerator period hPeriod fields parameters)
  map_add' first second := by
    apply Prod.ext
    · exact contract.linearizedMetricVariation.map_add first.1 second.1
    · exact (matterGaugeGenerator period hPeriod fields).map_add first second
  map_smul' scalar parameters := by
    apply Prod.ext
    · exact contract.linearizedMetricVariation.map_smul scalar parameters.1
    · exact (matterGaugeGenerator period hPeriod fields).map_smul scalar parameters

@[simp]
theorem metricMatterGaugeLinearizedVariation_metric
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (parameters : MatterGaugeParameterSpace period hPeriod) :
    (metricMatterGaugeLinearizedVariation period hPeriod fields plusMetric
      minusMetric contract parameters).1 =
        ((contract.flow parameters.1).plusVariation,
          (contract.flow parameters.1).minusVariation) := by
  exact contract.agreesWithFlow parameters.1

@[simp]
theorem metricMatterGaugeLinearizedVariation_matterGauge
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (parameters : MatterGaugeParameterSpace period hPeriod) :
    (metricMatterGaugeLinearizedVariation period hPeriod fields plusMetric
      minusMetric contract parameters).2 =
        matterGaugeGenerator period hPeriod fields parameters :=
  rfl

/-- Both metric components of the conditional combined variation are smooth
and symmetric global sections. -/
theorem metricMatterGaugeLinearizedVariation_metric_symmetric
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (parameters : MatterGaugeParameterSpace period hPeriod) :
    IsSymmetric period hPeriod
        (metricMatterGaugeLinearizedVariation period hPeriod fields plusMetric
          minusMetric contract parameters).1.1 ∧
      IsSymmetric period hPeriod
        (metricMatterGaugeLinearizedVariation period hPeriod fields plusMetric
          minusMetric contract parameters).1.2 := by
  rw [metricMatterGaugeLinearizedVariation_metric]
  exact ⟨(contract.flow parameters.1).plusVariation_symmetric,
    (contract.flow parameters.1).minusVariation_symmetric⟩

/-- Algebraic B/Noether candidate for the conditional combined variation,
again with no claim that the arbitrary covector is an action derivative. -/
def metricMatterGaugeNoetherOperator
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (euler : MetricMatterGaugeVariationSpace period hPeriod →ₗ[Real] Real) :
    MatterGaugeParameterSpace period hPeriod →ₗ[Real] Real :=
  euler.comp (metricMatterGaugeLinearizedVariation period hPeriod fields
    plusMetric minusMetric contract)

@[simp]
theorem metricMatterGaugeNoetherOperator_apply
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (euler : MetricMatterGaugeVariationSpace period hPeriod →ₗ[Real] Real)
    (parameters : MatterGaugeParameterSpace period hPeriod) :
    metricMatterGaugeNoetherOperator period hPeriod fields plusMetric minusMetric
        contract euler parameters =
      euler
        (((contract.flow parameters.1).plusVariation,
            (contract.flow parameters.1).minusVariation),
          matterGaugeGenerator period hPeriod fields parameters) := by
  rw [metricMatterGaugeNoetherOperator, LinearMap.comp_apply]
  apply congrArg euler
  apply Prod.ext
  · exact metricMatterGaugeLinearizedVariation_metric period hPeriod fields
      plusMetric minusMetric contract parameters
  · rfl

/-- Vanishing of the conditional B operator is exactly annihilation of every
metric, matter and gauge direction produced by the same supplied contract. -/
theorem metricMatterGaugeNoetherOperator_eq_zero_iff
    (fields : IndependentFields period hPeriod)
    (plusMetric minusMetric :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (contract : MetricPairFlowToGhostContract period hPeriod plusMetric minusMetric)
    (euler : MetricMatterGaugeVariationSpace period hPeriod →ₗ[Real] Real) :
    metricMatterGaugeNoetherOperator period hPeriod fields plusMetric minusMetric
        contract euler = 0 ↔
      ∀ parameters : MatterGaugeParameterSpace period hPeriod,
        euler (metricMatterGaugeLinearizedVariation period hPeriod fields
          plusMetric minusMetric contract parameters) = 0 := by
  constructor
  · intro hZero parameters
    exact LinearMap.congr_fun hZero parameters
  · intro hAnnihilates
    apply LinearMap.ext
    intro parameters
    exact hAnnihilates parameters

end

end P0EFTJanusMappingTorusMetricMatterGaugeNoetherOperator4D
end JanusFormal
