import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMixedHessian4D

/-!
# Integrated metric--matter mixed variation of the same global action

This gate first differentiates the existing eight-component global
metric--matter action in a genuine matter-only direction, at every point of
the actual exponential diagonal-metric curve.  It then differentiates that
first derivative in the metric direction and passes the pointwise mixed
variation under the same spacetime integral.

Both passages under the integral use explicit local Lipschitz domination
contracts: measurability, integrability at the base point, a common parameter
neighbourhood and an integrable majorant.  No derivative or Hessian identity
is stored as a hypothesis.  The result remains conditional on these analytic
contracts and concerns only the eight scalar matter terms; it does not add the
Candidate-A interaction, Einstein--Hilbert, Maxwell, ghosts, boundary terms,
or a global Programme-P Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMixedHessian4D

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonMetricD9Variation4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMixedHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The common fields on the genuine exponential diagonal-metric curve. -/
def metricOnlyIndependentFieldsCurve
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (metricParameter : Real) : IndependentFields period hPeriod :=
  independentFieldCurve period hPeriod fields
    (metricOnlyIndependentVariation period hPeriod metricDirection)
    metricParameter

/-- Two-parameter restriction of the same eight-component global action:
first move the metric, then move all eight actual matter components. -/
def programPMetricMatterNestedActionCurve
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (metricParameter matterParameter : Real) : Real :=
  programPMetricMatterActionCurve period hPeriod measure massSquared
    (metricOnlyIndependentFieldsCurve period hPeriod fields metricDirection
      metricParameter)
    (matterOnlyRobinCompleteVariation period hPeriod matterDirection)
    matterParameter

/-- Integral of the matter derivative of that same action along the outer
metric curve. -/
def integratedIndependentMatterEulerCurve
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (metricParameter : Real) : Real :=
  ∑ component : MatterComponentIndex,
    ∫ point, independentMatterEulerDensity period hPeriod
      (massSquared component)
      (metricOnlyIndependentFieldsCurve period hPeriod fields metricDirection
        metricParameter)
      matterDirection component point ∂measure

/-- Integral of the explicit pointwise mixed metric--matter density. -/
def integratedIndependentMetricMatterMixedVariation
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber) : Real :=
  ∑ component : MatterComponentIndex,
    ∫ point, independentMetricMatterMixedDensity period hPeriod
      (massSquared component) fields metricDirection matterDirection component point
      ∂measure

/-- Genuine analytic hypotheses for both differentiations under the integral.
The inner field is the existing first-variation domination contract at every
outer metric parameter; the remaining fields dominate the outer derivative
of the matter Euler density. -/
structure DominatedIndependentMetricMatterMixedVariationContract
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber) where
  innerContract : ∀ metricParameter,
    DominatedIndependentMetricMatterVariationContract period hPeriod measure
      massSquared
      (metricOnlyIndependentFieldsCurve period hPeriod fields metricDirection
        metricParameter)
      (matterOnlyRobinCompleteVariation period hPeriod matterDirection)
  parameterDomain : Set Real
  parameterDomain_mem_nhds : parameterDomain ∈ nhds (0 : Real)
  eulerDensity_aeStronglyMeasurable : ∀ component,
    ∀ᶠ metricParameter in nhds (0 : Real),
      AEStronglyMeasurable
        (fun point ↦ independentMatterEulerDensity period hPeriod
          (massSquared component)
          (metricOnlyIndependentFieldsCurve period hPeriod fields metricDirection
            metricParameter)
          matterDirection component point)
        measure
  eulerDensity_integrable_at_zero : ∀ component,
    Integrable
      (fun point ↦ independentMatterEulerDensity period hPeriod
        (massSquared component)
        (metricOnlyIndependentFieldsCurve period hPeriod fields metricDirection 0)
        matterDirection component point)
      measure
  mixedDensity_aeStronglyMeasurable : ∀ component,
    AEStronglyMeasurable
      (independentMetricMatterMixedDensity period hPeriod
        (massSquared component) fields metricDirection matterDirection component)
      measure
  bound : MatterComponentIndex → EffectiveQuotient period hPeriod → Real
  eulerDensity_lipschitz : ∀ component, ∀ᵐ point ∂measure,
    LipschitzOnWith (Real.nnabs (bound component point))
      (fun metricParameter ↦ independentMatterEulerDensity period hPeriod
        (massSquared component)
        (metricOnlyIndependentFieldsCurve period hPeriod fields metricDirection
          metricParameter)
        matterDirection component point)
      parameterDomain
  bound_integrable : ∀ component, Integrable (bound component) measure

/-- At every outer metric parameter, the displayed Euler integral is the
actual matter derivative of the same global eight-component action. -/
theorem programPMetricMatterNestedActionCurve_matter_hasDerivAt
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (contract : DominatedIndependentMetricMatterMixedVariationContract
      period hPeriod measure massSquared fields metricDirection matterDirection)
    (metricParameter : Real) :
    HasDerivAt
      (programPMetricMatterNestedActionCurve period hPeriod measure massSquared
        fields metricDirection matterDirection metricParameter)
      (integratedIndependentMatterEulerCurve period hPeriod measure massSquared
        fields metricDirection matterDirection metricParameter) 0 := by
  unfold programPMetricMatterNestedActionCurve
  have hDerivative := programPMetricMatterActionCurve_hasDerivAt period hPeriod
    measure massSquared
    (metricOnlyIndependentFieldsCurve period hPeriod fields metricDirection
      metricParameter)
    (matterOnlyRobinCompleteVariation period hPeriod matterDirection)
    (contract.innerContract metricParameter)
  refine hDerivative.congr_deriv ?_
  unfold integratedIndependentMetricMatterFirstVariation
    integratedIndependentMatterEulerCurve
  apply Finset.sum_congr rfl
  intro component _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point ↦ by
    simpa [matterOnlyRobinCompleteVariation] using
      independentMetricMatterFirstVariationDensity_matterOnly period hPeriod
        (massSquared component)
        (metricOnlyIndependentFieldsCurve period hPeriod fields metricDirection
          metricParameter)
        matterDirection component point

/-- The outer metric derivative passes through the same integral and is the
integral of the explicit pointwise mixed second variation. -/
theorem integratedIndependentMatterEulerCurve_hasDerivAt
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (contract : DominatedIndependentMetricMatterMixedVariationContract
      period hPeriod measure massSquared fields metricDirection matterDirection) :
    HasDerivAt
      (integratedIndependentMatterEulerCurve period hPeriod measure massSquared
        fields metricDirection matterDirection)
      (integratedIndependentMetricMatterMixedVariation period hPeriod measure
        massSquared fields metricDirection matterDirection) 0 := by
  unfold integratedIndependentMatterEulerCurve
    integratedIndependentMetricMatterMixedVariation
  exact HasDerivAt.fun_sum fun component _ ↦ by
    have hPointwise : ∀ᵐ point ∂measure,
        HasDerivAt
          (fun metricParameter ↦ independentMatterEulerDensity period hPeriod
            (massSquared component)
            (metricOnlyIndependentFieldsCurve period hPeriod fields
              metricDirection metricParameter)
            matterDirection component point)
          (independentMetricMatterMixedDensity period hPeriod
            (massSquared component) fields metricDirection matterDirection
            component point) 0 :=
      Filter.Eventually.of_forall fun point ↦ by
        simpa [metricOnlyIndependentFieldsCurve] using
          independentMatterEulerDensity_metricOnlyCurve_hasDerivAt period hPeriod
            (massSquared component) fields metricDirection matterDirection
            component point
    have hIntegral := hasDerivAt_integral_of_dominated_loc_of_lip
      (F := fun metricParameter point ↦ independentMatterEulerDensity
        period hPeriod (massSquared component)
        (metricOnlyIndependentFieldsCurve period hPeriod fields metricDirection
          metricParameter)
        matterDirection component point)
      (F' := independentMetricMatterMixedDensity period hPeriod
        (massSquared component) fields metricDirection matterDirection component)
      (bound := contract.bound component)
      contract.parameterDomain_mem_nhds
      (contract.eulerDensity_aeStronglyMeasurable component)
      (contract.eulerDensity_integrable_at_zero component)
      (contract.mixedDensity_aeStronglyMeasurable component)
      (contract.eulerDensity_lipschitz component)
      (contract.bound_integrable component) hPointwise
    exact hIntegral.2

/-- Curve of actual inner derivatives of the same global action. -/
def programPMetricMatterIntegratedMixedDerivativeCurve
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (metricParameter : Real) : Real :=
  deriv
    (programPMetricMatterNestedActionCurve period hPeriod measure massSquared fields
      metricDirection matterDirection metricParameter) 0

/-- Conditional integrated mixed Hessian identity for the same global
eight-component metric--matter action. -/
theorem programPMetricMatterIntegratedMixedDerivativeCurve_hasDerivAt
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (contract : DominatedIndependentMetricMatterMixedVariationContract
      period hPeriod measure massSquared fields metricDirection matterDirection) :
    HasDerivAt
      (programPMetricMatterIntegratedMixedDerivativeCurve period hPeriod measure
        massSquared fields metricDirection matterDirection)
      (integratedIndependentMetricMatterMixedVariation period hPeriod measure
        massSquared fields metricDirection matterDirection) 0 := by
  have hCurve :
      programPMetricMatterIntegratedMixedDerivativeCurve period hPeriod measure
          massSquared fields metricDirection matterDirection =
        integratedIndependentMatterEulerCurve period hPeriod measure massSquared
          fields metricDirection matterDirection := by
    funext metricParameter
    exact (programPMetricMatterNestedActionCurve_matter_hasDerivAt period hPeriod
      measure massSquared fields metricDirection matterDirection contract
      metricParameter).deriv
  rw [hCurve]
  exact integratedIndependentMatterEulerCurve_hasDerivAt period hPeriod measure
    massSquared fields metricDirection matterDirection contract

end

end P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMixedHessian4D
end JanusFormal
