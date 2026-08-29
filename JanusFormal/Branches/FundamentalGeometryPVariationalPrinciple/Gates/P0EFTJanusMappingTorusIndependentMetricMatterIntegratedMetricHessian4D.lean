import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMetricHessian4D

/-!
# Integrated pure metric Hessian of the scalar matter action

This gate integrates the genuine pointwise scale-chart Hessian of all eight
scalar components.  Differentiation under the integral is controlled by an
explicit local domination contract.  The base first variation is identified
with the metric-only derivative of the existing Program-P matter action.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMetricHessian4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothDiagonalInteraction4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMetricD9Variation4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMetricHessian4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

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

/-- Integral of the metric-only first variation of all scalar components. -/
def integratedIndependentMatterMetricScaleFirstVariation
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod) : Real :=
  ∑ component : MatterComponentIndex,
    ∫ point, independentMatterMetricScaleFirstVariation period hPeriod
      (massSquared component) fields direction component point ∂measure

/-- The scale-chart first variation is exactly the existing integrated
metric-only Program-P first variation. -/
theorem integratedIndependentMatterMetricScaleFirstVariation_eq_metricOnly
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod) :
    integratedIndependentMatterMetricScaleFirstVariation period hPeriod measure
        massSquared fields direction =
      integratedIndependentMetricMatterFirstVariation period hPeriod measure
        massSquared fields
        (metricOnlyRobinCompleteVariation period hPeriod direction) := by
  unfold integratedIndependentMatterMetricScaleFirstVariation
    integratedIndependentMetricMatterFirstVariation
  apply Finset.sum_congr rfl
  intro component _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point => by
    simpa only [metricOnlyRobinCompleteVariation,
      includeCompleteVariation_complete, independentCompleteVariation_independent]
      using
        (independentMetricMatterFirstVariationDensity_metricOnly_eq_scaleFirstVariation
          period hPeriod (massSquared component) fields direction component
          point).symm

/-- Consequently, this base coefficient is the derivative of the existing
global eight-component matter action. -/
theorem programPMetricMatterMetricOnlyActionCurve_hasDerivAt
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (contract : DominatedIndependentMetricMatterVariationContract period hPeriod
      measure massSquared fields
      (metricOnlyRobinCompleteVariation period hPeriod direction)) :
    HasDerivAt
      (programPMetricMatterActionCurve period hPeriod measure massSquared fields
        (metricOnlyRobinCompleteVariation period hPeriod direction))
      (integratedIndependentMatterMetricScaleFirstVariation period hPeriod measure
        massSquared fields direction) 0 := by
  have hDerivative := programPMetricMatterActionCurve_hasDerivAt period hPeriod
    measure massSquared fields
    (metricOnlyRobinCompleteVariation period hPeriod direction) contract
  refine hDerivative.congr_deriv ?_
  exact
    (integratedIndependentMatterMetricScaleFirstVariation_eq_metricOnly
      period hPeriod measure massSquared fields direction).symm

/-- Integrated first metric variation in `first`, evaluated along the affine
scale curve generated by `second`. -/
def integratedIndependentMatterMetricFirstVariationAlongSecond
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (parameter : Real) : Real :=
  ∑ component : MatterComponentIndex,
    ∫ point, independentMatterMetricFirstVariationAlongSecond period hPeriod
      (massSquared component) fields first second component point parameter
      ∂measure

@[simp]
theorem integratedIndependentMatterMetricFirstVariationAlongSecond_zero
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod) :
    integratedIndependentMatterMetricFirstVariationAlongSecond period hPeriod
        measure massSquared fields first second 0 =
      integratedIndependentMatterMetricScaleFirstVariation period hPeriod measure
        massSquared fields first := by
  unfold integratedIndependentMatterMetricFirstVariationAlongSecond
    integratedIndependentMatterMetricScaleFirstVariation
  apply Finset.sum_congr rfl
  intro component _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point => by
    exact independentMatterMetricFirstVariationAlongSecond_zero period hPeriod
      (massSquared component) fields first second component point

/-- Integral of the genuine pure metric Hessian density of all eight scalar
components. -/
def integratedIndependentMatterMetricHessian
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod) : Real :=
  ∑ component : MatterComponentIndex,
    ∫ point, independentMatterMetricHessianDensity period hPeriod
      (massSquared component) fields first second component point ∂measure

/-- Explicit local domination hypotheses for the second differentiation
under every component integral. -/
structure DominatedIndependentMatterMetricSecondVariationContract
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod) where
  parameterDomain : Set Real
  parameterDomain_mem_nhds : parameterDomain ∈ nhds (0 : Real)
  curve_mem_domain : ∀ component point parameter,
    parameter ∈ parameterDomain →
      independentMatterMetricScaleCurve period hPeriod fields second component
        point parameter ∈ positiveMagnitudeDomain
  firstVariation_aeStronglyMeasurable : ∀ component,
    ∀ᶠ parameter in nhds (0 : Real),
      AEStronglyMeasurable
        (fun point => independentMatterMetricFirstVariationAlongSecond
          period hPeriod (massSquared component) fields first second component
          point parameter)
        measure
  firstVariation_integrable_at_zero : ∀ component,
    Integrable
      (fun point => independentMatterMetricFirstVariationAlongSecond
        period hPeriod (massSquared component) fields first second component
        point 0)
      measure
  hessian_aeStronglyMeasurable : ∀ component,
    AEStronglyMeasurable
      (independentMatterMetricHessianDensity period hPeriod
        (massSquared component) fields first second component)
      measure
  bound : MatterComponentIndex → EffectiveQuotient period hPeriod → Real
  derivative_norm_le : ∀ component, ∀ᵐ point ∂measure,
    ∀ parameter ∈ parameterDomain,
      ‖fderiv Real
          (fderiv Real
            (independentMatterScaleDensityFunction period hPeriod
              (massSquared component) fields component point))
          (independentMatterMetricScaleCurve period hPeriod fields second
            component point parameter)
          (independentMatterScaleDirection period hPeriod fields second
            component.1 point)
          (independentMatterScaleDirection period hPeriod fields first
            component.1 point)‖ ≤
        bound component point
  bound_integrable : ∀ component, Integrable (bound component) measure

/-- The integrated first variation differentiates to the pure scalar
metric--metric Hessian. -/
theorem integratedIndependentMatterMetricFirstVariationAlongSecond_hasDerivAt
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (contract : DominatedIndependentMatterMetricSecondVariationContract
      period hPeriod measure massSquared fields first second) :
    HasDerivAt
      (integratedIndependentMatterMetricFirstVariationAlongSecond period hPeriod
        measure massSquared fields first second)
      (integratedIndependentMatterMetricHessian period hPeriod measure
        massSquared fields first second) 0 := by
  unfold integratedIndependentMatterMetricFirstVariationAlongSecond
    integratedIndependentMatterMetricHessian
  exact HasDerivAt.fun_sum fun component _ => by
    have hPointwise : ∀ᵐ point ∂measure,
        ∀ parameter ∈ contract.parameterDomain,
          HasDerivAt
            (fun varied =>
              independentMatterMetricFirstVariationAlongSecond period hPeriod
                (massSquared component) fields first second component point
                varied)
            (fderiv Real
              (fderiv Real
                (independentMatterScaleDensityFunction period hPeriod
                  (massSquared component) fields component point))
              (independentMatterMetricScaleCurve period hPeriod fields second
                component point parameter)
              (independentMatterScaleDirection period hPeriod fields second
                component.1 point)
              (independentMatterScaleDirection period hPeriod fields first
                component.1 point))
            parameter :=
      Filter.Eventually.of_forall fun point parameter hParameter => by
        simpa only [independentMatterMetricFirstVariationAlongSecond] using
          independentMatterMetricFirstVariationAlongSecond_hasDerivAt
            period hPeriod (massSquared component) fields first second component
            point parameter
            (contract.curve_mem_domain component point parameter hParameter)
    have hHessianMeasurable :=
      contract.hessian_aeStronglyMeasurable component
    change AEStronglyMeasurable
      (fun point =>
        fderiv Real
          (fderiv Real
            (independentMatterScaleDensityFunction period hPeriod
              (massSquared component) fields component point))
          (independentMatterScale period hPeriod fields component.1 point)
          (independentMatterScaleDirection period hPeriod fields second
            component.1 point)
          (independentMatterScaleDirection period hPeriod fields first
            component.1 point))
      measure at hHessianMeasurable
    have hIntegral := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun parameter point =>
        independentMatterMetricFirstVariationAlongSecond period hPeriod
          (massSquared component) fields first second component point parameter)
      (F' := fun parameter point =>
        fderiv Real
          (fderiv Real
            (independentMatterScaleDensityFunction period hPeriod
              (massSquared component) fields component point))
          (independentMatterMetricScaleCurve period hPeriod fields second
            component point parameter)
          (independentMatterScaleDirection period hPeriod fields second
            component.1 point)
          (independentMatterScaleDirection period hPeriod fields first
            component.1 point))
      (bound := contract.bound component)
      contract.parameterDomain_mem_nhds
      (contract.firstVariation_aeStronglyMeasurable component)
      (contract.firstVariation_integrable_at_zero component)
      (by
        simpa only [independentMatterMetricScaleCurve_zero] using
          hHessianMeasurable)
      (contract.derivative_norm_le component)
      (contract.bound_integrable component)
      hPointwise
    simpa only [independentMatterMetricScaleCurve_zero,
      independentMatterMetricHessianDensity] using hIntegral.2

/-- The integrated pure metric Hessian is symmetric. -/
theorem integratedIndependentMatterMetricHessian_symmetric
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod) :
    integratedIndependentMatterMetricHessian period hPeriod measure massSquared
        fields first second =
      integratedIndependentMatterMetricHessian period hPeriod measure massSquared
        fields second first := by
  unfold integratedIndependentMatterMetricHessian
  apply Finset.sum_congr rfl
  intro component _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    independentMatterMetricHessianDensity_symmetric period hPeriod
      (massSquared component) fields first second component point

end

end P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMetricHessian4D
end JanusFormal
