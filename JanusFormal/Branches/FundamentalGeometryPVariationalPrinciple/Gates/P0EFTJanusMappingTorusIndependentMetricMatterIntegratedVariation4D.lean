import Mathlib.Analysis.Calculus.ParametricIntegral
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIndependentMetricMatterPointwiseVariation4D

/-!
# Integrated metric--matter variation on the common Program-P curve

This gate integrates the pointwise metric--matter variation of the eight
actual scalar components.  Each scalar and its sector-selected metric are
evaluated on the same `IndependentFields` curve carried by one
`ProgramPRobinCompleteVariation4D`, with the same measure and masses as the
existing Candidate-A sector matter data.

Differentiation under the integral is conditional on the standard explicit
local Lipschitz domination contract.  No covariant stress decomposition,
mixed Hessian, Einstein--Hilbert, Maxwell, ghost, or global Programme-P
closure is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseVariation4D

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

/-- The genuine global eight-component action, with every scalar coupled to
the metric stored in the same plus/minus sector of one configuration. -/
def globalIndependentMetricMatterAction
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod) : Real :=
  ∑ component : MatterComponentIndex,
    globalHolonomicScalarAction period hPeriod (massSquared component)
      (independentMatterMagnitude period hPeriod fields component.1)
      (independentMatterComponentFamily period hPeriod fields component) measure

/-- The global action above evaluated on the simultaneous metric--matter
curve selected by one Robin-complete direction. -/
def programPMetricMatterActionCurve
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : Real :=
  globalIndependentMetricMatterAction period hPeriod measure massSquared
    (independentFieldCurve period hPeriod fields
      direction.complete.independent parameter)

/-- Integral of the exact pointwise first variation, summed over the eight
matter coordinates. -/
def integratedIndependentMetricMatterFirstVariation
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod) : Real :=
  ∑ component : MatterComponentIndex,
    ∫ point, independentMetricMatterFirstVariationDensity period hPeriod
      (massSquared component) fields direction.complete.independent component point
      ∂measure

/-- Explicit analytic hypotheses for differentiating every component of the
common global metric--matter action under the integral. -/
structure DominatedIndependentMetricMatterVariationContract
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod) where
  parameterDomain : Set Real
  parameterDomain_mem_nhds : parameterDomain ∈ nhds (0 : Real)
  density_aeStronglyMeasurable : ∀ component,
    ∀ᶠ parameter in nhds (0 : Real),
      AEStronglyMeasurable
        (fun point ↦ programPMetricMatterDensityCurve period hPeriod
          (massSquared component) fields direction component point parameter)
        measure
  density_integrable_at_zero : ∀ component,
    Integrable
      (fun point ↦ programPMetricMatterDensityCurve period hPeriod
        (massSquared component) fields direction component point 0) measure
  variation_aeStronglyMeasurable : ∀ component,
    AEStronglyMeasurable
      (independentMetricMatterFirstVariationDensity period hPeriod
        (massSquared component) fields direction.complete.independent component)
      measure
  bound : MatterComponentIndex → EffectiveQuotient period hPeriod → Real
  density_lipschitz : ∀ component, ∀ᵐ point ∂measure,
    LipschitzOnWith (Real.nnabs (bound component point))
      (programPMetricMatterDensityCurve period hPeriod
        (massSquared component) fields direction component point)
      parameterDomain
  bound_integrable : ∀ component, Integrable (bound component) measure

/-- One component of the true global action is differentiable under the
displayed domination contract. -/
theorem programPMetricMatterComponentAction_hasDerivAt
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (contract : DominatedIndependentMetricMatterVariationContract period hPeriod
      measure massSquared fields direction)
    (component : MatterComponentIndex) :
    HasDerivAt
      (fun parameter ↦ ∫ point,
        programPMetricMatterDensityCurve period hPeriod
          (massSquared component) fields direction component point parameter
          ∂measure)
      (∫ point, independentMetricMatterFirstVariationDensity period hPeriod
        (massSquared component) fields direction.complete.independent component
        point ∂measure) 0 := by
  have hPointwise : ∀ᵐ point ∂measure,
      HasDerivAt
        (programPMetricMatterDensityCurve period hPeriod
          (massSquared component) fields direction component point)
        (independentMetricMatterFirstVariationDensity period hPeriod
          (massSquared component) fields direction.complete.independent component
          point) 0 :=
    Filter.Eventually.of_forall fun point ↦
      programPMetricMatterDensityCurve_hasDerivAt period hPeriod
        (massSquared component) fields direction component point
  have hIntegral := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun parameter point ↦
      programPMetricMatterDensityCurve period hPeriod
        (massSquared component) fields direction component point parameter)
    (F' := independentMetricMatterFirstVariationDensity period hPeriod
      (massSquared component) fields direction.complete.independent component)
    (bound := contract.bound component)
    contract.parameterDomain_mem_nhds
    (contract.density_aeStronglyMeasurable component)
    (contract.density_integrable_at_zero component)
    (contract.variation_aeStronglyMeasurable component)
    (contract.density_lipschitz component)
    (contract.bound_integrable component) hPointwise
  exact hIntegral.2

/-- The exact integrated metric--matter first variation is the derivative of
the one global eight-component action on the common Program-P curve. -/
theorem programPMetricMatterActionCurve_hasDerivAt
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (contract : DominatedIndependentMetricMatterVariationContract period hPeriod
      measure massSquared fields direction) :
    HasDerivAt
      (programPMetricMatterActionCurve period hPeriod measure massSquared fields
        direction)
      (integratedIndependentMetricMatterFirstVariation period hPeriod measure
        massSquared fields direction) 0 := by
  unfold programPMetricMatterActionCurve globalIndependentMetricMatterAction
    integratedIndependentMetricMatterFirstVariation
  exact HasDerivAt.fun_sum fun component _ ↦ by
    simpa [globalHolonomicScalarAction, programPMetricMatterDensityCurve] using
      programPMetricMatterComponentAction_hasDerivAt period hPeriod measure
        massSquared fields direction contract component

/-- At the base point this is literally the existing sector-metric matter
action data used beside Candidate A, with the same measure and masses. -/
@[simp] theorem programPMetricMatterActionCurve_zero_eq_actionData
    (measure : Measure (EffectiveQuotient period hPeriod))
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields measure) :
    programPMetricMatterActionCurve period hPeriod measure
        matterContract.massSquared fields direction 0 =
      globalIndependentMatterAction period hPeriod
        (independentMatterMetricActionData period hPeriod fields measure
          matterContract) fields := by
  simp only [programPMetricMatterActionCurve, independentFieldCurve_zero]
  rfl

end

end P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
end JanusFormal
