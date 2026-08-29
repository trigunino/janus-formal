import Mathlib.Analysis.Calculus.Deriv.Mul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDominatedParametricRealIntegralVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D

/-!
# Dominated weighted integrals for nuclear Duhamel heat families

`NuclearHeatDuhamelWeightedIntegralData` previously accepted the completed
statement that differentiation commutes with the weighted time integral.  This
module constructs that packet from the measurable and integrable domination
estimates consumed by Mathlib.

For the weighted integrand

```text
F(a,t) = w(t) Tr K_a(t),
```

the pointwise derivative is generated from the nuclear heat trace theorem:

```text
partial_a F(a,t)
  = w(t) * (-t) * Tr D_a(t).
```

When `w(t)t = 1` almost everywhere, the existing Duhamel layer then reduces the
integrated derivative to `- integral Tr D_a(t)`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open P0EFTJanusProgramPDominatedParametricRealIntegralVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Local dominated-differentiation data for one logarithmically weighted heat
integral. -/
structure NuclearHeatDuhamelDominatedWeightedIntegralData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (timeRegion : Set Real) where
  weight : Real → Real
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict timeRegion, weight time * time = 1
  parameterDomain : Real → Set Real
  parameterDomain_mem_nhds : ∀ parameter,
    parameterDomain parameter ∈ 𝓝 parameter
  integrand_aeStronglyMeasurable : ∀ parameter,
    ∀ᶠ current in 𝓝 parameter,
      AEStronglyMeasurable
        (fun time => weight time * extendedHeatTrace nuclear current time)
        (volume.restrict timeRegion)
  integrand_integrable : ∀ parameter,
    Integrable
      (fun time => weight time * extendedHeatTrace nuclear parameter time)
      (volume.restrict timeRegion)
  derivative_aeStronglyMeasurable : ∀ parameter,
    AEStronglyMeasurable
      (fun time =>
        weight time * extendedHeatTraceDerivative nuclear parameter time)
      (volume.restrict timeRegion)
  bound : Real → Real → Real
  derivative_norm_le : ∀ parameter,
    ∀ᵐ time ∂volume.restrict timeRegion,
      ∀ current ∈ parameterDomain parameter,
        ‖weight time * extendedHeatTraceDerivative nuclear current time‖ ≤
          bound parameter time
  bound_integrable : ∀ parameter,
    Integrable (bound parameter) (volume.restrict timeRegion)

namespace NuclearHeatDuhamelDominatedWeightedIntegralData

/-- The weighted heat integrand and its derivative satisfy the generic
dominated parametric-integral packet. -/
def toDominatedParametricIntegral
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear timeRegion) :
    DominatedParametricRealIntegralVariationData timeRegion where
  integrand := fun parameter time =>
    data.weight time * extendedHeatTrace nuclear parameter time
  derivative := fun parameter time =>
    data.weight time * extendedHeatTraceDerivative nuclear parameter time
  parameterDomain := data.parameterDomain
  parameterDomain_mem_nhds := data.parameterDomain_mem_nhds
  integrand_aeStronglyMeasurable := data.integrand_aeStronglyMeasurable
  integrand_integrable := data.integrand_integrable
  derivative_aeStronglyMeasurable := data.derivative_aeStronglyMeasurable
  bound := data.bound
  derivative_norm_le := data.derivative_norm_le
  bound_integrable := data.bound_integrable
  pointwise_hasDerivAt := by
    intro parameter
    filter_upwards [] with time
    intro current hCurrent
    have hConstant :
        HasDerivAt (fun _ : Real => data.weight time) 0 current :=
      hasDerivAt_const current (data.weight time)
    have hHeat := extendedHeatTrace_hasDerivAt nuclear current time
    simpa using! hConstant.mul hHeat

/-- Construct the original weighted Duhamel interface from the dominated
estimates. -/
def toWeightedIntegral
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear timeRegion) :
    NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion where
  weight := data.weight
  weight_mul_time_eq_one := data.weight_mul_time_eq_one
  hasDerivAt_integral := by
    intro parameter
    simpa [DominatedParametricRealIntegralVariationData.contribution,
      DominatedParametricRealIntegralVariationData.derivativeContribution,
      toDominatedParametricIntegral]
      using! data.toDominatedParametricIntegral.hasDerivAt_contribution parameter

/-- The weighted integral derivative is no longer an input. -/
theorem hasDerivAt_integral
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear timeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        ∫ time in timeRegion,
          data.weight time * extendedHeatTrace nuclear current time)
      (∫ time in timeRegion,
        data.weight time *
          extendedHeatTraceDerivative nuclear parameter time)
      parameter :=
  data.toWeightedIntegral.hasDerivAt_integral parameter

/-- The logarithmic weight cancels the Duhamel time factor after dominated
differentiation. -/
theorem derivativeContribution_eq_neg_integral
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear timeRegion)
    (parameter : Real) :
    data.toWeightedIntegral.toWeightedHeatTraceVariation.derivativeContribution parameter =
      -(∫ time in timeRegion,
        extendedDuhamelTrace nuclear parameter time) :=
  data.toWeightedIntegral.derivativeContribution_eq_neg_integral parameter

/-- Public dominated nuclear-Duhamel integral checkpoint. -/
theorem nuclear_heat_duhamel_dominated_weighted_integral_gate
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (timeRegion : Set Real)
    (data : NuclearHeatDuhamelDominatedWeightedIntegralData nuclear timeRegion) :
    (∀ parameter,
      Integrable
        (fun time =>
          data.weight time *
            extendedHeatTraceDerivative nuclear parameter time)
        (volume.restrict timeRegion)) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          ∫ time in timeRegion,
            data.weight time * extendedHeatTrace nuclear current time)
        (-(∫ time in timeRegion,
          extendedDuhamelTrace nuclear parameter time)) parameter) := by
  constructor
  · intro parameter
    exact data.toDominatedParametricIntegral.derivative_integrable parameter
  · intro parameter
    rw [← data.derivativeContribution_eq_neg_integral parameter]
    exact data.hasDerivAt_integral parameter

end NuclearHeatDuhamelDominatedWeightedIntegralData

end
end P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D
end JanusFormal
