import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Dominated differentiation for real set integrals

Several heat-family frontends currently accept a completed theorem saying that
a parameter derivative may be moved through a real-time integral.  This module
packages the actual hypotheses of Mathlib's dominated parametric-integral
theorem instead:

* a common parameter neighborhood;
* almost-everywhere strong measurability near the base parameter;
* integrability at the base parameter;
* a measurable derivative field;
* one integrable majorant, uniform on that neighborhood;
* the pointwise derivative identity almost everywhere.

The derivative of the set integral is then a theorem.  The majorant may depend
on the base parameter, but not on the moving parameter inside its selected
neighborhood.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDominatedParametricRealIntegralVariation4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- A real parameter integral together with the complete local dominated
-differentiation contract at every parameter. -/
structure DominatedParametricRealIntegralVariationData
    (timeRegion : Set Real) where
  integrand : Real → Real → Real
  derivative : Real → Real → Real
  parameterDomain : Real → Set Real
  parameterDomain_mem_nhds : ∀ parameter,
    parameterDomain parameter ∈ 𝓝 parameter
  integrand_aeStronglyMeasurable : ∀ parameter,
    ∀ᶠ current in 𝓝 parameter,
      AEStronglyMeasurable (integrand current)
        (volume.restrict timeRegion)
  integrand_integrable : ∀ parameter,
    Integrable (integrand parameter) (volume.restrict timeRegion)
  derivative_aeStronglyMeasurable : ∀ parameter,
    AEStronglyMeasurable (derivative parameter)
      (volume.restrict timeRegion)
  bound : Real → Real → Real
  derivative_norm_le : ∀ parameter,
    ∀ᵐ time ∂volume.restrict timeRegion,
      ∀ current ∈ parameterDomain parameter,
        ‖derivative current time‖ ≤ bound parameter time
  bound_integrable : ∀ parameter,
    Integrable (bound parameter) (volume.restrict timeRegion)
  pointwise_hasDerivAt : ∀ parameter,
    ∀ᵐ time ∂volume.restrict timeRegion,
      ∀ current ∈ parameterDomain parameter,
        HasDerivAt (fun moving => integrand moving time)
          (derivative current time) current

namespace DominatedParametricRealIntegralVariationData

/-- The parameter-dependent set integral. -/
def contribution
    {timeRegion : Set Real}
    (data : DominatedParametricRealIntegralVariationData timeRegion)
    (parameter : Real) : Real :=
  ∫ time in timeRegion, data.integrand parameter time

/-- The integral of the pointwise parameter derivative. -/
def derivativeContribution
    {timeRegion : Set Real}
    (data : DominatedParametricRealIntegralVariationData timeRegion)
    (parameter : Real) : Real :=
  ∫ time in timeRegion, data.derivative parameter time

/-- The derivative passes through the set integral by dominated
differentiation. -/
theorem hasDerivAt_contribution
    {timeRegion : Set Real}
    (data : DominatedParametricRealIntegralVariationData timeRegion)
    (parameter : Real) :
    HasDerivAt data.contribution
      (data.derivativeContribution parameter) parameter := by
  have hIntegral :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict timeRegion)
      (F := data.integrand)
      (F' := data.derivative)
      (x₀ := parameter)
      (s := data.parameterDomain parameter)
      (bound := data.bound parameter)
      (data.parameterDomain_mem_nhds parameter)
      (data.integrand_aeStronglyMeasurable parameter)
      (data.integrand_integrable parameter)
      (data.derivative_aeStronglyMeasurable parameter)
      (data.derivative_norm_le parameter)
      (data.bound_integrable parameter)
      (data.pointwise_hasDerivAt parameter)
  simpa [contribution, derivativeContribution] using! hIntegral.2

/-- The derivative field is integrable at every parameter. -/
theorem derivative_integrable
    {timeRegion : Set Real}
    (data : DominatedParametricRealIntegralVariationData timeRegion)
    (parameter : Real) :
    Integrable (data.derivative parameter) (volume.restrict timeRegion) := by
  have hIntegral :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict timeRegion)
      (F := data.integrand)
      (F' := data.derivative)
      (x₀ := parameter)
      (s := data.parameterDomain parameter)
      (bound := data.bound parameter)
      (data.parameterDomain_mem_nhds parameter)
      (data.integrand_aeStronglyMeasurable parameter)
      (data.integrand_integrable parameter)
      (data.derivative_aeStronglyMeasurable parameter)
      (data.derivative_norm_le parameter)
      (data.bound_integrable parameter)
      (data.pointwise_hasDerivAt parameter)
  exact hIntegral.1

/-- Public dominated set-integral checkpoint. -/
theorem dominated_parametric_real_integral_variation_gate
    (timeRegion : Set Real)
    (data : DominatedParametricRealIntegralVariationData timeRegion) :
    (∀ parameter,
      Integrable (data.derivative parameter)
        (volume.restrict timeRegion)) ∧
    (∀ parameter,
      HasDerivAt data.contribution
        (data.derivativeContribution parameter) parameter) :=
  ⟨data.derivative_integrable, data.hasDerivAt_contribution⟩

end DominatedParametricRealIntegralVariationData

end
end P0EFTJanusProgramPDominatedParametricRealIntegralVariation4D
end JanusFormal
