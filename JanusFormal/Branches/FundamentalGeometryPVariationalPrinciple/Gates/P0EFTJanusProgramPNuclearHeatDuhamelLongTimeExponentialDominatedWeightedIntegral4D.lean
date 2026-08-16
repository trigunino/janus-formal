import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D

/-!
# Long-time dominated heat variation from an exponential estimate

On `(T₀, +∞)`, a bound `C exp (-c t)` with `0 < c` is integrable.  This
module uses that fact to generate the `bound_integrable` field of the dominated
nuclear-Duhamel weighted integral.  The positive rate remains a genuine
spectral input; it is not inferred from the two-sided H14 norm gap alone.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegral4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

structure NuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegralData
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (start : Real) where
  weight : Real → Real
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict (Set.Ioi start), weight time * time = 1
  parameterDomain : Real → Set Real
  parameterDomain_mem_nhds : ∀ parameter,
    parameterDomain parameter ∈ 𝓝 parameter
  integrand_aeStronglyMeasurable : ∀ parameter,
    ∀ᶠ current in 𝓝 parameter,
      AEStronglyMeasurable
        (fun time => weight time * nuclear.extendedHeatTrace current time)
        (volume.restrict (Set.Ioi start))
  integrand_integrable : ∀ parameter,
    Integrable
      (fun time => weight time * nuclear.extendedHeatTrace parameter time)
      (volume.restrict (Set.Ioi start))
  derivative_aeStronglyMeasurable : ∀ parameter,
    AEStronglyMeasurable
      (fun time =>
        weight time * nuclear.extendedHeatTraceDerivative parameter time)
      (volume.restrict (Set.Ioi start))
  scale : Real → Real
  rate : Real → Real
  rate_pos : ∀ parameter, 0 < rate parameter
  derivative_norm_le : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioi start),
      ∀ current ∈ parameterDomain parameter,
        ‖weight time * nuclear.extendedHeatTraceDerivative current time‖ ≤
          longTimeExponentialBound (scale parameter) (rate parameter) time

namespace NuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegralData

theorem bound_integrable
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {start : Real}
    (data : NuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegralData
      nuclear start)
    (parameter : Real) :
    Integrable
      (longTimeExponentialBound (data.scale parameter) (data.rate parameter))
      (volume.restrict (Set.Ioi start)) :=
  integrableOn_longTimeExponentialBound (data.scale parameter)
    (data.rate_pos parameter) start

def toDominatedWeightedIntegral
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {start : Real}
    (data : NuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegralData
      nuclear start) :
    NuclearHeatDuhamelDominatedWeightedIntegralData nuclear (Set.Ioi start) where
  weight := data.weight
  weight_mul_time_eq_one := data.weight_mul_time_eq_one
  parameterDomain := data.parameterDomain
  parameterDomain_mem_nhds := data.parameterDomain_mem_nhds
  integrand_aeStronglyMeasurable := data.integrand_aeStronglyMeasurable
  integrand_integrable := data.integrand_integrable
  derivative_aeStronglyMeasurable := data.derivative_aeStronglyMeasurable
  bound := fun parameter =>
    longTimeExponentialBound (data.scale parameter) (data.rate parameter)
  derivative_norm_le := data.derivative_norm_le
  bound_integrable := data.bound_integrable

theorem hasDerivAt_integral
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {start : Real}
    (data : NuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegralData
      nuclear start)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        ∫ time in Set.Ioi start,
          data.weight time * nuclear.extendedHeatTrace current time)
      (-(∫ time in Set.Ioi start,
        nuclear.extendedDuhamelTrace parameter time)) parameter :=
  data.toDominatedWeightedIntegral.toWeightedIntegral.
    toDuhamelWeightedHeatTraceVariation.hasDerivAt_contribution parameter

/-- Public long-time exponential domination checkpoint. -/
theorem nuclear_heat_duhamel_long_time_exponential_dominated_weighted_integral_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (start : Real)
    (data : NuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegralData
      nuclear start) :
    (∀ parameter,
      Integrable
        (longTimeExponentialBound (data.scale parameter)
          (data.rate parameter))
        (volume.restrict (Set.Ioi start))) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          ∫ time in Set.Ioi start,
            data.weight time * nuclear.extendedHeatTrace current time)
        (-(∫ time in Set.Ioi start,
          nuclear.extendedDuhamelTrace parameter time)) parameter) :=
  ⟨data.bound_integrable, data.hasDerivAt_integral⟩

end NuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegralData

end
end P0EFTJanusProgramPNuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegral4D
end JanusFormal
