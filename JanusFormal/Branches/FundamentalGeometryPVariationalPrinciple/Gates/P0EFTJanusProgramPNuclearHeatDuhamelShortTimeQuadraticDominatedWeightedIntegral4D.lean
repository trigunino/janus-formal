import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D

/-!
# Short-time nuclear Duhamel domination from a quadratic remainder

On `(0,ε)`, the envelope `|C| t²` is integrable.  This module converts a
quadratic renormalized heat-remainder estimate into the dominated weighted
integral packet, so `bound_integrable` is no longer an independent input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

def shortTimeQuadraticBound (scale time : Real) : Real :=
  |scale| * time ^ 2

theorem integrableOn_shortTimeQuadraticBound
    (scale cutoff : Real) :
    IntegrableOn (shortTimeQuadraticBound scale) (Set.Ioo 0 cutoff) := by
  apply IntegrableOn.mono_set
    ((show Continuous (shortTimeQuadraticBound scale) by
      unfold shortTimeQuadraticBound
      fun_prop).integrableOn_Icc)
  exact Set.Ioo_subset_Icc_self

structure NuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegralData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) where
  weight : Real → Real
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff), weight time * time = 1
  parameterDomain : Real → Set Real
  parameterDomain_mem_nhds : ∀ parameter,
    parameterDomain parameter ∈ 𝓝 parameter
  integrand_aeStronglyMeasurable : ∀ parameter,
    ∀ᶠ current in 𝓝 parameter,
      AEStronglyMeasurable
        (fun time => weight time * extendedHeatTrace nuclear current time)
        (volume.restrict (Set.Ioo 0 cutoff))
  integrand_integrable : ∀ parameter,
    Integrable
      (fun time => weight time * extendedHeatTrace nuclear parameter time)
      (volume.restrict (Set.Ioo 0 cutoff))
  derivative_aeStronglyMeasurable : ∀ parameter,
    AEStronglyMeasurable
      (fun time => weight time * extendedHeatTraceDerivative nuclear parameter time)
      (volume.restrict (Set.Ioo 0 cutoff))
  scale : Real → Real
  derivative_norm_le : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff),
      ∀ current ∈ parameterDomain parameter,
        ‖weight time * extendedHeatTraceDerivative nuclear current time‖ ≤
          shortTimeQuadraticBound (scale parameter) time

namespace NuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegralData

theorem bound_integrable
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegralData
      nuclear cutoff)
    (parameter : Real) :
    Integrable
      (shortTimeQuadraticBound (data.scale parameter))
      (volume.restrict (Set.Ioo 0 cutoff)) :=
  integrableOn_shortTimeQuadraticBound (data.scale parameter) cutoff

def toDominatedWeightedIntegral
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegralData
      nuclear cutoff) :
    NuclearHeatDuhamelDominatedWeightedIntegralData nuclear
      (Set.Ioo 0 cutoff) where
  weight := data.weight
  weight_mul_time_eq_one := data.weight_mul_time_eq_one
  parameterDomain := data.parameterDomain
  parameterDomain_mem_nhds := data.parameterDomain_mem_nhds
  integrand_aeStronglyMeasurable := data.integrand_aeStronglyMeasurable
  integrand_integrable := data.integrand_integrable
  derivative_aeStronglyMeasurable := data.derivative_aeStronglyMeasurable
  bound := fun parameter => shortTimeQuadraticBound (data.scale parameter)
  derivative_norm_le := data.derivative_norm_le
  bound_integrable := data.bound_integrable

theorem hasDerivAt_integral
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegralData
      nuclear cutoff)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        ∫ time in Set.Ioo 0 cutoff,
          data.weight time * extendedHeatTrace nuclear current time)
      (-∫ time in Set.Ioo 0 cutoff,
        extendedDuhamelTrace nuclear parameter time) parameter :=
  P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D.DuhamelWeightedHeatTraceVariationData.hasDerivAt_contribution
    data.toDominatedWeightedIntegral.toWeightedIntegral.toDuhamelWeightedHeatTraceVariation
    parameter

/-- Public short-time quadratic domination checkpoint. -/
theorem nuclear_heat_duhamel_short_time_quadratic_dominated_weighted_integral_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real)
    (data : NuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegralData
      nuclear cutoff) :
    (∀ parameter,
      Integrable
        (shortTimeQuadraticBound (data.scale parameter))
        (volume.restrict (Set.Ioo 0 cutoff))) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          ∫ time in Set.Ioo 0 cutoff,
            data.weight time * extendedHeatTrace nuclear current time)
        (-∫ time in Set.Ioo 0 cutoff,
          extendedDuhamelTrace nuclear parameter time) parameter) :=
  ⟨data.bound_integrable, data.hasDerivAt_integral⟩

end NuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegralData

end
end P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D
end JanusFormal
