import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPParametricDerivativeAEStronglyMeasurable4D

/-!
# Counterterm-subtracted short-time nuclear Duhamel integrals

This module differentiates the renormalized kernel

```text
w(t) (Tr K_a(t) - C_a(t)).
```

After the logarithmic identity `w(t)t = 1`, its Duhamel trace is

```text
Tr D_a(t) + w(t) partial_a C_a(t).
```
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open P0EFTJanusProgramPDominatedParametricRealIntegralVariation4D
open P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- A short-time heat trace after subtraction of a differentiable scalar UV
counterterm, with a quadratic uniform bound on its weighted derivative. -/
structure NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real) where
  weight : Real → Real
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff), weight time * time = 1
  counterterm : Real → Real → Real
  countertermDerivative : Real → Real → Real
  counterterm_hasDerivAt : ∀ parameter time,
    HasDerivAt (fun current => counterterm current time)
      (countertermDerivative parameter time) parameter
  parameterDomain : Real → Set Real
  parameterDomain_mem_nhds : ∀ parameter,
    parameterDomain parameter ∈ nhds parameter
  integrand_aeStronglyMeasurable : ∀ parameter,
    ∀ᶠ current in nhds parameter,
      AEStronglyMeasurable
        (fun time => weight time *
          (extendedHeatTrace nuclear current time - counterterm current time))
        (volume.restrict (Set.Ioo 0 cutoff))
  integrandMajorant : Real → Real → Real
  integrandMajorant_integrable : ∀ parameter,
    Integrable
      (integrandMajorant parameter)
      (volume.restrict (Set.Ioo 0 cutoff))
  integrand_norm_le : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff),
      ‖weight time *
        (extendedHeatTrace nuclear parameter time -
          counterterm parameter time)‖ ≤
        integrandMajorant parameter time
  scale : Real → Real
  derivative_norm_le : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioo 0 cutoff),
      ∀ current ∈ parameterDomain parameter,
        ‖weight time *
          (extendedHeatTraceDerivative nuclear current time -
            countertermDerivative current time)‖ ≤
          shortTimeQuadraticBound (scale parameter) time

namespace NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData

def subtractedHeatTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff)
    (parameter time : Real) : Real :=
  extendedHeatTrace nuclear parameter time - data.counterterm parameter time

def subtractedHeatTraceDerivative
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff)
    (parameter time : Real) : Real :=
  extendedHeatTraceDerivative nuclear parameter time -
    data.countertermDerivative parameter time

/-- The Duhamel trace corrected by the parameter variation of the UV
counterterm. -/
def renormalizedDuhamelTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff)
    (parameter time : Real) : Real :=
  extendedDuhamelTrace nuclear parameter time +
    data.weight time * data.countertermDerivative parameter time

/-- Pointwise differentiation of the weighted subtracted heat trace. -/
theorem weightedSubtractedHeatTrace_hasDerivAt
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff)
    (parameter time : Real) :
    HasDerivAt
      (fun current =>
        data.weight time * data.subtractedHeatTrace current time)
      (data.weight time * data.subtractedHeatTraceDerivative parameter time)
      parameter := by
  have hConstant :
      HasDerivAt (fun _ : Real => data.weight time) 0 parameter :=
    hasDerivAt_const parameter (data.weight time)
  have hSubtracted :=
    (extendedHeatTrace_hasDerivAt nuclear parameter time).sub
      (data.counterterm_hasDerivAt parameter time)
  simpa [subtractedHeatTrace, subtractedHeatTraceDerivative] using!
    hConstant.mul hSubtracted

/-- Local measurability of the subtracted kernels and their pointwise
derivative imply measurability of the derivative field. -/
theorem derivative_aeStronglyMeasurable
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff)
    (parameter : Real) :
    AEStronglyMeasurable
      (fun time => data.weight time *
        data.subtractedHeatTraceDerivative parameter time)
      (volume.restrict (Set.Ioo 0 cutoff)) :=
  P0EFTJanusProgramPParametricDerivativeAEStronglyMeasurable4D.derivative_aeStronglyMeasurable
      (volume.restrict (Set.Ioo 0 cutoff))
      (fun current time =>
        data.weight time * data.subtractedHeatTrace current time)
      (fun time =>
        data.weight time * data.subtractedHeatTraceDerivative parameter time)
      parameter (by
        simpa [subtractedHeatTrace] using
          data.integrand_aeStronglyMeasurable parameter)
      (Filter.Eventually.of_forall fun time =>
        data.weightedSubtractedHeatTrace_hasDerivAt parameter time)

/-- The short-time heat remainder is integrable once it is dominated by the
separate integrable value majorant. -/
theorem integrand_integrable
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff)
    (parameter : Real) :
    Integrable
      (fun time => data.weight time *
        data.subtractedHeatTrace parameter time)
      (volume.restrict (Set.Ioo 0 cutoff)) := by
  apply (data.integrandMajorant_integrable parameter).mono'
  · simpa [subtractedHeatTrace] using
      (data.integrand_aeStronglyMeasurable parameter).self_of_nhds
  · simpa [subtractedHeatTrace] using data.integrand_norm_le parameter

/-- The subtracted weighted kernel satisfies the generic dominated
parametric-integral contract. -/
def toDominatedParametricIntegral
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff) :
    DominatedParametricRealIntegralVariationData (Set.Ioo 0 cutoff) where
  integrand := fun parameter time =>
    data.weight time * data.subtractedHeatTrace parameter time
  derivative := fun parameter time =>
    data.weight time * data.subtractedHeatTraceDerivative parameter time
  parameterDomain := data.parameterDomain
  parameterDomain_mem_nhds := data.parameterDomain_mem_nhds
  integrand_aeStronglyMeasurable := data.integrand_aeStronglyMeasurable
  integrand_integrable := data.integrand_integrable
  derivative_aeStronglyMeasurable := data.derivative_aeStronglyMeasurable
  bound := fun parameter => shortTimeQuadraticBound (data.scale parameter)
  derivative_norm_le := data.derivative_norm_le
  bound_integrable := fun parameter =>
    integrableOn_shortTimeQuadraticBound (data.scale parameter) cutoff
  pointwise_hasDerivAt := by
    intro parameter
    filter_upwards [] with time
    intro current hCurrent
    exact data.weightedSubtractedHeatTrace_hasDerivAt current time

/-- Weighted heat-variation interface for the subtracted heat trace. -/
def toWeightedHeatTraceVariation
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff) :
    WeightedHeatTraceIntegralVariationData (Set.Ioo 0 cutoff) where
  weight := data.weight
  heatTrace := data.subtractedHeatTrace
  heatTraceDerivative := data.subtractedHeatTraceDerivative
  pointwise_hasDerivAt_heatTrace := by
    intro parameter
    filter_upwards [] with time
    exact (extendedHeatTrace_hasDerivAt nuclear parameter time).sub
      (data.counterterm_hasDerivAt parameter time)
  hasDerivAt_integral := by
    intro parameter
    simpa [DominatedParametricRealIntegralVariationData.contribution,
      DominatedParametricRealIntegralVariationData.derivativeContribution,
      toDominatedParametricIntegral] using!
      data.toDominatedParametricIntegral.hasDerivAt_contribution parameter

/-- Complete Duhamel interface after UV counterterm subtraction. -/
def toDuhamelWeightedHeatTraceVariation
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff) :
    DuhamelWeightedHeatTraceVariationData (Set.Ioo 0 cutoff) where
  weighted := data.toWeightedHeatTraceVariation
  duhamelTrace := data.renormalizedDuhamelTrace
  heatTraceDerivative_eq := by
    intro parameter
    filter_upwards [data.weight_mul_time_eq_one] with time hWeight
    change
      extendedHeatTraceDerivative nuclear parameter time -
          data.countertermDerivative parameter time =
        -time * (extendedDuhamelTrace nuclear parameter time +
          data.weight time * data.countertermDerivative parameter time)
    rw [extendedHeatTraceDerivative_eq]
    calc
      -time * extendedDuhamelTrace nuclear parameter time -
          data.countertermDerivative parameter time =
        -time * extendedDuhamelTrace nuclear parameter time -
          (data.weight time * time) *
            data.countertermDerivative parameter time := by simp [hWeight]
      _ = -time * (extendedDuhamelTrace nuclear parameter time +
          data.weight time * data.countertermDerivative parameter time) := by
        ring
  weight_mul_time_eq_one := data.weight_mul_time_eq_one

theorem derivative_integrable
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff)
    (parameter : Real) :
    Integrable
      (fun time => data.weight time *
        data.subtractedHeatTraceDerivative parameter time)
      (volume.restrict (Set.Ioo 0 cutoff)) :=
  data.toDominatedParametricIntegral.derivative_integrable parameter

/-- The renormalized Duhamel trace is integrable on the short-time region. -/
theorem renormalizedDuhamelTrace_integrable
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff)
    (parameter : Real) :
    Integrable (data.renormalizedDuhamelTrace parameter)
      (volume.restrict (Set.Ioo 0 cutoff)) := by
  apply (data.derivative_integrable parameter).neg.congr
  filter_upwards [
    data.toDuhamelWeightedHeatTraceVariation.derivativeKernel_eq_neg_duhamelTrace
      parameter] with time hDerivative
  change -(data.weight time *
      data.subtractedHeatTraceDerivative parameter time) =
    data.renormalizedDuhamelTrace parameter time
  change data.weight time * data.subtractedHeatTraceDerivative parameter time =
    -data.renormalizedDuhamelTrace parameter time at hDerivative
  rw [hDerivative]
  ring

theorem hasDerivAt_integral
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {cutoff : Real}
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        ∫ time in Set.Ioo 0 cutoff,
          data.weight time * data.subtractedHeatTrace current time)
      (-(∫ time in Set.Ioo 0 cutoff,
        data.renormalizedDuhamelTrace parameter time)) parameter := by
  change HasDerivAt
    data.toDuhamelWeightedHeatTraceVariation.weighted.contribution
    (-(∫ time in Set.Ioo 0 cutoff,
      data.toDuhamelWeightedHeatTraceVariation.duhamelTrace parameter time))
    parameter
  exact data.toDuhamelWeightedHeatTraceVariation.hasDerivAt_contribution parameter

/-- Public counterterm-subtracted short-time Duhamel checkpoint. -/
theorem nuclear_heat_duhamel_counterterm_subtracted_short_time_quadratic_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (cutoff : Real)
    (data : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear cutoff) :
    (∀ parameter, Integrable
      (fun time => data.weight time *
        data.subtractedHeatTrace parameter time)
      (volume.restrict (Set.Ioo 0 cutoff))) ∧
    (∀ parameter, Integrable
      (fun time => data.weight time *
        data.subtractedHeatTraceDerivative parameter time)
      (volume.restrict (Set.Ioo 0 cutoff))) ∧
    (∀ parameter, Integrable
      (data.renormalizedDuhamelTrace parameter)
      (volume.restrict (Set.Ioo 0 cutoff))) ∧
    (∀ parameter, HasDerivAt
      (fun current =>
        ∫ time in Set.Ioo 0 cutoff,
          data.weight time * data.subtractedHeatTrace current time)
      (-(∫ time in Set.Ioo 0 cutoff,
        data.renormalizedDuhamelTrace parameter time)) parameter) :=
  ⟨data.integrand_integrable, data.derivative_integrable,
    data.renormalizedDuhamelTrace_integrable,
    data.hasDerivAt_integral⟩

end NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData

end
end P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
end JanusFormal
