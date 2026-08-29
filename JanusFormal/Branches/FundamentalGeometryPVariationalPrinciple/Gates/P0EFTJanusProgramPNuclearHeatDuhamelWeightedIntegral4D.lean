import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D

/-!
# Weighted Duhamel integrals from a nuclear heat family

The nuclear Duhamel packet is naturally indexed by the subtype `HeatTime` of
strictly positive times, whereas the finite-part integrals are written on real
time regions.  Extend the scalar heat and Duhamel traces by zero outside
positive time.

For any real time, the extended heat trace remains differentiable in the family
parameter.  On a region carrying a logarithmic weight `w(t)` with
`w(t) * t = 1`, the weighted pointwise derivative reduces to the negative
extended Duhamel trace.  A single differentiation-under-the-integral theorem
then constructs the complete `DuhamelWeightedHeatTraceVariationData` interface.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

namespace NuclearHeatDuhamelTraceVariationData

/-- Scalar heat trace extended by zero to all real times. -/
def extendedHeatTrace
    (data : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (parameter time : Real) : Real :=
  if hTime : 0 < time then data.heatTrace parameter ⟨time, hTime⟩ else 0

/-- Scalar Duhamel trace extended by zero to all real times. -/
def extendedDuhamelTrace
    (data : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (parameter time : Real) : Real :=
  if hTime : 0 < time then data.duhamelTrace parameter ⟨time, hTime⟩ else 0

/-- Extended scalar heat derivative. -/
def extendedHeatTraceDerivative
    (data : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (parameter time : Real) : Real :=
  -time * extendedDuhamelTrace data parameter time

/-- Pointwise derivative of the extended scalar heat trace. -/
theorem extendedHeatTrace_hasDerivAt
    (data : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (parameter time : Real) :
    HasDerivAt (fun current => extendedHeatTrace data current time)
      (extendedHeatTraceDerivative data parameter time) parameter := by
  by_cases hTime : 0 < time
  · simpa [extendedHeatTrace, extendedHeatTraceDerivative,
      extendedDuhamelTrace, hTime] using
      data.heatTrace_hasDerivAt parameter ⟨time, hTime⟩
  · simp only [extendedHeatTrace, extendedHeatTraceDerivative,
      extendedDuhamelTrace, hTime, dite_false, mul_zero]
    exact hasDerivAt_const parameter 0

/-- The extended derivative is still `-t` times the extended Duhamel trace. -/
theorem extendedHeatTraceDerivative_eq
    (data : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (parameter time : Real) :
    extendedHeatTraceDerivative data parameter time =
      -time * extendedDuhamelTrace data parameter time :=
  rfl

end NuclearHeatDuhamelTraceVariationData

open NuclearHeatDuhamelTraceVariationData

/-- One weighted real-time region built from a nuclear heat Duhamel family. -/
structure NuclearHeatDuhamelWeightedIntegralData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (timeRegion : Set Real) where
  weight : Real → Real
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict timeRegion, weight time * time = 1
  hasDerivAt_integral : ∀ parameter,
    HasDerivAt
      (fun current =>
        ∫ time in timeRegion,
          weight time * extendedHeatTrace nuclear current time)
      (∫ time in timeRegion,
        weight time * extendedHeatTraceDerivative nuclear parameter time)
      parameter

namespace NuclearHeatDuhamelWeightedIntegralData

/-- Weighted heat integral interface. -/
def toWeightedHeatTraceVariation
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion) :
    WeightedHeatTraceIntegralVariationData timeRegion where
  weight := data.weight
  heatTrace := extendedHeatTrace nuclear
  heatTraceDerivative := extendedHeatTraceDerivative nuclear
  pointwise_hasDerivAt_heatTrace := by
    intro parameter
    filter_upwards [] with time
    exact extendedHeatTrace_hasDerivAt nuclear parameter time
  hasDerivAt_integral := data.hasDerivAt_integral

/-- Complete Duhamel-weighted integral interface. -/
def toDuhamelWeightedHeatTraceVariation
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion) :
    DuhamelWeightedHeatTraceVariationData timeRegion where
  weighted := data.toWeightedHeatTraceVariation
  duhamelTrace := extendedDuhamelTrace nuclear
  heatTraceDerivative_eq := by
    intro parameter
    filter_upwards [] with time
    exact extendedHeatTraceDerivative_eq nuclear parameter time
  weight_mul_time_eq_one := data.weight_mul_time_eq_one

/-- The weighted derivative integral is the negative Duhamel-trace integral. -/
theorem derivativeContribution_eq_neg_integral
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion)
    (parameter : Real) :
    data.toWeightedHeatTraceVariation.derivativeContribution parameter =
      -(∫ time in timeRegion,
        extendedDuhamelTrace nuclear parameter time) :=
  P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D.DuhamelWeightedHeatTraceVariationData.derivativeContribution_eq_neg_integral_duhamelTrace
    data.toDuhamelWeightedHeatTraceVariation parameter

/-- Public nuclear-to-weighted-Duhamel checkpoint. -/
theorem nuclear_heat_duhamel_weighted_integral_gate
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    (timeRegion : Set Real)
    (data : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion) :
    (∀ parameter time,
      HasDerivAt (fun current => extendedHeatTrace nuclear current time)
        (extendedHeatTraceDerivative nuclear parameter time) parameter) ∧
    (∀ parameter,
      data.toWeightedHeatTraceVariation.derivativeContribution parameter =
        -(∫ time in timeRegion,
          extendedDuhamelTrace nuclear parameter time)) ∧
    (∀ parameter,
      HasDerivAt data.toWeightedHeatTraceVariation.contribution
        (-(∫ time in timeRegion,
          extendedDuhamelTrace nuclear parameter time)) parameter) :=
  ⟨extendedHeatTrace_hasDerivAt nuclear,
    data.derivativeContribution_eq_neg_integral,
    P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D.DuhamelWeightedHeatTraceVariationData.hasDerivAt_contribution
      data.toDuhamelWeightedHeatTraceVariation⟩

end NuclearHeatDuhamelWeightedIntegralData

end
end P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
end JanusFormal
