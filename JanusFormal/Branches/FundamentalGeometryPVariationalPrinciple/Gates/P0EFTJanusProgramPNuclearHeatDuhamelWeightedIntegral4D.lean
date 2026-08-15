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

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

namespace NuclearHeatDuhamelTraceVariationData

/-- Scalar heat trace extended by zero to all real times. -/
def extendedHeatTrace
    (data : NuclearHeatDuhamelTraceVariationData (E := E))
    (parameter time : Real) : Real :=
  if hTime : 0 < time then data.heatTrace parameter ⟨time, hTime⟩ else 0

/-- Scalar Duhamel trace extended by zero to all real times. -/
def extendedDuhamelTrace
    (data : NuclearHeatDuhamelTraceVariationData (E := E))
    (parameter time : Real) : Real :=
  if hTime : 0 < time then data.duhamelTrace parameter ⟨time, hTime⟩ else 0

/-- Extended scalar heat derivative. -/
def extendedHeatTraceDerivative
    (data : NuclearHeatDuhamelTraceVariationData (E := E))
    (parameter time : Real) : Real :=
  -time * data.extendedDuhamelTrace parameter time

/-- Pointwise derivative of the extended scalar heat trace. -/
theorem extendedHeatTrace_hasDerivAt
    (data : NuclearHeatDuhamelTraceVariationData (E := E))
    (parameter time : Real) :
    HasDerivAt (fun current => data.extendedHeatTrace current time)
      (data.extendedHeatTraceDerivative parameter time) parameter := by
  by_cases hTime : 0 < time
  · simpa [extendedHeatTrace, extendedHeatTraceDerivative,
      extendedDuhamelTrace, hTime] using
      data.heatTrace_hasDerivAt parameter ⟨time, hTime⟩
  · simp [extendedHeatTrace, extendedHeatTraceDerivative,
      extendedDuhamelTrace, hTime]

/-- The extended derivative is still `-t` times the extended Duhamel trace. -/
theorem extendedHeatTraceDerivative_eq
    (data : NuclearHeatDuhamelTraceVariationData (E := E))
    (parameter time : Real) :
    data.extendedHeatTraceDerivative parameter time =
      -time * data.extendedDuhamelTrace parameter time :=
  rfl

end NuclearHeatDuhamelTraceVariationData

/-- One weighted real-time region built from a nuclear heat Duhamel family. -/
structure NuclearHeatDuhamelWeightedIntegralData
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (timeRegion : Set Real) where
  weight : Real → Real
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict timeRegion, weight time * time = 1
  hasDerivAt_integral : ∀ parameter,
    HasDerivAt
      (fun current =>
        ∫ time in timeRegion,
          weight time * nuclear.extendedHeatTrace current time)
      (∫ time in timeRegion,
        weight time * nuclear.extendedHeatTraceDerivative parameter time)
      parameter

namespace NuclearHeatDuhamelWeightedIntegralData

/-- Weighted heat integral interface. -/
def toWeightedHeatTraceVariation
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion) :
    WeightedHeatTraceIntegralVariationData timeRegion where
  weight := data.weight
  heatTrace := nuclear.extendedHeatTrace
  heatTraceDerivative := nuclear.extendedHeatTraceDerivative
  pointwise_hasDerivAt_heatTrace := by
    intro parameter
    filter_upwards [] with time
    exact nuclear.extendedHeatTrace_hasDerivAt parameter time
  hasDerivAt_integral := data.hasDerivAt_integral

/-- Complete Duhamel-weighted integral interface. -/
def toDuhamelWeightedHeatTraceVariation
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion) :
    DuhamelWeightedHeatTraceVariationData timeRegion where
  weighted := data.toWeightedHeatTraceVariation
  duhamelTrace := nuclear.extendedDuhamelTrace
  heatTraceDerivative_eq := by
    intro parameter
    filter_upwards [] with time
    exact nuclear.extendedHeatTraceDerivative_eq parameter time
  weight_mul_time_eq_one := data.weight_mul_time_eq_one

/-- The weighted derivative integral is the negative Duhamel-trace integral. -/
theorem derivativeContribution_eq_neg_integral
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {timeRegion : Set Real}
    (data : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion)
    (parameter : Real) :
    data.toWeightedHeatTraceVariation.derivativeContribution parameter =
      -(∫ time in timeRegion,
        nuclear.extendedDuhamelTrace parameter time) :=
  data.toDuhamelWeightedHeatTraceVariation.
    derivativeContribution_eq_neg_integral_duhamelTrace parameter

/-- Public nuclear-to-weighted-Duhamel checkpoint. -/
theorem nuclear_heat_duhamel_weighted_integral_gate
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (timeRegion : Set Real)
    (data : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion) :
    (∀ parameter time,
      HasDerivAt (fun current => nuclear.extendedHeatTrace current time)
        (nuclear.extendedHeatTraceDerivative parameter time) parameter) ∧
    (∀ parameter,
      data.toWeightedHeatTraceVariation.derivativeContribution parameter =
        -(∫ time in timeRegion,
          nuclear.extendedDuhamelTrace parameter time)) ∧
    (∀ parameter,
      HasDerivAt data.toWeightedHeatTraceVariation.contribution
        (-(∫ time in timeRegion,
          nuclear.extendedDuhamelTrace parameter time)) parameter) :=
  ⟨nuclear.extendedHeatTrace_hasDerivAt,
    data.derivativeContribution_eq_neg_integral,
    data.toDuhamelWeightedHeatTraceVariation.hasDerivAt_integral⟩

end NuclearHeatDuhamelWeightedIntegralData

end
end P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
end JanusFormal
