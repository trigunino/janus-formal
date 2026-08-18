import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D

/-!
# Sign reversal for weighted Duhamel heat-trace variations

The simultaneous sign reversal of the heat trace, its derivative, and the
Duhamel trace preserves the Duhamel relation.  Its contribution is the
negative original contribution, while its derivative is the positive integral
of the original Duhamel trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

namespace DuhamelWeightedHeatTraceVariationData

/-- Simultaneously reverse the heat-trace and Duhamel signs. -/
def negated
    {timeRegion : Set Real}
    (data : DuhamelWeightedHeatTraceVariationData timeRegion) :
    DuhamelWeightedHeatTraceVariationData timeRegion where
  weighted :=
    { weight := data.weighted.weight
      heatTrace := fun parameter time => -data.weighted.heatTrace parameter time
      heatTraceDerivative := fun parameter time =>
        -data.weighted.heatTraceDerivative parameter time
      pointwise_hasDerivAt_heatTrace := fun parameter => by
        filter_upwards [data.weighted.pointwise_hasDerivAt_heatTrace parameter]
          with time hTime
        exact hTime.neg
      hasDerivAt_integral := fun parameter => by
        convert (data.weighted.hasDerivAt_integral parameter).neg using 1
        · apply AddCommGroup.ext
          funext first second
          rfl
        · apply Module.ext
          funext scalar value
          rfl
        · funext current
          simp only [mul_neg, integral_neg, Pi.neg_apply]
        · simp only [mul_neg, integral_neg] }
  duhamelTrace := fun parameter time => -data.duhamelTrace parameter time
  heatTraceDerivative_eq := fun parameter => by
    filter_upwards [data.heatTraceDerivative_eq parameter] with time hTime
    rw [hTime]
    ring
  weight_mul_time_eq_one := data.weight_mul_time_eq_one

/-- The sign-reversed weighted contribution is the negative original one. -/
theorem negated_contribution_eq_neg_contribution
    {timeRegion : Set Real}
    (data : DuhamelWeightedHeatTraceVariationData timeRegion)
    (parameter : Real) :
    data.negated.weighted.contribution parameter =
      -data.weighted.contribution parameter := by
  simp only [WeightedHeatTraceIntegralVariationData.contribution, negated,
    mul_neg, integral_neg]

/-- The sign-reversed Duhamel integral is the negative original integral. -/
theorem integral_negated_duhamelTrace_eq_neg_integral
    {timeRegion : Set Real}
    (data : DuhamelWeightedHeatTraceVariationData timeRegion)
    (parameter : Real) :
    (∫ time in timeRegion, data.negated.duhamelTrace parameter time) =
      -(∫ time in timeRegion, data.duhamelTrace parameter time) := by
  simp only [negated, integral_neg]

/-- Its differentiated weighted contribution is the positive original
Duhamel integral. -/
theorem negated_derivativeContribution_eq_integral_duhamelTrace
    {timeRegion : Set Real}
    (data : DuhamelWeightedHeatTraceVariationData timeRegion)
    (parameter : Real) :
    data.negated.weighted.derivativeContribution parameter =
      ∫ time in timeRegion, data.duhamelTrace parameter time := by
  rw [data.negated.derivativeContribution_eq_neg_integral_duhamelTrace]
  simp only [negated, integral_neg, neg_neg]

/-- The derivative of the sign-reversed contribution has the expected
positive Duhamel sign. -/
theorem negated_hasDerivAt_contribution
    {timeRegion : Set Real}
    (data : DuhamelWeightedHeatTraceVariationData timeRegion)
    (parameter : Real) :
    HasDerivAt data.negated.weighted.contribution
      (∫ time in timeRegion, data.duhamelTrace parameter time)
      parameter := by
  rw [← data.negated_derivativeContribution_eq_integral_duhamelTrace parameter]
  exact data.negated.weighted.hasDerivAt_integral parameter

/-- Public checkpoint for the sign-reversed Duhamel convention. -/
theorem negated_duhamel_weighted_heat_trace_variation_gate
    (timeRegion : Set Real)
    (data : DuhamelWeightedHeatTraceVariationData timeRegion) :
    (∀ parameter,
      data.negated.weighted.contribution parameter =
        -data.weighted.contribution parameter) ∧
    (∀ parameter,
      data.negated.weighted.derivativeContribution parameter =
        ∫ time in timeRegion, data.duhamelTrace parameter time) ∧
    (∀ parameter,
      HasDerivAt data.negated.weighted.contribution
        (∫ time in timeRegion, data.duhamelTrace parameter time)
        parameter) :=
  ⟨data.negated_contribution_eq_neg_contribution,
    data.negated_derivativeContribution_eq_integral_duhamelTrace,
    data.negated_hasDerivAt_contribution⟩

end DuhamelWeightedHeatTraceVariationData

end
end P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D
end JanusFormal
