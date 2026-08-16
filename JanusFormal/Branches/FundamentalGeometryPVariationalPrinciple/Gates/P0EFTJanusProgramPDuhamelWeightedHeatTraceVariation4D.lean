import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

/-!
# Duhamel reduction of weighted heat-trace derivatives

For a differentiable operator family, the trace form of Duhamel's formula has
the shape

```text
partial_a h(a,t) = -t d(a,t),
```

where `d(a,t)` is the appropriate nuclear Duhamel trace.  The determinant
integrand has weight `1/t`; more invariantly, its weight satisfies

```text
w(t) * t = 1
```

on the selected positive-time region.  Hence

```text
w(t) * partial_a h(a,t) = -d(a,t).
```

This file records that cancellation and identifies the derivative of the
weighted heat integral with the negative integral of the Duhamel trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

/-- Weighted heat variation satisfying the trace Duhamel formula and the
logarithmic weight identity. -/
structure DuhamelWeightedHeatTraceVariationData
    (timeRegion : Set Real) where
  weighted : WeightedHeatTraceIntegralVariationData timeRegion
  duhamelTrace : Real → Real → Real
  heatTraceDerivative_eq : ∀ parameter,
    ∀ᵐ time ∂volume.restrict timeRegion,
      weighted.heatTraceDerivative parameter time =
        -time * duhamelTrace parameter time
  weight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict timeRegion,
      weighted.weight time * time = 1

namespace DuhamelWeightedHeatTraceVariationData

/-- On the logarithmic time weight, the weighted derivative kernel is exactly
minus the Duhamel trace. -/
theorem derivativeKernel_eq_neg_duhamelTrace
    {timeRegion : Set Real}
    (data : DuhamelWeightedHeatTraceVariationData timeRegion)
    (parameter : Real) :
    ∀ᵐ time ∂volume.restrict timeRegion,
      data.weighted.derivativeKernel parameter time =
        -data.duhamelTrace parameter time := by
  filter_upwards [data.heatTraceDerivative_eq parameter,
    data.weight_mul_time_eq_one] with time hDerivative hWeight
  unfold WeightedHeatTraceIntegralVariationData.derivativeKernel
  rw [hDerivative]
  calc
    data.weighted.weight time * (-time * data.duhamelTrace parameter time) =
        -(data.weighted.weight time * time) *
          data.duhamelTrace parameter time := by ring
    _ = -data.duhamelTrace parameter time := by rw [hWeight]; ring

/-- The derivative contribution is the negative integral of the Duhamel trace. -/
theorem derivativeContribution_eq_neg_integral_duhamelTrace
    {timeRegion : Set Real}
    (data : DuhamelWeightedHeatTraceVariationData timeRegion)
    (parameter : Real) :
    data.weighted.derivativeContribution parameter =
      -(∫ time in timeRegion, data.duhamelTrace parameter time) := by
  unfold WeightedHeatTraceIntegralVariationData.derivativeContribution
  calc
    (∫ time in timeRegion,
        data.weighted.weight time *
          data.weighted.heatTraceDerivative parameter time) =
        ∫ time in timeRegion, -data.duhamelTrace parameter time := by
      apply integral_congr_ae
      exact data.derivativeKernel_eq_neg_duhamelTrace parameter
    _ = -(∫ time in timeRegion, data.duhamelTrace parameter time) := by
      rw [integral_neg]

/-- Duhamel form of the derivative theorem for the weighted heat integral. -/
theorem hasDerivAt_contribution
    {timeRegion : Set Real}
    (data : DuhamelWeightedHeatTraceVariationData timeRegion)
    (parameter : Real) :
    HasDerivAt data.weighted.contribution
      (-(∫ time in timeRegion, data.duhamelTrace parameter time)) parameter := by
  rw [← data.derivativeContribution_eq_neg_integral_duhamelTrace parameter]
  exact data.weighted.hasDerivAt_integral parameter

/-- Public logarithmic-weight Duhamel checkpoint. -/
theorem duhamel_weighted_heat_trace_variation_gate
    (timeRegion : Set Real)
    (data : DuhamelWeightedHeatTraceVariationData timeRegion) :
    (∀ parameter,
      ∀ᵐ time ∂volume.restrict timeRegion,
        data.weighted.derivativeKernel parameter time =
          -data.duhamelTrace parameter time) ∧
    (∀ parameter,
      data.weighted.derivativeContribution parameter =
        -(∫ time in timeRegion, data.duhamelTrace parameter time)) ∧
    (∀ parameter,
      HasDerivAt data.weighted.contribution
        (-(∫ time in timeRegion, data.duhamelTrace parameter time)) parameter) :=
  ⟨data.derivativeKernel_eq_neg_duhamelTrace,
    data.derivativeContribution_eq_neg_integral_duhamelTrace,
    data.hasDerivAt_contribution⟩

end DuhamelWeightedHeatTraceVariationData

end
end P0EFTJanusProgramPDuhamelWeightedHeatTraceVariation4D
end JanusFormal
