import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatIntegralVariation4D
import Mathlib.Algebra.Ring.Ext

/-!
# Differentiated weighted heat-trace integrals

Both short- and long-time determinant contributions have the form

```text
I(a) = integral_R w(t) h(a,t) dt.
```

A pointwise derivative `h'_a(t)` gives the formal derivative kernel

```text
w(t) h'_a(t).
```

This file packages the weighted integral and derives its pointwise derivative
law.  The sole remaining analytic input is the interchange theorem asserting
that the derivative of the integral is the integral of the derivative.  This is
where local domination and endpoint estimates belong.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPRelativeHeatIntegralVariation4D

/-- One weighted heat-trace integral with pointwise parameter derivative and a
certified differentiation-under-the-integral theorem. -/
structure WeightedHeatTraceIntegralVariationData
    (timeRegion : Set Real) where
  weight : Real → Real
  heatTrace : Real → Real → Real
  heatTraceDerivative : Real → Real → Real
  pointwise_hasDerivAt_heatTrace : ∀ parameter,
    ∀ᵐ time ∂volume.restrict timeRegion,
      HasDerivAt (fun current => heatTrace current time)
        (heatTraceDerivative parameter time) parameter
  hasDerivAt_integral : ∀ parameter,
    HasDerivAt
      (fun current =>
        ∫ time in timeRegion, weight time * heatTrace current time)
      (∫ time in timeRegion,
        weight time * heatTraceDerivative parameter time)
      parameter

namespace WeightedHeatTraceIntegralVariationData

/-- Weighted heat-trace contribution. -/
def contribution
    {timeRegion : Set Real}
    (data : WeightedHeatTraceIntegralVariationData timeRegion)
    (parameter : Real) : Real :=
  ∫ time in timeRegion, data.weight time * data.heatTrace parameter time

/-- Integral of the weighted pointwise derivative. -/
def derivativeContribution
    {timeRegion : Set Real}
    (data : WeightedHeatTraceIntegralVariationData timeRegion)
    (parameter : Real) : Real :=
  ∫ time in timeRegion,
    data.weight time * data.heatTraceDerivative parameter time

/-- Weighted kernel. -/
def kernel
    {timeRegion : Set Real}
    (data : WeightedHeatTraceIntegralVariationData timeRegion)
    (parameter time : Real) : Real :=
  data.weight time * data.heatTrace parameter time

/-- Weighted derivative kernel. -/
def derivativeKernel
    {timeRegion : Set Real}
    (data : WeightedHeatTraceIntegralVariationData timeRegion)
    (parameter time : Real) : Real :=
  data.weight time * data.heatTraceDerivative parameter time

/-- Pointwise weighted kernel derivative. -/
theorem pointwise_hasDerivAt_kernel
    {timeRegion : Set Real}
    (data : WeightedHeatTraceIntegralVariationData timeRegion)
    (parameter : Real) :
    ∀ᵐ time ∂volume.restrict timeRegion,
      HasDerivAt (fun current => data.kernel current time)
        (data.derivativeKernel parameter time) parameter := by
  filter_upwards [data.pointwise_hasDerivAt_heatTrace parameter] with time hTime
  change HasDerivAt
    (fun current => data.weight time * data.heatTrace current time)
    (data.weight time * data.heatTraceDerivative parameter time) parameter
  convert hTime.const_smul (data.weight time) using 1
  · apply AddCommGroup.ext
    funext first second
    rfl
  · apply Module.ext
    funext scalar value
    rfl
  · funext current
    rfl
  · rfl

/-- Convert to the generic parameterized integral interface. -/
def toParametricIntegralVariation
    {timeRegion : Set Real}
    (data : WeightedHeatTraceIntegralVariationData timeRegion) :
    ParametricRealIntegralVariationData timeRegion where
  kernel := data.kernel
  derivativeKernel := data.derivativeKernel
  contribution := data.contribution
  derivativeContribution := data.derivativeContribution
  contribution_eq_integral := fun _ => rfl
  derivativeContribution_eq_integral := fun _ => rfl
  pointwise_hasDerivAt := data.pointwise_hasDerivAt_kernel
  hasDerivAt_integral := data.hasDerivAt_integral

/-- Public weighted heat-integral checkpoint. -/
theorem weighted_heat_trace_integral_variation_gate
    (timeRegion : Set Real)
    (data : WeightedHeatTraceIntegralVariationData timeRegion) :
    (∀ parameter,
      HasDerivAt data.contribution
        (data.derivativeContribution parameter) parameter) ∧
    (∀ parameter,
      ∀ᵐ time ∂volume.restrict timeRegion,
        HasDerivAt (fun current => data.kernel current time)
          (data.derivativeKernel parameter time) parameter) :=
  ⟨data.hasDerivAt_integral,
    data.pointwise_hasDerivAt_kernel⟩

end WeightedHeatTraceIntegralVariationData

end
end P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D
end JanusFormal
