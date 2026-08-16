import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D

/-!
# Long-time Duhamel boundary decay from an exponential estimate

The endpoint-limit interface asks directly for convergence of the terminal
primitive to zero.  In concrete heat calculations this convergence is normally
proved by a scalar spectral estimate

```text
‖terminalPrimitive(R)‖ ≤ C exp (-c T(R)),
0 < c,
T(R) → +∞.
```

This file turns exactly that estimate into the required vector-valued limit.
It deliberately does not claim that a two-sided operator gap
`c ‖x‖ ≤ ‖H x‖` alone implies heat decay: positivity of the heat generator, or
an equivalent spectral estimate, remains a genuine input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelLongTimeExponentialDecay4D

set_option autoImplicit false
noncomputable section

open Filter Topology
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D

variable {Cutoff E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Finite-cutoff long-time identity together with an exponentially decaying
bound for its terminal primitive. -/
structure ReferenceNuclearDuhamelLongTimeExponentialDecayData
    (cutoffFilter : Filter Cutoff) [NeBot cutoffFilter]
    (integratedOperator matchingOperator : E) where
  partialIntegral : Cutoff → E
  terminalPrimitive : Cutoff → E
  cutoffTime : Cutoff → Real
  scale : Real
  rate : Real
  scale_nonneg : 0 ≤ scale
  rate_pos : 0 < rate
  cutoffTime_tendsto_atTop : Tendsto cutoffTime cutoffFilter atTop
  terminalPrimitive_norm_le : ∀ᶠ cutoff in cutoffFilter,
    ‖terminalPrimitive cutoff‖ ≤
      scale * Real.exp (-rate * cutoffTime cutoff)
  partialIntegral_tendsto :
    Tendsto partialIntegral cutoffFilter (𝓝 integratedOperator)
  finiteBoundaryIdentity : ∀ cutoff,
    partialIntegral cutoff + terminalPrimitive cutoff = matchingOperator

namespace ReferenceNuclearDuhamelLongTimeExponentialDecayData

/-- The scalar exponential envelope tends to zero. -/
theorem envelope_tendsto_zero
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelLongTimeExponentialDecayData cutoffFilter
      integratedOperator matchingOperator) :
    Tendsto
      (fun cutoff =>
        data.scale * Real.exp (-data.rate * data.cutoffTime cutoff))
      cutoffFilter (𝓝 0) := by
  have hRateTime :
      Tendsto (fun cutoff => data.rate * data.cutoffTime cutoff)
        cutoffFilter atTop :=
    (tendsto_const_mul_atTop_of_pos data.rate_pos).2
      data.cutoffTime_tendsto_atTop
  have hNegative :
      Tendsto (fun cutoff => -(data.rate * data.cutoffTime cutoff))
        cutoffFilter atBot :=
    tendsto_neg_atTop_atBot.comp hRateTime
  have hExp :
      Tendsto
        (fun cutoff => Real.exp (-(data.rate * data.cutoffTime cutoff)))
        cutoffFilter (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hNegative
  have hScaled :
      Tendsto
        (fun cutoff =>
          data.scale * Real.exp (-(data.rate * data.cutoffTime cutoff)))
        cutoffFilter (𝓝 (data.scale * 0)) :=
    tendsto_const_nhds.mul hExp
  simpa [neg_mul] using hScaled

/-- Exponential norm decay gives the vector-valued terminal limit required by
the boundary packet. -/
theorem terminalPrimitive_tendsto_zero
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelLongTimeExponentialDecayData cutoffFilter
      integratedOperator matchingOperator) :
    Tendsto data.terminalPrimitive cutoffFilter (𝓝 0) :=
  squeeze_zero_norm' data.terminalPrimitive_norm_le data.envelope_tendsto_zero

/-- Convert the spectral exponential estimate to the existing long-time
boundary-limit interface. -/
def toLongTimeBoundaryLimit
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelLongTimeExponentialDecayData cutoffFilter
      integratedOperator matchingOperator) :
    ReferenceNuclearDuhamelLongTimeBoundaryLimitData cutoffFilter
      integratedOperator matchingOperator where
  partialIntegral := data.partialIntegral
  terminalPrimitive := data.terminalPrimitive
  partialIntegral_tendsto := data.partialIntegral_tendsto
  terminalPrimitive_tendsto_zero := data.terminalPrimitive_tendsto_zero
  finiteBoundaryIdentity := data.finiteBoundaryIdentity

/-- The full long-time integral equals the matching operator. -/
theorem boundaryIdentity
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelLongTimeExponentialDecayData cutoffFilter
      integratedOperator matchingOperator) :
    integratedOperator = matchingOperator :=
  data.toLongTimeBoundaryLimit.boundaryIdentity

/-- Public exponential long-time checkpoint. -/
theorem reference_nuclear_duhamel_long_time_exponential_decay_gate
    (cutoffFilter : Filter Cutoff) [NeBot cutoffFilter]
    (integratedOperator matchingOperator : E)
    (data : ReferenceNuclearDuhamelLongTimeExponentialDecayData cutoffFilter
      integratedOperator matchingOperator) :
    Tendsto data.terminalPrimitive cutoffFilter (𝓝 0) ∧
      integratedOperator = matchingOperator :=
  ⟨data.terminalPrimitive_tendsto_zero, data.boundaryIdentity⟩

end ReferenceNuclearDuhamelLongTimeExponentialDecayData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelLongTimeExponentialDecay4D
end JanusFormal
