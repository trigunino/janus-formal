import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimits4D

/-!
# Selected-trace endpoint limits from domination and exponential decay

This is the strongest generic reference endpoint currently exposed by the
nuclear Duhamel chain.  It removes two formerly completed analytic statements:

```text
parameter differentiation commutes with the short/long time integral,
terminalPrimitive(R) tends to zero.
```

The first is generated from local dominated differentiation for each region;
the second is generated from a genuine exponential spectral estimate.  The
remaining endpoint data are the concrete rank-one expansions, the short-time
renormalized cutoff limit, and the finite-cutoff long-time primitive identity.

The final logarithmic operator and nuclear trace are still definitionally the
ones selected by the reference chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimits4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Topology
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
open P0EFTJanusProgramPReferenceNuclearCountertermRankOneVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelLongTimeExponentialDecay4D

universe e i s a b

variable {Slice : Type s} {ShortCutoff : Type a} {LongCutoff : Type b}
  {E : Type e}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Selected-reference endpoint data with generated integral differentiation
and generated long-time terminal decay. -/
structure ReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimitsData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (countertermContribution : Real → Real)
    (shortTimeRegion longTimeRegion : Set Real)
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i}
      referenceOperator) where
  countertermVariation :
    ReferenceNuclearCountertermRankOneVariationData.{i, e}
      (E := E) countertermContribution
  shortTime :
    NuclearDuhamelDominatedCollapsedRankOneIntegralData.{e, i, s} sliceMeasure nuclear
      shortTimeRegion
  longTime :
    NuclearDuhamelDominatedCollapsedRankOneIntegralData.{e, i, s} sliceMeasure nuclear
      longTimeRegion
  countertermMinusShortTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{e, i}
      (countertermVariation.derivativeOperator parameter -
        shortTime.integratedOperator parameter)
  totalTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{e, i}
      ((countertermVariation.derivativeOperator parameter -
          shortTime.integratedOperator parameter) -
        longTime.integratedOperator parameter)
  matchingOperator : Real → E →L[Real] E
  shortBoundaryLimit : ∀ parameter,
    ReferenceNuclearDuhamelShortTimeBoundaryLimitData.{a, e} shortCutoffFilter
      (countertermVariation.derivativeOperator parameter)
      (shortTime.integratedOperator parameter)
      (selectedTrace.family.logarithmicDerivativeOperator parameter)
      (matchingOperator parameter)
  longBoundaryDecay : ∀ parameter,
    ReferenceNuclearDuhamelLongTimeExponentialDecayData.{b, e} longCutoffFilter
      (longTime.integratedOperator parameter)
      (matchingOperator parameter)

namespace ReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimitsData

/-- Generate both weighted integral derivative theorems and the long-time
terminal limit, then recover the preceding selected exponential packet. -/
def toSelectedTraceExponentialBoundaryLimits
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion longTimeRegion : Set Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeRegion
            referenceOperator selectedTrace) :
    ReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeRegion
          referenceOperator selectedTrace where
  countertermVariation := data.countertermVariation
  shortTime := data.shortTime.toCollapsedRankOneIntegral
  longTime := data.longTime.toCollapsedRankOneIntegral
  countertermMinusShortTraceClass := data.countertermMinusShortTraceClass
  totalTraceClass := data.totalTraceClass
  matchingOperator := data.matchingOperator
  shortBoundaryLimit := data.shortBoundaryLimit
  longBoundaryDecay := data.longBoundaryDecay

/-- Dominated short-time differentiation. -/
theorem shortTime_hasDerivAt
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion longTimeRegion : Set Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeRegion
            referenceOperator selectedTrace)
    (parameter : Real) :
    HasDerivAt
      data.shortTime.toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.contribution
      (-(∫ time in shortTimeRegion,
        extendedDuhamelTrace nuclear parameter time)) parameter :=
  data.shortTime.weightedIntegral_hasDerivAt parameter

/-- Dominated long-time differentiation. -/
theorem longTime_hasDerivAt
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion longTimeRegion : Set Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeRegion
            referenceOperator selectedTrace)
    (parameter : Real) :
    HasDerivAt
      data.longTime.toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.contribution
      (-(∫ time in longTimeRegion,
        extendedDuhamelTrace nuclear parameter time)) parameter :=
  data.longTime.weightedIntegral_hasDerivAt parameter

/-- The long-time terminal primitive limit is generated from the exponential
estimate. -/
theorem terminalPrimitive_tendsto_zero
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion longTimeRegion : Set Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeRegion
            referenceOperator selectedTrace)
    (parameter : Real) :
    Tendsto (data.longBoundaryDecay parameter).terminalPrimitive
      longCutoffFilter (𝓝 0) :=
  (data.longBoundaryDecay parameter).terminalPrimitive_tendsto_zero

/-- The endpoint scalar remains the selected reference trace. -/
@[simp] theorem generatedLogarithmicTrace_eq_selectedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion longTimeRegion : Set Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeRegion
            referenceOperator selectedTrace)
    (parameter : Real) :
    data.toSelectedTraceExponentialBoundaryLimits.toSelectedTraceBoundaryLimits.toFullySpectralBoundaryLimits.toCollapsedBoundaryLimits.toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace
        parameter = selectedTrace.trace parameter :=
  data.toSelectedTraceExponentialBoundaryLimits.generatedLogarithmicTrace_eq_selectedTrace
    parameter

/-- Public dominated/exponential selected-reference endpoint checkpoint. -/
theorem reference_nuclear_duhamel_green_selected_trace_dominated_exponential_boundary_limits_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (countertermContribution : Real → Real)
    (shortTimeRegion longTimeRegion : Set Real)
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator)
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeRegion
            referenceOperator selectedTrace) :
    (∀ parameter,
      HasDerivAt
        data.shortTime.toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.contribution
        (-(∫ time in shortTimeRegion,
          extendedDuhamelTrace nuclear parameter time)) parameter) ∧
    (∀ parameter,
      HasDerivAt
        data.longTime.toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.contribution
        (-(∫ time in longTimeRegion,
          extendedDuhamelTrace nuclear parameter time)) parameter) ∧
    (∀ parameter,
      Tendsto (data.longBoundaryDecay parameter).terminalPrimitive
        longCutoffFilter (𝓝 0)) ∧
    (∀ parameter,
      data.toSelectedTraceExponentialBoundaryLimits.toSelectedTraceBoundaryLimits.toFullySpectralBoundaryLimits.toCollapsedBoundaryLimits.toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace
          parameter = selectedTrace.trace parameter) :=
  ⟨data.shortTime_hasDerivAt,
    data.longTime_hasDerivAt,
    data.terminalPrimitive_tendsto_zero,
    data.generatedLogarithmicTrace_eq_selectedTrace⟩

end ReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimitsData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimits4D
end JanusFormal
