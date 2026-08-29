import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimits4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelLongTimeExponentialDecay4D

/-!
# Selected-trace boundaries with generated long-time decay

The selected-trace boundary packet still accepted

```text
terminalPrimitive(R) → 0
```

inside its long-time endpoint certificate.  Concrete spectral estimates instead
produce a scalar exponential bound.  This frontend replaces the direct
vector-valued limit by

```text
‖terminalPrimitive(R)‖ ≤ C exp (-c T(R)),
0 < c,
T(R) → +∞.
```

The preceding exponential-decay theorem generates the required terminal limit,
then the selected-reference endpoint chain proceeds unchanged.  The
logarithmic target and trace remain definitionally those of the selected
`IntrinsicLogarithmicDerivativeTraceData`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimits4D

set_option autoImplicit false
noncomputable section

open Filter Set Topology MeasureTheory
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelCollapsedRankOneIntegral4D
open P0EFTJanusProgramPReferenceNuclearCountertermRankOneVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelLongTimeExponentialDecay4D

universe e i s a b

variable {Slice : Type s} {ShortCutoff : Type a} {LongCutoff : Type b}
  {E : Type e}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Selected-reference endpoint data whose long-time terminal limit is generated
from an exponential norm estimate. -/
structure ReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimitsData
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
  shortTime : NuclearDuhamelCollapsedRankOneIntegralData.{e, i, s} sliceMeasure nuclear
    shortTimeRegion
  longTime : NuclearDuhamelCollapsedRankOneIntegralData.{e, i, s} sliceMeasure nuclear
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

namespace ReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimitsData

/-- Generate the long-time vector limit and recover the selected-trace endpoint
packet. -/
def toSelectedTraceBoundaryLimits
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion longTimeRegion : Set Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeRegion
            referenceOperator selectedTrace) :
    ReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeRegion
          referenceOperator selectedTrace where
  countertermVariation := data.countertermVariation
  shortTime := data.shortTime
  longTime := data.longTime
  countertermMinusShortTraceClass := data.countertermMinusShortTraceClass
  totalTraceClass := data.totalTraceClass
  matchingOperator := data.matchingOperator
  shortBoundaryLimit := data.shortBoundaryLimit
  longBoundaryLimit := fun parameter =>
    (data.longBoundaryDecay parameter).toLongTimeBoundaryLimit

/-- Every terminal primitive in the family tends to zero. -/
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
      ReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeRegion
            referenceOperator selectedTrace)
    (parameter : Real) :
    Tendsto (data.longBoundaryDecay parameter).terminalPrimitive
      longCutoffFilter (𝓝 0) :=
  (data.longBoundaryDecay parameter).terminalPrimitive_tendsto_zero

/-- The final scalar remains exactly the selected logarithmic trace. -/
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
      ReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeRegion
            referenceOperator selectedTrace)
    (parameter : Real) :
    data.toSelectedTraceBoundaryLimits.toFullySpectralBoundaryLimits.toCollapsedBoundaryLimits.toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace
        parameter =
      selectedTrace.trace parameter :=
  data.toSelectedTraceBoundaryLimits.generatedLogarithmicTrace_eq_selectedTrace
    parameter

/-- Public selected-reference exponential endpoint checkpoint. -/
theorem reference_nuclear_duhamel_green_selected_trace_exponential_boundary_limits_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (countertermContribution : Real → Real)
    (shortTimeRegion longTimeRegion : Set Real)
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator)
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeRegion
            referenceOperator selectedTrace) :
    (∀ parameter,
      Tendsto (data.longBoundaryDecay parameter).terminalPrimitive
        longCutoffFilter (𝓝 0)) ∧
    (∀ parameter,
      data.toSelectedTraceBoundaryLimits.toFullySpectralBoundaryLimits.toCollapsedBoundaryLimits.toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace
          parameter =
        selectedTrace.trace parameter) :=
  ⟨data.terminalPrimitive_tendsto_zero,
    data.generatedLogarithmicTrace_eq_selectedTrace⟩

end ReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimitsData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimits4D
end JanusFormal
