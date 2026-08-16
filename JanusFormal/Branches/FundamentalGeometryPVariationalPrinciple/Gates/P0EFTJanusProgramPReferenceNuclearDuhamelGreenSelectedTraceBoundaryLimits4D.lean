import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenFullySpectralBoundaryLimits4D

/-!
# Duhamel--Green boundary limits tied to one selected reference trace

The fully spectral boundary packet still accepted an independently named
logarithmic derivative operator and an independently selected nuclear trace
certificate for it.  In the determinant atlas those data already exist in the
selected `IntrinsicLogarithmicDerivativeTraceData` of the reference chart.

This file parameterizes the endpoint construction directly by that selected
packet.  The short-time renormalized remainder therefore converges to the exact
operator

```text
G_ref,a H'_ref,a,
```

and the final nuclear certificate is definitionally the selected reference
certificate.  Consequently the generated scalar logarithmic trace is
literally the selected reference trace; no operator comparison, trace
comparison or uniqueness argument is required at the atlas boundary.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimits4D

set_option autoImplicit false
noncomputable section

open Filter Set
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelCollapsedRankOneIntegral4D
open P0EFTJanusProgramPReferenceNuclearCountertermRankOneVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenFullySpectralBoundaryLimits4D

variable {Slice ShortCutoff LongCutoff E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Complete spectral boundary data whose logarithmic target and nuclear trace
are the ones already selected by a reference chart. -/
structure ReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimitsData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (countertermContribution : Real → Real)
    (shortTimeRegion longTimeRegion : Set Real)
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator) where
  countertermVariation :
    ReferenceNuclearCountertermRankOneVariationData
      (E := E) countertermContribution
  shortTime : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
    shortTimeRegion
  longTime : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
    longTimeRegion
  countertermMinusShortTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData
      (countertermVariation.derivativeOperator parameter -
        shortTime.integratedOperator parameter)
  totalTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData
      ((countertermVariation.derivativeOperator parameter -
          shortTime.integratedOperator parameter) -
        longTime.integratedOperator parameter)
  matchingOperator : Real → E →L[Real] E
  shortBoundaryLimit : ∀ parameter,
    ReferenceNuclearDuhamelShortTimeBoundaryLimitData shortCutoffFilter
      (countertermVariation.derivativeOperator parameter)
      (shortTime.integratedOperator parameter)
      (selectedTrace.family.logarithmicDerivativeOperator parameter)
      (matchingOperator parameter)
  longBoundaryLimit : ∀ parameter,
    ReferenceNuclearDuhamelLongTimeBoundaryLimitData longCutoffFilter
      (longTime.integratedOperator parameter)
      (matchingOperator parameter)

namespace ReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimitsData

/-- Forget the selected-reference presentation only after inserting its exact
operator and exact nuclear trace certificate into the existing fully spectral
boundary packet. -/
def toFullySpectralBoundaryLimits
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion longTimeRegion : Set Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    (data : ReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeRegion
          referenceOperator selectedTrace) :
    ReferenceNuclearDuhamelGreenFullySpectralBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeRegion where
  countertermVariation := data.countertermVariation
  shortTime := data.shortTime
  longTime := data.longTime
  countertermMinusShortTraceClass := data.countertermMinusShortTraceClass
  totalTraceClass := data.totalTraceClass
  logarithmicDerivativeOperator :=
    selectedTrace.family.logarithmicDerivativeOperator
  logarithmicDerivativeTraceClass := selectedTrace.traceClass
  matchingOperator := data.matchingOperator
  shortBoundaryLimit := data.shortBoundaryLimit
  longBoundaryLimit := data.longBoundaryLimit

/-- The logarithmic operator entering the endpoint identity is definitionally
`G_ref H'_ref` from the selected reference family. -/
@[simp] theorem logarithmicDerivativeOperator_eq_selected
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion longTimeRegion : Set Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    (data : ReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeRegion
          referenceOperator selectedTrace)
    (parameter : Real) :
    data.toFullySpectralBoundaryLimits.logarithmicDerivativeOperator parameter =
      selectedTrace.family.logarithmicDerivativeOperator parameter :=
  rfl

/-- The scalar produced by the full endpoint chain is literally the selected
reference logarithmic trace. -/
@[simp] theorem generatedLogarithmicTrace_eq_selectedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion longTimeRegion : Set Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    (data : ReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeRegion
          referenceOperator selectedTrace)
    (parameter : Real) :
    data.toFullySpectralBoundaryLimits.toCollapsedBoundaryLimits.
        toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.
          logarithmicTrace parameter =
      selectedTrace.trace parameter :=
  rfl

/-- Public selected-reference boundary checkpoint. -/
theorem reference_nuclear_duhamel_green_selected_trace_boundary_limits_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (countertermContribution : Real → Real)
    (shortTimeRegion longTimeRegion : Set Real)
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator)
    (data : ReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeRegion
          referenceOperator selectedTrace) :
    (∀ parameter,
      data.toFullySpectralBoundaryLimits.logarithmicDerivativeOperator parameter =
        selectedTrace.family.logarithmicDerivativeOperator parameter) ∧
    (∀ parameter,
      data.toFullySpectralBoundaryLimits.toCollapsedBoundaryLimits.
          toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.
            logarithmicTrace parameter = selectedTrace.trace parameter) :=
  ⟨data.logarithmicDerivativeOperator_eq_selected,
    data.generatedLogarithmicTrace_eq_selectedTrace⟩

end ReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimitsData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceBoundaryLimits4D
end JanusFormal
