import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimits4D

/-!
# Selected-reference boundaries with exponential long-time domination

The short-time region keeps a general local dominated packet because its
majorant depends on the renormalized small-time expansion.  On the long-time
half-line `(T₀, +∞)`, this frontend replaces the generic integrable bound by the
spectral envelope `C exp (-c t)` with `0 < c`.

It generates both long-time derivative integrability and terminal primitive
decay, then feeds the unchanged selected trace into the Duhamel--Green endpoint
identity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimits4D

set_option autoImplicit false
noncomputable section

open Filter Set
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
open P0EFTJanusProgramPNuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegral4D
open P0EFTJanusProgramPReferenceNuclearCountertermRankOneVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelLongTimeExponentialDecay4D

variable {Slice ShortCutoff LongCutoff E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

structure ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimitsData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (countertermContribution : Real → Real)
    (shortTimeRegion : Set Real) (longTimeStart : Real)
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator) where
  countertermVariation :
    ReferenceNuclearCountertermRankOneVariationData
      (E := E) countertermContribution
  shortTime :
    NuclearDuhamelDominatedCollapsedRankOneIntegralData sliceMeasure nuclear
      shortTimeRegion
  longTime :
    NuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegralData
      sliceMeasure nuclear longTimeStart
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
  longBoundaryDecay : ∀ parameter,
    ReferenceNuclearDuhamelLongTimeExponentialDecayData longCutoffFilter
      (longTime.integratedOperator parameter)
      (matchingOperator parameter)

namespace ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimitsData

/-- Convert to the general dominated/exponential boundary packet after
constructing the long-time integrable majorant. -/
def toDominatedExponentialBoundaryLimits
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace) :
    ReferenceNuclearDuhamelGreenSelectedTraceDominatedExponentialBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion (Set.Ioi longTimeStart)
          referenceOperator selectedTrace where
  countertermVariation := data.countertermVariation
  shortTime := data.shortTime
  longTime := data.longTime.toDominatedCollapsedRankOneIntegral
  countertermMinusShortTraceClass := data.countertermMinusShortTraceClass
  totalTraceClass := data.totalTraceClass
  matchingOperator := data.matchingOperator
  shortBoundaryLimit := data.shortBoundaryLimit
  longBoundaryDecay := data.longBoundaryDecay

/-- The long-time exponential majorant is integrable. -/
theorem longTime_bound_integrable
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace)
    (parameter : Real) :
    Integrable
      (P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D.
        longTimeExponentialBound (data.longTime.weighted.scale parameter)
          (data.longTime.weighted.rate parameter))
      (volume.restrict (Set.Ioi longTimeStart)) :=
  data.longTime.bound_integrable parameter

/-- The long-time weighted derivative is generated from the spectral envelope. -/
theorem longTime_hasDerivAt
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace)
    (parameter : Real) :
    HasDerivAt
      data.longTime.toDominatedCollapsedRankOneIntegral.
        toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.
          contribution
      (-(∫ time in Set.Ioi longTimeStart,
        nuclear.extendedDuhamelTrace parameter time)) parameter :=
  data.longTime.weightedIntegral_hasDerivAt parameter

/-- The selected logarithmic trace remains the terminal scalar. -/
@[simp] theorem generatedLogarithmicTrace_eq_selectedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace)
    (parameter : Real) :
    data.toDominatedExponentialBoundaryLimits.
        toSelectedTraceExponentialBoundaryLimits.toSelectedTraceBoundaryLimits.
          toFullySpectralBoundaryLimits.toCollapsedBoundaryLimits.
            toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.
              logarithmicTrace parameter = selectedTrace.trace parameter :=
  data.toDominatedExponentialBoundaryLimits.
    generatedLogarithmicTrace_eq_selectedTrace parameter

/-- Public short-dominated/long-exponential boundary checkpoint. -/
theorem reference_nuclear_duhamel_green_selected_trace_short_dominated_long_exponential_boundary_limits_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (countertermContribution : Real → Real)
    (shortTimeRegion : Set Real) (longTimeStart : Real)
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator)
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimitsData
        sliceMeasure shortCutoffFilter longCutoffFilter nuclear
          countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace) :
    (∀ parameter,
      Integrable
        (P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D.
          longTimeExponentialBound (data.longTime.weighted.scale parameter)
            (data.longTime.weighted.rate parameter))
        (volume.restrict (Set.Ioi longTimeStart))) ∧
    (∀ parameter,
      HasDerivAt
        data.longTime.toDominatedCollapsedRankOneIntegral.
          toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.
            contribution
        (-(∫ time in Set.Ioi longTimeStart,
          nuclear.extendedDuhamelTrace parameter time)) parameter) ∧
    (∀ parameter,
      data.toDominatedExponentialBoundaryLimits.
          toSelectedTraceExponentialBoundaryLimits.toSelectedTraceBoundaryLimits.
            toFullySpectralBoundaryLimits.toCollapsedBoundaryLimits.
              toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.
                logarithmicTrace parameter = selectedTrace.trace parameter) :=
  ⟨data.longTime_bound_integrable,
    data.longTime_hasDerivAt,
    data.generatedLogarithmicTrace_eq_selectedTrace⟩

end ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimitsData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimits4D
end JanusFormal
