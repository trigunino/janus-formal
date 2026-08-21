import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelProductThroatLongTimeCollapsedRankOneIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelProductThroatLongTimeDecay4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimits4D

/-!
# Selected-reference boundaries with concrete product-throat long-time decay

The short-time region remains governed by its local dominated asymptotic
packet.  The long-time region is now tied to one genuine product-throat
reference spectrum in two places:

* the inserted Duhamel trace is dominated by the product heat trace;
* the terminal primitive is dominated by the same product heat trace.

Both exponential packets therefore use the exact rate `1 / R^2`; no unrelated
long-time decay rate remains in the selected-reference boundary interface.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimits4D

set_option autoImplicit false
noncomputable section

open Filter Set Topology MeasureTheory
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
open P0EFTJanusProgramPNuclearDuhamelProductThroatLongTimeCollapsedRankOneIntegral4D
open P0EFTJanusProgramPReferenceNuclearCountertermRankOneVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearDuhamelProductThroatLongTimeDecay4D
open P0EFTJanusProductThroatPositiveHeatGapLongTime4D
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D

universe e i s a b

variable {Slice : Type s} {ShortCutoff : Type a} {LongCutoff : Type b}
  {E : Type e}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Selected-reference endpoint data whose complete long-time analysis comes
from one concrete product-throat reference spectrum. -/
structure ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (countertermContribution : Real → Real)
    (shortTimeRegion : Set Real) (longTimeStart : Real)
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
    NuclearDuhamelProductThroatLongTimeCollapsedRankOneIntegralData.{e, i, s}
      productData fold twist sliceMeasure nuclear longTimeStart
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
    ReferenceNuclearDuhamelProductThroatLongTimeDecayData.{b, e}
      productData fold twist longCutoffFilter
        (longTime.integratedOperator parameter)
        (matchingOperator parameter)

namespace ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData

/-- Convert to the preceding short-dominated/long-exponential boundary packet
after generating both occurrences of its exponential rate from the product
spectrum. -/
def toShortDominatedLongExponentialBoundaryLimits
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData
        productData fold twist sliceMeasure shortCutoffFilter longCutoffFilter
          nuclear countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace) :
    ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeStart
          referenceOperator selectedTrace where
  countertermVariation := data.countertermVariation
  shortTime := data.shortTime
  longTime :=
    data.longTime.toLongTimeExponentialDominatedCollapsedRankOneIntegral
  countertermMinusShortTraceClass := data.countertermMinusShortTraceClass
  totalTraceClass := data.totalTraceClass
  matchingOperator := data.matchingOperator
  shortBoundaryLimit := data.shortBoundaryLimit
  longBoundaryDecay := fun parameter =>
    (data.longBoundaryDecay parameter).toLongTimeExponentialDecay

/-- The Duhamel-integrand decay rate is the concrete product heat gap. -/
@[simp] theorem longTime_generatedRate_eq_productThroatPositiveHeatGap
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData
        productData fold twist sliceMeasure shortCutoffFilter longCutoffFilter
          nuclear countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace)
    (parameter : Real) :
    data.toShortDominatedLongExponentialBoundaryLimits.longTime.weighted.rate
        parameter =
      productThroatPositiveHeatGap productData :=
  rfl

/-- The terminal-primitive decay rate is the same product heat gap. -/
@[simp] theorem terminal_generatedRate_eq_productThroatPositiveHeatGap
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData
        productData fold twist sliceMeasure shortCutoffFilter longCutoffFilter
          nuclear countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace)
    (parameter : Real) :
    (data.toShortDominatedLongExponentialBoundaryLimits.longBoundaryDecay
      parameter).rate = productThroatPositiveHeatGap productData :=
  rfl

/-- The product-generated Duhamel majorant is integrable. -/
theorem longTime_bound_integrable
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData
        productData fold twist sliceMeasure shortCutoffFilter longCutoffFilter
          nuclear countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace)
    (parameter : Real) :
    Integrable
      (longTimeExponentialBound
        (data.longTime.weighted.longTimeScale parameter)
        (productThroatPositiveHeatGap productData))
      (volume.restrict (Set.Ioi longTimeStart)) :=
  data.longTime.bound_integrable parameter

/-- Product spectral decay forces the terminal primitive to zero. -/
theorem terminalPrimitive_tendsto_zero
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData
        productData fold twist sliceMeasure shortCutoffFilter longCutoffFilter
          nuclear countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace)
    (parameter : Real) :
    Tendsto (data.longBoundaryDecay parameter).terminalPrimitive
      longCutoffFilter (𝓝 0) :=
  (data.longBoundaryDecay parameter).terminalPrimitive_tendsto_zero

/-- The endpoint scalar remains definitionally the selected intrinsic trace. -/
@[simp] theorem generatedLogarithmicTrace_eq_selectedTrace
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {countertermContribution : Real → Real}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData
        productData fold twist sliceMeasure shortCutoffFilter longCutoffFilter
          nuclear countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace)
    (parameter : Real) :
    data.toShortDominatedLongExponentialBoundaryLimits.toDominatedExponentialBoundaryLimits.toSelectedTraceExponentialBoundaryLimits.toSelectedTraceBoundaryLimits.toFullySpectralBoundaryLimits.toCollapsedBoundaryLimits.toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace
        parameter = selectedTrace.trace parameter :=
  data.toShortDominatedLongExponentialBoundaryLimits.generatedLogarithmicTrace_eq_selectedTrace
    parameter

/-- Public selected-reference product-throat long-time boundary checkpoint. -/
theorem reference_nuclear_duhamel_green_selected_trace_short_dominated_product_throat_long_time_boundary_limits_gate
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (countertermContribution : Real → Real)
    (shortTimeRegion : Set Real) (longTimeStart : Real)
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator)
    (data :
      ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData
        productData fold twist sliceMeasure shortCutoffFilter longCutoffFilter
          nuclear countertermContribution shortTimeRegion longTimeStart
            referenceOperator selectedTrace) :
    0 < productThroatPositiveHeatGap productData ∧
    (∀ parameter,
      Integrable
        (longTimeExponentialBound
          (data.longTime.weighted.longTimeScale parameter)
          (productThroatPositiveHeatGap productData))
        (volume.restrict (Set.Ioi longTimeStart))) ∧
    (∀ parameter,
      Tendsto (data.longBoundaryDecay parameter).terminalPrimitive
        longCutoffFilter (𝓝 0)) ∧
    (∀ parameter,
      data.toShortDominatedLongExponentialBoundaryLimits.toDominatedExponentialBoundaryLimits.toSelectedTraceExponentialBoundaryLimits.toSelectedTraceBoundaryLimits.toFullySpectralBoundaryLimits.toCollapsedBoundaryLimits.toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace
          parameter = selectedTrace.trace parameter) :=
  ⟨productThroatPositiveHeatGap_pos productData,
    data.longTime_bound_integrable,
    data.terminalPrimitive_tendsto_zero,
    data.generatedLogarithmicTrace_eq_selectedTrace⟩

end ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimits4D
end JanusFormal
