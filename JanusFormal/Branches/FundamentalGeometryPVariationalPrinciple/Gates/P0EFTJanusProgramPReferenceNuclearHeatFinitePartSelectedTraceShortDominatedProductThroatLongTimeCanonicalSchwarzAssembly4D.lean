import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimits4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssembly4D

/-!
# Selected zeta coefficient with product-throat long-time analysis

For one standalone reference chart this frontend combines

* the general dominated short-time renormalization;
* the concrete product-throat heat gap `1 / R^2`;
* product-spectral domination of the Duhamel insertion;
* product-spectral decay of the terminal primitive;
* the selected intrinsic logarithmic trace;
* canonical Mellin Schwarz reflection.

It converts to the preceding short-dominated/long-exponential assembly, but
both long-time rates and both long-time scales have already been generated from
the genuine reference spectrum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open Filter Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProductThroatPositiveHeatGapLongTime4D
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D

variable {Slice ShortCutoff LongCutoff E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Standalone selected-reference zeta data whose full long-time analysis comes
from one concrete product-throat spectrum. -/
structure ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator)
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion : Set Real) (longTimeStart : Real) where
  nuclear : NuclearHeatDuhamelTraceVariationData (E := E)
  countertermContribution : Real → Real
  spectralBoundary :
    ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedProductThroatLongTimeBoundaryLimitsData
      productData fold twist sliceMeasure shortCutoffFilter longCutoffFilter
        nuclear countertermContribution shortTimeRegion longTimeStart
          referenceOperator selectedTrace
  logDeterminant_eq : ∀ parameter,
    P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter +
        spectralBoundary.toShortDominatedLongExponentialBoundaryLimits.
            toDominatedExponentialBoundaryLimits.
              toSelectedTraceExponentialBoundaryLimits.toSelectedTraceBoundaryLimits.
                toFullySpectralBoundaryLimits.shortTime.weighted.
                  toWeightedHeatTraceVariation.contribution parameter +
          spectralBoundary.toShortDominatedLongExponentialBoundaryLimits.
              toDominatedExponentialBoundaryLimits.
                toSelectedTraceExponentialBoundaryLimits.toSelectedTraceBoundaryLimits.
                  toFullySpectralBoundaryLimits.longTime.weighted.
                    toWeightedHeatTraceVariation.contribution parameter
  zetaCanonicalSchwarz : ∀ parameter,
    RelativeHeatMellinZetaCanonicalSchwarzReflectionData
      (family.continuation parameter)

namespace ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData

/-- Convert to the previous selected-trace assembly after generating the full
product-spectral long-time boundary packet. -/
def toShortDominatedLongExponentialCanonicalSchwarzAssembly
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData
        (E := E) productData fold twist sliceMeasure shortCutoffFilter
          longCutoffFilter referenceOperator selectedTrace family
            shortTimeRegion longTimeStart) :
    ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
        referenceOperator selectedTrace family shortTimeRegion longTimeStart where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  spectralBoundary :=
    data.spectralBoundary.toShortDominatedLongExponentialBoundaryLimits
  logDeterminant_eq := data.logDeterminant_eq
  zetaCanonicalSchwarz := data.zetaCanonicalSchwarz

/-- The long-time insertion rate is the concrete product gap. -/
@[simp] theorem longTime_generatedRate_eq_productThroatPositiveHeatGap
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData
        (E := E) productData fold twist sliceMeasure shortCutoffFilter
          longCutoffFilter referenceOperator selectedTrace family
            shortTimeRegion longTimeStart)
    (parameter : Real) :
    data.toShortDominatedLongExponentialCanonicalSchwarzAssembly.
        spectralBoundary.longTime.weighted.rate parameter =
      productThroatPositiveHeatGap productData :=
  rfl

/-- The terminal primitive uses the identical product gap. -/
@[simp] theorem terminal_generatedRate_eq_productThroatPositiveHeatGap
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData
        (E := E) productData fold twist sliceMeasure shortCutoffFilter
          longCutoffFilter referenceOperator selectedTrace family
            shortTimeRegion longTimeStart)
    (parameter : Real) :
    (data.toShortDominatedLongExponentialCanonicalSchwarzAssembly.
      spectralBoundary.longBoundaryDecay parameter).rate =
        productThroatPositiveHeatGap productData :=
  rfl

/-- The product-generated exponential insertion envelope is integrable. -/
theorem longTime_bound_integrable
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData
        (E := E) productData fold twist sliceMeasure shortCutoffFilter
          longCutoffFilter referenceOperator selectedTrace family
            shortTimeRegion longTimeStart)
    (parameter : Real) :
    Integrable
      (longTimeExponentialBound
        (data.spectralBoundary.longTime.weighted.longTimeScale parameter)
        (productThroatPositiveHeatGap productData))
      (volume.restrict (Set.Ioi longTimeStart)) :=
  data.spectralBoundary.longTime_bound_integrable parameter

/-- Product spectral decay removes the terminal primitive. -/
theorem terminalPrimitive_tendsto_zero
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData
        (E := E) productData fold twist sliceMeasure shortCutoffFilter
          longCutoffFilter referenceOperator selectedTrace family
            shortTimeRegion longTimeStart)
    (parameter : Real) :
    Tendsto (data.spectralBoundary.longBoundaryDecay parameter).
        terminalPrimitive longCutoffFilter (𝓝 0) :=
  data.spectralBoundary.terminalPrimitive_tendsto_zero parameter

/-- Dominated short-time differentiation is unchanged. -/
theorem shortTime_hasDerivAt
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData
        (E := E) productData fold twist sliceMeasure shortCutoffFilter
          longCutoffFilter referenceOperator selectedTrace family
            shortTimeRegion longTimeStart)
    (parameter : Real) :
    HasDerivAt
      data.spectralBoundary.shortTime.toCollapsedRankOneIntegral.weighted.
        toWeightedHeatTraceVariation.contribution
      (-(∫ time in shortTimeRegion,
        data.nuclear.extendedDuhamelTrace parameter time)) parameter :=
  data.toShortDominatedLongExponentialCanonicalSchwarzAssembly.
    shortTime_hasDerivAt parameter

/-- Product-spectral long-time differentiation. -/
theorem longTime_hasDerivAt
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData
        (E := E) productData fold twist sliceMeasure shortCutoffFilter
          longCutoffFilter referenceOperator selectedTrace family
            shortTimeRegion longTimeStart)
    (parameter : Real) :
    HasDerivAt
      data.spectralBoundary.longTime.
        toLongTimeExponentialDominatedCollapsedRankOneIntegral.
          toDominatedCollapsedRankOneIntegral.toCollapsedRankOneIntegral.weighted.
            toWeightedHeatTraceVariation.contribution
      (-(∫ time in Set.Ioi longTimeStart,
        data.nuclear.extendedDuhamelTrace parameter time)) parameter :=
  data.spectralBoundary.longTime.weightedIntegral_hasDerivAt parameter

/-- The standalone reference connection coefficient is the selected intrinsic
trace. -/
theorem connectionCoefficient_eq_neg_selectedTrace
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData
        (E := E) productData fold twist sliceMeasure shortCutoffFilter
          longCutoffFilter referenceOperator selectedTrace family
            shortTimeRegion longTimeStart)
    (parameter : Real) :
    P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
        relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(selectedTrace.trace parameter : Complex) :=
  data.toShortDominatedLongExponentialCanonicalSchwarzAssembly.
    connectionCoefficient_eq_neg_selectedTrace parameter

/-- Public selected-reference product-throat zeta checkpoint. -/
theorem reference_nuclear_heat_finite_part_selected_trace_short_dominated_product_throat_long_time_canonical_schwarz_assembly_gate
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator)
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion : Set Real) (longTimeStart : Real)
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData
        (E := E) productData fold twist sliceMeasure shortCutoffFilter
          longCutoffFilter referenceOperator selectedTrace family
            shortTimeRegion longTimeStart) :
    0 < productThroatPositiveHeatGap productData ∧
    (∀ parameter,
      Integrable
        (longTimeExponentialBound
          (data.spectralBoundary.longTime.weighted.longTimeScale parameter)
          (productThroatPositiveHeatGap productData))
        (volume.restrict (Set.Ioi longTimeStart))) ∧
    (∀ parameter,
      Tendsto (data.spectralBoundary.longBoundaryDecay parameter).
          terminalPrimitive longCutoffFilter (𝓝 0)) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(selectedTrace.trace parameter : Complex)) :=
  ⟨productThroatPositiveHeatGap_pos productData,
    data.longTime_bound_integrable,
    data.terminalPrimitive_tendsto_zero,
    data.connectionCoefficient_eq_neg_selectedTrace⟩

end ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssembly4D
end JanusFormal
