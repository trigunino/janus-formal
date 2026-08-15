import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimits4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceDominatedExponentialCanonicalSchwarzAssembly4D

/-!
# Selected reference coefficient with exponential long-time domination

This frontend uses a general dominated short-time region and a concrete
exponentially dominated long-time half-line.  It generates

* differentiation through both weighted heat integrals;
* integrability of the long-time majorant;
* decay of the long-time terminal primitive;
* identification of the endpoint scalar with the selected chart trace;
* reality of the standalone zeta derivative by canonical Schwarz symmetry;
* `T_reference = -selectedTrace.trace`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open Filter Set
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceDominatedExponentialCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

variable {Slice ShortCutoff LongCutoff E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

structure ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData
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
    ReferenceNuclearDuhamelGreenSelectedTraceShortDominatedLongExponentialBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeStart
          referenceOperator selectedTrace
  logDeterminant_eq : ∀ parameter,
    P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter +
        spectralBoundary.toDominatedExponentialBoundaryLimits.
            toSelectedTraceExponentialBoundaryLimits.toSelectedTraceBoundaryLimits.
              toFullySpectralBoundaryLimits.shortTime.weighted.
                toWeightedHeatTraceVariation.contribution parameter +
          spectralBoundary.toDominatedExponentialBoundaryLimits.
              toSelectedTraceExponentialBoundaryLimits.toSelectedTraceBoundaryLimits.
                toFullySpectralBoundaryLimits.longTime.weighted.
                  toWeightedHeatTraceVariation.contribution parameter
  zetaCanonicalSchwarz : ∀ parameter,
    RelativeHeatMellinZetaCanonicalSchwarzReflectionData
      (family.continuation parameter)

namespace ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData

/-- Convert to the general dominated/exponential selected-reference assembly
after generating the long-time integrable majorant. -/
def toDominatedExponentialCanonicalSchwarzAssembly
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeStart) :
    ReferenceNuclearHeatFinitePartSelectedTraceDominatedExponentialCanonicalSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
        referenceOperator selectedTrace family shortTimeRegion
          (Set.Ioi longTimeStart) where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  spectralBoundary := data.spectralBoundary.toDominatedExponentialBoundaryLimits
  logDeterminant_eq := data.logDeterminant_eq
  zetaCanonicalSchwarz := data.zetaCanonicalSchwarz

/-- Long-time exponential integrability. -/
theorem longTime_bound_integrable
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeStart)
    (parameter : Real) :
    Integrable
      (P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D.
        longTimeExponentialBound
          (data.spectralBoundary.longTime.weighted.scale parameter)
          (data.spectralBoundary.longTime.weighted.rate parameter))
      (volume.restrict (Set.Ioi longTimeStart)) :=
  data.spectralBoundary.longTime_bound_integrable parameter

/-- Dominated short-time differentiation. -/
theorem shortTime_hasDerivAt
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeStart)
    (parameter : Real) :
    HasDerivAt
      data.spectralBoundary.shortTime.toCollapsedRankOneIntegral.weighted.
        toWeightedHeatTraceVariation.contribution
      (-(∫ time in shortTimeRegion,
        data.nuclear.extendedDuhamelTrace parameter time)) parameter :=
  data.toDominatedExponentialCanonicalSchwarzAssembly.
    shortTime_hasDerivAt parameter

/-- Exponentially dominated long-time differentiation. -/
theorem longTime_hasDerivAt
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeStart)
    (parameter : Real) :
    HasDerivAt
      data.spectralBoundary.longTime.toDominatedCollapsedRankOneIntegral.
        toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.
          contribution
      (-(∫ time in Set.Ioi longTimeStart,
        data.nuclear.extendedDuhamelTrace parameter time)) parameter :=
  data.spectralBoundary.longTime_hasDerivAt parameter

/-- The selected standalone reference coefficient. -/
theorem connectionCoefficient_eq_neg_selectedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion : Set Real} {longTimeStart : Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeStart)
    (parameter : Real) :
    P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
        relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(selectedTrace.trace parameter : Complex) :=
  data.toDominatedExponentialCanonicalSchwarzAssembly.
    connectionCoefficient_eq_neg_selectedTrace parameter

/-- Public selected-reference short/long checkpoint. -/
theorem reference_nuclear_heat_finite_part_selected_trace_short_dominated_long_exponential_canonical_schwarz_assembly_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData referenceOperator)
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion : Set Real) (longTimeStart : Real)
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeStart) :
    (∀ parameter,
      Integrable
        (P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D.
          longTimeExponentialBound
            (data.spectralBoundary.longTime.weighted.scale parameter)
            (data.spectralBoundary.longTime.weighted.rate parameter))
        (volume.restrict (Set.Ioi longTimeStart))) ∧
    (∀ parameter,
      HasDerivAt
        data.spectralBoundary.shortTime.toCollapsedRankOneIntegral.weighted.
          toWeightedHeatTraceVariation.contribution
        (-(∫ time in shortTimeRegion,
          data.nuclear.extendedDuhamelTrace parameter time)) parameter) ∧
    (∀ parameter,
      HasDerivAt
        data.spectralBoundary.longTime.toDominatedCollapsedRankOneIntegral.
          toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.
            contribution
        (-(∫ time in Set.Ioi longTimeStart,
          data.nuclear.extendedDuhamelTrace parameter time)) parameter) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(selectedTrace.trace parameter : Complex)) :=
  ⟨data.longTime_bound_integrable,
    data.shortTime_hasDerivAt,
    data.longTime_hasDerivAt,
    data.connectionCoefficient_eq_neg_selectedTrace⟩

end ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssembly4D
end JanusFormal
