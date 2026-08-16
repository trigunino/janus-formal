import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenCollapsedBoundaryLimits4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryAssembly4D

/-!
# Reference finite parts from collapsed Duhamel endpoint limits

This is the strongest generic standalone-reference frontend.  It starts from

* probability-averaged Duhamel slices;
* nuclear cyclicity and the heat semigroup law;
* rank-one expansions of `H'_a K_a(t)`;
* short- and long-time coefficient integrals;
* a short-time renormalized cutoff limit;
* a long-time primitive with vanishing terminal value.

The exact short/long boundary identities, global operator equality, intrinsic
trace formula, finite-part derivative and standalone reference zeta coefficient
are all derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssembly4D

set_option autoImplicit false
noncomputable section

open Filter Set
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenCollapsedBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryAssembly4D

variable {Slice ShortCutoff LongCutoff E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Complete reference zeta packet generated from spectral Duhamel endpoint
limits. -/
structure ReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssemblyData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real) where
  nuclear : NuclearHeatDuhamelTraceVariationData (E := E)
  countertermContribution : Real → Real
  boundaryLimits :
    ReferenceNuclearDuhamelGreenCollapsedBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        shortTimeRegion longTimeRegion
  hasDerivAt_counterterm : ∀ parameter,
    HasDerivAt countertermContribution
      (boundaryLimits.countertermDerivative parameter) parameter
  logDeterminant_eq : ∀ parameter,
    P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter +
        boundaryLimits.shortTime.weighted.toWeightedHeatTraceVariation.
            contribution parameter +
          boundaryLimits.longTime.weighted.toWeightedHeatTraceVariation.
            contribution parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssemblyData

/-- Convert endpoint limits to the collapsed finite-part assembly after both
boundary identities have been proved. -/
def toCollapsedBoundaryAssembly
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion) :
    ReferenceNuclearHeatFinitePartCollapsedBoundaryAssemblyData
      (E := E) sliceMeasure family shortTimeRegion longTimeRegion where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  collapsedBoundary := data.boundaryLimits.toCollapsedBoundary
  hasDerivAt_counterterm := data.hasDerivAt_counterterm
  logDeterminant_eq := data.logDeterminant_eq
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The finite-part logarithm differentiates to the intrinsic logarithmic
operator trace. -/
theorem hasDerivAt_finitePartLog
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
      (data.boundaryLimits.toCollapsedBoundary.toBoundaryMatching.
        toOperatorIdentity.logarithmicTrace parameter) parameter :=
  data.toCollapsedBoundaryAssembly.hasDerivAt_finitePartLog parameter

/-- Standalone reference zeta coefficient generated from endpoint limits. -/
theorem connectionCoefficient_eq_neg_logarithmicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion)
    (parameter : Real) :
    P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
        relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.boundaryLimits.toCollapsedBoundary.toBoundaryMatching.
          toOperatorIdentity.logarithmicTrace parameter : Complex) :=
  data.toCollapsedBoundaryAssembly.connectionCoefficient_eq_neg_logarithmicTrace
    parameter

/-- Public endpoint-limit finite-part checkpoint. -/
theorem reference_nuclear_heat_finite_part_collapsed_boundary_limits_assembly_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion) :
    (∀ parameter,
      data.boundaryLimits.countertermOperator parameter -
          data.boundaryLimits.shortTime.integratedOperator parameter =
        data.boundaryLimits.logarithmicDerivativeOperator parameter +
          data.boundaryLimits.matchingOperator parameter) ∧
    (∀ parameter,
      data.boundaryLimits.longTime.integratedOperator parameter =
        data.boundaryLimits.matchingOperator parameter) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
            relativeHeatFinitePartLogDeterminant
              (family.finitePartFamily.finitePart current))
        (data.boundaryLimits.toCollapsedBoundary.toBoundaryMatching.
          toOperatorIdentity.logarithmicTrace parameter) parameter) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.boundaryLimits.toCollapsedBoundary.toBoundaryMatching.
            toOperatorIdentity.logarithmicTrace parameter : Complex)) :=
  ⟨data.boundaryLimits.shortBoundaryIdentity,
    data.boundaryLimits.longBoundaryIdentity,
    data.hasDerivAt_finitePartLog,
    data.connectionCoefficient_eq_neg_logarithmicTrace⟩

end ReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssembly4D
end JanusFormal
