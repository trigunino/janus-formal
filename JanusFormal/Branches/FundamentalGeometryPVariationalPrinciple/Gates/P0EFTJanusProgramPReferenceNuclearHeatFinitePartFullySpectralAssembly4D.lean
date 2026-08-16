import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenFullySpectralBoundaryLimits4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssembly4D

/-!
# Fully spectral standalone reference finite-part assembly

This is the strongest generic reference-zeta assembly.  The counterterm
contribution is a differentiable rank-one trace series; the Duhamel simplex
average is spectral; every slice collapses by cyclicity and the heat semigroup
law; the short/long time integrals are obtained from spectral coefficient
integrals; and both boundary identities follow from endpoint limits.

The finite-part logarithmic derivative and standalone zeta connection
coefficient are therefore generated without any scalar comparison with an
operator trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartFullySpectralAssembly4D

set_option autoImplicit false
noncomputable section

open Filter Set
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenFullySpectralBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssembly4D

variable {Slice ShortCutoff LongCutoff E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Complete standalone reference packet with fully spectral counterterm and
Duhamel data. -/
structure ReferenceNuclearHeatFinitePartFullySpectralAssemblyData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real) where
  nuclear : NuclearHeatDuhamelTraceVariationData (E := E)
  countertermContribution : Real → Real
  spectralBoundary :
    ReferenceNuclearDuhamelGreenFullySpectralBoundaryLimitsData
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeRegion
  logDeterminant_eq : ∀ parameter,
    P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter +
        spectralBoundary.shortTime.weighted.toWeightedHeatTraceVariation.
            contribution parameter +
          spectralBoundary.longTime.weighted.toWeightedHeatTraceVariation.
            contribution parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceNuclearHeatFinitePartFullySpectralAssemblyData

/-- Convert the fully spectral packet to the preceding endpoint-limit assembly
after deriving the counterterm variation. -/
def toCollapsedBoundaryLimitsAssembly
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartFullySpectralAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion) :
    ReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  boundaryLimits := data.spectralBoundary.toCollapsedBoundaryLimits
  hasDerivAt_counterterm :=
    data.spectralBoundary.hasDerivAt_countertermContribution
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
    (data : ReferenceNuclearHeatFinitePartFullySpectralAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
      (data.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
        toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter)
      parameter :=
  data.toCollapsedBoundaryLimitsAssembly.hasDerivAt_finitePartLog parameter

/-- Standalone reference coefficient generated entirely from the spectral
counterterm, Duhamel and endpoint data. -/
theorem connectionCoefficient_eq_neg_logarithmicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartFullySpectralAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion)
    (parameter : Real) :
    P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
        relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
          toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter :
        Complex) :=
  data.toCollapsedBoundaryLimitsAssembly.
    connectionCoefficient_eq_neg_logarithmicTrace parameter

/-- Public fully spectral finite-part assembly checkpoint. -/
theorem reference_nuclear_heat_finite_part_fully_spectral_assembly_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (family : P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D.
      RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearHeatFinitePartFullySpectralAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion) :
    (∀ parameter,
      HasDerivAt data.countertermContribution
        (data.spectralBoundary.countertermVariation.derivative parameter)
        parameter) ∧
    (∀ parameter,
      data.spectralBoundary.countertermVariation.derivative parameter =
        P0EFTJanusProgramPIntrinsicNuclearTrace4D.intrinsicNuclearTrace
          (data.spectralBoundary.countertermVariation.derivativeTraceClass
            parameter)) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
            relativeHeatFinitePartLogDeterminant
              (family.finitePartFamily.finitePart current))
        (data.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
          toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter)
        parameter) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
            toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter :
          Complex)) :=
  ⟨data.spectralBoundary.hasDerivAt_countertermContribution,
    data.spectralBoundary.countertermVariation.derivative_eq_intrinsicTrace,
    data.hasDerivAt_finitePartLog,
    data.connectionCoefficient_eq_neg_logarithmicTrace⟩

end ReferenceNuclearHeatFinitePartFullySpectralAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartFullySpectralAssembly4D
end JanusFormal
