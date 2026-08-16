import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaIntegralSchwarzReflection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartGeneratedSchwarzAssembly4D

/-!
# Fully spectral reference assembly from Mellin-integral conjugation

This frontend removes Gamma conjugation from the per-reference data.  For every
family parameter it stores only Schwarz symmetry of the unnormalized Mellin
integral.  The canonical Gamma identity supplies normalization, and all later
reflection, reality and connection statements are derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartIntegralSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open Filter Set
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaIntegralSchwarzReflection4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenFullySpectralBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartGeneratedSchwarzAssembly4D

variable {Slice ShortCutoff LongCutoff E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Fully spectral standalone reference data whose only heat-dependent Schwarz
input is the unnormalized Mellin-integral symmetry. -/
structure ReferenceNuclearHeatFinitePartIntegralSchwarzAssemblyData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (family : RelativeHeatMellinZetaFamilyData)
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
  zetaIntegralSchwarz : ∀ parameter,
    RelativeHeatMellinZetaIntegralSchwarzReflectionData
      (family.continuation parameter)

namespace ReferenceNuclearHeatFinitePartIntegralSchwarzAssemblyData

/-- Convert unnormalized Mellin symmetry to the generated Schwarz assembly. -/
def toGeneratedSchwarzAssembly
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartIntegralSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion) :
    ReferenceNuclearHeatFinitePartGeneratedSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  spectralBoundary := data.spectralBoundary
  logDeterminant_eq := data.logDeterminant_eq
  zetaGeneratedSchwarz := fun parameter =>
    (data.zetaIntegralSchwarz parameter).toGeneratedSchwarzReflection

/-- Reality of every regularized derivative follows from unnormalized Mellin
conjugation. -/
theorem zetaPrimeAtZero_im_eq_zero
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartIntegralSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion)
    (parameter : Real) :
    (family.zetaPrimeAtZero parameter).im = 0 :=
  data.toGeneratedSchwarzAssembly.zetaPrimeAtZero_im_eq_zero parameter

/-- Standalone reference coefficient generated from operator spectra and the
unnormalized Mellin integral. -/
theorem connectionCoefficient_eq_neg_logarithmicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartIntegralSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion)
    (parameter : Real) :
    P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
        relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
          toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter :
        Complex) :=
  data.toGeneratedSchwarzAssembly.
    connectionCoefficient_eq_neg_logarithmicTrace parameter

/-- Public integral-Schwarz reference assembly checkpoint. -/
theorem reference_nuclear_heat_finite_part_integral_schwarz_assembly_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearHeatFinitePartIntegralSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion) :
    (∀ parameter spectral,
      P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
          relativeHeatMellinIntegral
            (family.finitePartFamily.heatTrace parameter) spectral =
        Complex.conj
          (P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
            relativeHeatMellinIntegral
              (family.finitePartFamily.heatTrace parameter)
              (Complex.conj spectral))) ∧
    (∀ parameter,
      (family.zetaPrimeAtZero parameter).im = 0) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
            toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter :
          Complex)) :=
  ⟨fun parameter =>
      (data.zetaIntegralSchwarz parameter).mellinIntegralSchwarz.
        mellinIntegral_schwarz,
    data.zetaPrimeAtZero_im_eq_zero,
    data.connectionCoefficient_eq_neg_logarithmicTrace⟩

end ReferenceNuclearHeatFinitePartIntegralSchwarzAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartIntegralSchwarzAssembly4D
end JanusFormal
