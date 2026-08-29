import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaKernelSchwarzReflection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartIntegralSchwarzAssembly4D

/-!
# Fully spectral reference assembly from pointwise Mellin-kernel symmetry

This frontend replaces the full unnormalized Mellin-integral conjugation field
by the lower-level compatibility of complex conjugation with the Bochner
integral of the pointwise reflected kernel.  Pointwise kernel symmetry, Mellin
integral symmetry, Gamma normalization, Schwarz continuation and reality of the
regularized derivative are all derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartKernelSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open Filter Set
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaKernelSchwarzReflection4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenFullySpectralBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartIntegralSchwarzAssembly4D

variable {Slice ShortCutoff LongCutoff E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Fully spectral standalone reference data with pointwise Mellin-kernel
Schwarz packets. -/
structure ReferenceNuclearHeatFinitePartKernelSchwarzAssemblyData
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
  zetaKernelSchwarz : ∀ parameter,
    RelativeHeatMellinZetaKernelSchwarzReflectionData
      (family.continuation parameter)

namespace ReferenceNuclearHeatFinitePartKernelSchwarzAssemblyData

/-- Convert pointwise kernel symmetry to the integral-Schwarz assembly. -/
def toIntegralSchwarzAssembly
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartKernelSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion) :
    ReferenceNuclearHeatFinitePartIntegralSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  spectralBoundary := data.spectralBoundary
  logDeterminant_eq := data.logDeterminant_eq
  zetaIntegralSchwarz := fun parameter =>
    (data.zetaKernelSchwarz parameter).toIntegralSchwarzReflection

/-- Reality of every regularized derivative follows from pointwise kernel
symmetry and map-integral compatibility. -/
theorem zetaPrimeAtZero_im_eq_zero
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartKernelSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion)
    (parameter : Real) :
    (family.zetaPrimeAtZero parameter).im = 0 :=
  data.toIntegralSchwarzAssembly.zetaPrimeAtZero_im_eq_zero parameter

/-- Standalone reference coefficient from pointwise Mellin-kernel symmetry. -/
theorem connectionCoefficient_eq_neg_logarithmicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartKernelSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion)
    (parameter : Real) :
    P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
        relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
          toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter :
        Complex) :=
  data.toIntegralSchwarzAssembly.
    connectionCoefficient_eq_neg_logarithmicTrace parameter

/-- Public kernel-Schwarz reference assembly checkpoint. -/
theorem reference_nuclear_heat_finite_part_kernel_schwarz_assembly_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearHeatFinitePartKernelSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion) :
    (∀ parameter spectral time,
      P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
          relativeHeatMellinKernel
            (family.finitePartFamily.heatTrace parameter) spectral time =
        Complex.conj
          (P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
            relativeHeatMellinKernel
              (family.finitePartFamily.heatTrace parameter)
              (Complex.conj spectral) time)) ∧
    (∀ parameter,
      (family.zetaPrimeAtZero parameter).im = 0) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
            toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter :
          Complex)) :=
  ⟨fun parameter =>
      P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D.
        relativeHeatMellinKernel_schwarz
          (family.finitePartFamily.heatTrace parameter),
    data.zetaPrimeAtZero_im_eq_zero,
    data.connectionCoefficient_eq_neg_logarithmicTrace⟩

end ReferenceNuclearHeatFinitePartKernelSchwarzAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartKernelSchwarzAssembly4D
end JanusFormal
