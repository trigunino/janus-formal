import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartRealAxisSpectralAssembly4D

/-!
# Fully spectral reference assembly with canonical Mellin Schwarz symmetry

The Mellin heat kernel, its Bochner integral and the Gamma-normalized candidate
now have canonical Schwarz symmetry in the certified convergence half-plane.
Accordingly this reference assembly contains no explicit Mellin conjugation
field.

For each family parameter it stores only one common analytic domain and
analyticity of the zeta continuation and its reflected function.  The seed
identity, Schwarz reflection, real-axis germ, reality of `zeta'(0)` and the
standalone connection coefficient are derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartCanonicalSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open Filter Set
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenFullySpectralBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartRealAxisSpectralAssembly4D

variable {Slice ShortCutoff LongCutoff E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Fully spectral standalone reference data with canonical Mellin Schwarz
symmetry and one reflected analytic continuation domain. -/
structure ReferenceNuclearHeatFinitePartCanonicalSchwarzAssemblyData
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
  zetaCanonicalSchwarz : ∀ parameter,
    RelativeHeatMellinZetaCanonicalSchwarzReflectionData
      (family.continuation parameter)

namespace ReferenceNuclearHeatFinitePartCanonicalSchwarzAssemblyData

/-- Convert canonical Schwarz reflection to the real-axis spectral frontend. -/
def toRealAxisSpectralAssembly
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartCanonicalSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion) :
    ReferenceNuclearHeatFinitePartRealAxisSpectralAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  spectralBoundary := data.spectralBoundary
  logDeterminant_eq := data.logDeterminant_eq
  zetaRealAxis := fun parameter =>
    (data.zetaCanonicalSchwarz parameter).toRealAxisReality

/-- Reality of every regularized derivative follows canonically. -/
theorem zetaPrimeAtZero_im_eq_zero
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartCanonicalSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion)
    (parameter : Real) :
    (family.zetaPrimeAtZero parameter).im = 0 :=
  data.toRealAxisSpectralAssembly.zetaPrimeAtZero_im_eq_zero parameter

/-- Standalone reference coefficient generated without a Mellin symmetry
field. -/
theorem connectionCoefficient_eq_neg_logarithmicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartCanonicalSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion)
    (parameter : Real) :
    P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
        relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
          toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter :
        Complex) :=
  data.toRealAxisSpectralAssembly.
    connectionCoefficient_eq_neg_logarithmicTrace parameter

/-- Public canonical-Schwarz reference assembly checkpoint. -/
theorem reference_nuclear_heat_finite_part_canonical_schwarz_assembly_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearHeatFinitePartCanonicalSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter family
        shortTimeRegion longTimeRegion) :
    (∀ parameter,
      Set.EqOn (family.continuation parameter).zeta
        (P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D.
          schwarzReflect (family.continuation parameter).zeta)
        (data.zetaCanonicalSchwarz parameter).domain) ∧
    (∀ parameter,
      (family.zetaPrimeAtZero parameter).im = 0) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
            toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter :
          Complex)) :=
  ⟨fun parameter =>
      (data.zetaCanonicalSchwarz parameter).zeta_eqOn_schwarz_domain,
    data.zetaPrimeAtZero_im_eq_zero,
    data.connectionCoefficient_eq_neg_logarithmicTrace⟩

end ReferenceNuclearHeatFinitePartCanonicalSchwarzAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartCanonicalSchwarzAssembly4D
end JanusFormal
