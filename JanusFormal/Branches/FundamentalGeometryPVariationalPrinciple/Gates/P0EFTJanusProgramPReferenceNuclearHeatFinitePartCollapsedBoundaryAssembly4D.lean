import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenCollapsedBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartBoundaryAssembly4D

/-!
# Reference finite parts from semigroup-collapsed Duhamel spectra

This frontend supplies the short- and long-time operator integrals from
rank-one expansions of `H'_a K_a(t)`.  The auxiliary Duhamel simplex average is
first eliminated by nuclear cyclicity, the heat semigroup law and probability
normalization.  Consequently no spectral expansion of the averaged Duhamel
operator is required.

The remaining chain is

```text
Duhamel slices
  -> cyclic semigroup collapse to H' K_t
  -> rank-one regional integrals
  -> short/long boundary matching
  -> global logarithmic derivative operator
  -> intrinsic trace
  -> finite-part derivative
  -> standalone reference zeta coefficient.
```
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryAssembly4D

set_option autoImplicit false
noncomputable section

open MeasureTheory

open Set
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenCollapsedBoundary4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartBoundaryAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

universe e i s

variable {Slice : Type s} {E : Type e}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Complete standalone reference packet from semigroup-collapsed rank-one
Duhamel data. -/
structure ReferenceNuclearHeatFinitePartCollapsedBoundaryAssemblyData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real) where
  nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)
  countertermContribution : Real → Real
  collapsedBoundary :
    ReferenceNuclearDuhamelGreenCollapsedBoundaryData sliceMeasure nuclear
      shortTimeRegion longTimeRegion
  hasDerivAt_counterterm : ∀ parameter,
    HasDerivAt countertermContribution
      (collapsedBoundary.countertermDerivative parameter) parameter
  logDeterminant_eq : ∀ parameter,
    relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter +
        collapsedBoundary.shortTime.weighted.toWeightedHeatTraceVariation.contribution parameter +
          collapsedBoundary.longTime.weighted.toWeightedHeatTraceVariation.contribution parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceNuclearHeatFinitePartCollapsedBoundaryAssemblyData

/-- Convert the collapsed spectral data to the existing boundary assembly only
after the Duhamel average and regional trace integrals have been derived. -/
def toBoundaryAssembly
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartCollapsedBoundaryAssemblyData
      (E := E) sliceMeasure family shortTimeRegion longTimeRegion) :
    ReferenceNuclearHeatFinitePartBoundaryAssemblyData
      (E := E) family shortTimeRegion longTimeRegion where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  boundaryMatching := data.collapsedBoundary.toBoundaryMatching
  hasDerivAt_counterterm := data.hasDerivAt_counterterm
  logDeterminant_eq := data.logDeterminant_eq
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- The finite-part logarithmic derivative is the intrinsic trace of the
logarithmic insertion/Green operator. -/
theorem hasDerivAt_finitePartLog
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartCollapsedBoundaryAssemblyData
      (E := E) sliceMeasure family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
      (data.collapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter)
      parameter :=
  data.toBoundaryAssembly.hasDerivAt_finitePartLog parameter

/-- Standalone reference zeta coefficient obtained without an expansion of the
averaged Duhamel operator. -/
theorem connectionCoefficient_eq_neg_logarithmicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearHeatFinitePartCollapsedBoundaryAssemblyData
      (E := E) sliceMeasure family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.collapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace
          parameter : Complex) :=
  data.toBoundaryAssembly.connectionCoefficient_eq_neg_logarithmicTrace
    parameter

/-- Public collapsed finite-part assembly checkpoint. -/
theorem reference_nuclear_heat_finite_part_collapsed_boundary_assembly_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearHeatFinitePartCollapsedBoundaryAssemblyData
      (E := E) sliceMeasure family shortTimeRegion longTimeRegion) :
    (∀ parameter time,
      data.nuclear.duhamelTrace parameter time =
        P0EFTJanusProgramPIntrinsicNuclearTrace4D.intrinsicNuclearTrace
          (data.collapsedBoundary.shortTime.semigroup.collapsedTraceClass
            parameter time)) ∧
    (∀ parameter,
      (∫ time in shortTimeRegion,
        P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData.extendedDuhamelTrace
          data.nuclear parameter time) =
          P0EFTJanusProgramPIntrinsicNuclearTrace4D.intrinsicNuclearTrace
            (data.collapsedBoundary.shortTime.integratedTraceClass parameter)) ∧
    (∀ parameter,
      (∫ time in longTimeRegion,
        P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData.extendedDuhamelTrace
          data.nuclear parameter time) =
          P0EFTJanusProgramPIntrinsicNuclearTrace4D.intrinsicNuclearTrace
            (data.collapsedBoundary.longTime.integratedTraceClass parameter)) ∧
    (∀ parameter,
      HasDerivAt
        (fun current =>
          relativeHeatFinitePartLogDeterminant
              (family.finitePartFamily.finitePart current))
        (data.collapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace
          parameter) parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.collapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace
            parameter : Complex)) :=
  ⟨data.collapsedBoundary.shortTime.semigroup.duhamelTrace_eq_insertionFullHeatTrace,
    data.collapsedBoundary.shortTimeIntegral_eq_trace,
    data.collapsedBoundary.longTimeIntegral_eq_trace,
    data.hasDerivAt_finitePartLog,
    data.connectionCoefficient_eq_neg_logarithmicTrace⟩

end ReferenceNuclearHeatFinitePartCollapsedBoundaryAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryAssembly4D
end JanusFormal
