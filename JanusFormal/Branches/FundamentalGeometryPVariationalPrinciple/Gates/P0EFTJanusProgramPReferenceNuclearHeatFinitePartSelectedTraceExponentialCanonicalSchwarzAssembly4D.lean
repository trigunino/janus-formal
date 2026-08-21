import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimits4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceCanonicalSchwarzAssembly4D

/-!
# Selected-trace canonical-Schwarz assembly from exponential long-time decay

The selected-reference finite-part assembly previously accepted the terminal
long-time convergence as part of its endpoint packet.  This frontend replaces
that convergence by the concrete spectral estimate

```text
‖terminalPrimitive(R)‖ ≤ C exp (-c T(R)),
0 < c,
T(R) → +∞.
```

The exponential envelope generates the vector-valued limit, after which the
existing selected-trace and canonical-Schwarz chain derives

```text
finitePartLogDerivative(a) = selectedTrace.trace(a),
T_reference(a) = -selectedTrace.trace(a).
```

The H14 two-sided norm gap is not silently reinterpreted as positivity of the
heat generator.  The positive decay rate belongs to the genuine reference
spectral estimate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssembly4D

set_option autoImplicit false
noncomputable section

open Filter Set Topology MeasureTheory
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimits4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

universe e i s a b

variable {Slice : Type s} {ShortCutoff : Type a} {LongCutoff : Type b}
  {E : Type e}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Standalone reference data with a selected logarithmic trace and a generated
long-time terminal limit. -/
structure ReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssemblyData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i}
      referenceOperator)
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real) where
  nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)
  countertermContribution : Real → Real
  spectralBoundary :
    ReferenceNuclearDuhamelGreenSelectedTraceExponentialBoundaryLimitsData.{e, i, s, a, b}
      sliceMeasure shortCutoffFilter longCutoffFilter nuclear
        countertermContribution shortTimeRegion longTimeRegion
          referenceOperator selectedTrace
  logDeterminant_eq : ∀ parameter,
    relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter +
        spectralBoundary.toSelectedTraceBoundaryLimits.toFullySpectralBoundaryLimits.shortTime.weighted.toWeightedHeatTraceVariation.contribution
            parameter +
          spectralBoundary.toSelectedTraceBoundaryLimits.toFullySpectralBoundaryLimits.longTime.weighted.toWeightedHeatTraceVariation.contribution
              parameter
  zetaCanonicalSchwarz : ∀ parameter,
    RelativeHeatMellinZetaCanonicalSchwarzReflectionData
      (family.continuation parameter)

namespace ReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssemblyData

/-- Generate the terminal primitive limit and recover the selected-trace
canonical-Schwarz assembly. -/
def toSelectedTraceCanonicalSchwarzAssembly
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeRegion) :
    ReferenceNuclearHeatFinitePartSelectedTraceCanonicalSchwarzAssemblyData
      (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
        referenceOperator selectedTrace family shortTimeRegion longTimeRegion where
  nuclear := data.nuclear
  countertermContribution := data.countertermContribution
  spectralBoundary := data.spectralBoundary.toSelectedTraceBoundaryLimits
  logDeterminant_eq := data.logDeterminant_eq
  zetaCanonicalSchwarz := data.zetaCanonicalSchwarz

/-- The exponential estimate generates the terminal primitive limit at every
parameter. -/
theorem terminalPrimitive_tendsto_zero
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    Tendsto (data.spectralBoundary.longBoundaryDecay parameter).terminalPrimitive
      longCutoffFilter (𝓝 0) :=
  data.spectralBoundary.terminalPrimitive_tendsto_zero parameter

/-- The endpoint scalar is still definitionally the selected chart trace. -/
@[simp] theorem generatedLogarithmicTrace_eq_selectedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    data.toSelectedTraceCanonicalSchwarzAssembly.toCanonicalSchwarzAssembly.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace
        parameter =
      selectedTrace.trace parameter :=
  data.toSelectedTraceCanonicalSchwarzAssembly.generatedLogarithmicTrace_eq_selectedTrace
    parameter

/-- Canonical Schwarz reflection forces reality of the regularized derivative. -/
theorem zetaPrimeAtZero_im_eq_zero
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    (family.zetaPrimeAtZero parameter).im = 0 :=
  data.toSelectedTraceCanonicalSchwarzAssembly.zetaPrimeAtZero_im_eq_zero
    parameter

/-- The standalone reference coefficient is generated from the selected trace
and the exponential long-time estimate. -/
theorem connectionCoefficient_eq_neg_selectedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {referenceOperator : Real → E →L[Real] E}
    {selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator}
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeRegion)
    (parameter : Real) :
    relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(selectedTrace.trace parameter : Complex) :=
  data.toSelectedTraceCanonicalSchwarzAssembly.connectionCoefficient_eq_neg_selectedTrace
    parameter

/-- Public exponential selected-trace canonical-Schwarz checkpoint. -/
theorem reference_nuclear_heat_finite_part_selected_trace_exponential_canonical_schwarz_assembly_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (referenceOperator : Real → E →L[Real] E)
    (selectedTrace : IntrinsicLogarithmicDerivativeTraceData.{e, i} referenceOperator)
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data :
      ReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssemblyData
        (E := E) sliceMeasure shortCutoffFilter longCutoffFilter
          referenceOperator selectedTrace family shortTimeRegion longTimeRegion) :
    (∀ parameter,
      Tendsto (data.spectralBoundary.longBoundaryDecay parameter).terminalPrimitive
        longCutoffFilter (𝓝 0)) ∧
    (∀ parameter,
      Set.EqOn (family.continuation parameter).zeta
        (schwarzReflect (family.continuation parameter).zeta)
        (data.zetaCanonicalSchwarz parameter).domain) ∧
    (∀ parameter,
      (family.zetaPrimeAtZero parameter).im = 0) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(selectedTrace.trace parameter : Complex)) :=
  ⟨data.terminalPrimitive_tendsto_zero,
    fun parameter =>
      (data.zetaCanonicalSchwarz parameter).zeta_eqOn_schwarz_domain,
    data.zetaPrimeAtZero_im_eq_zero,
    data.connectionCoefficient_eq_neg_selectedTrace⟩

end ReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssemblyData

end
end P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceExponentialCanonicalSchwarzAssembly4D
end JanusFormal
