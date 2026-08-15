import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelCollapsedRankOneIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearDuhamelGreenBoundaryMatching4D

/-!
# Green boundary matching from collapsed Duhamel spectral integrals

This file combines the semigroup-probability collapse with the short/long
boundary argument.  The regional operator integrals are built from spectral
expansions of the simpler operators

```text
H'_a K_a(t)
```

rather than from expansions of the auxiliary-parameter averaged Duhamel
operator.  Nuclear cyclicity and the heat semigroup law first establish

```text
Tr(D_a(t)) = Tr(H'_a K_a(t)).
```

The collapsed rank-one coefficients are then integrated separately on the
short- and long-time regions.  Their operator-valued integrals meet through the
same boundary operator and generate the full Duhamel--Green trace identity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelGreenCollapsedBoundary4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelCollapsedRankOneIntegral4D
open P0EFTJanusProgramPReferenceNuclearDuhamelGreenBoundaryMatching4D

variable {Slice E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Reference short/long matching data built from semigroup-collapsed spectral
expansions. -/
structure ReferenceNuclearDuhamelGreenCollapsedBoundaryData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (shortTimeRegion longTimeRegion : Set Real) where
  countertermOperator : Real → E →L[Real] E
  countertermTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData (countertermOperator parameter)
  countertermDerivative : Real → Real
  countertermDerivative_eq_trace : ∀ parameter,
    countertermDerivative parameter =
      intrinsicNuclearTrace (countertermTraceClass parameter)
  shortTime : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
    shortTimeRegion
  longTime : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
    longTimeRegion
  countertermMinusShortTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData
      (countertermOperator parameter - shortTime.integratedOperator parameter)
  totalTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData
      ((countertermOperator parameter - shortTime.integratedOperator parameter) -
        longTime.integratedOperator parameter)
  logarithmicDerivativeOperator : Real → E →L[Real] E
  logarithmicDerivativeTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData (logarithmicDerivativeOperator parameter)
  matchingOperator : Real → E →L[Real] E
  shortBoundaryIdentity : ∀ parameter,
    countertermOperator parameter - shortTime.integratedOperator parameter =
      logarithmicDerivativeOperator parameter + matchingOperator parameter
  longBoundaryIdentity : ∀ parameter,
    longTime.integratedOperator parameter = matchingOperator parameter

namespace ReferenceNuclearDuhamelGreenCollapsedBoundaryData

/-- Conversion to the generic short/long boundary matching interface. -/
def toBoundaryMatching
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenCollapsedBoundaryData sliceMeasure
      nuclear shortTimeRegion longTimeRegion) :
    ReferenceNuclearDuhamelGreenBoundaryMatchingData nuclear
      shortTimeRegion longTimeRegion where
  countertermOperator := data.countertermOperator
  countertermTraceClass := data.countertermTraceClass
  countertermDerivative := data.countertermDerivative
  countertermDerivative_eq_trace := data.countertermDerivative_eq_trace
  shortTime := data.shortTime.toOperatorIntegral
  longTime := data.longTime.toOperatorIntegral
  countertermMinusShortTraceClass := data.countertermMinusShortTraceClass
  totalTraceClass := data.totalTraceClass
  logarithmicDerivativeOperator := data.logarithmicDerivativeOperator
  logarithmicDerivativeTraceClass := data.logarithmicDerivativeTraceClass
  matchingOperator := data.matchingOperator
  shortBoundaryIdentity := data.shortBoundaryIdentity
  longBoundaryIdentity := data.longBoundaryIdentity

/-- Short-time trace integration is obtained from the collapsed insertion/heat
expansion. -/
theorem shortTimeIntegral_eq_trace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenCollapsedBoundaryData sliceMeasure
      nuclear shortTimeRegion longTimeRegion)
    (parameter : Real) :
    (∫ time in shortTimeRegion,
      nuclear.extendedDuhamelTrace parameter time) =
        intrinsicNuclearTrace (data.shortTime.integratedTraceClass parameter) :=
  data.shortTime.scalarIntegral_eq_intrinsicTrace parameter

/-- Long-time trace integration is obtained from the collapsed insertion/heat
expansion. -/
theorem longTimeIntegral_eq_trace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenCollapsedBoundaryData sliceMeasure
      nuclear shortTimeRegion longTimeRegion)
    (parameter : Real) :
    (∫ time in longTimeRegion,
      nuclear.extendedDuhamelTrace parameter time) =
        intrinsicNuclearTrace (data.longTime.integratedTraceClass parameter) :=
  data.longTime.scalarIntegral_eq_intrinsicTrace parameter

/-- Full integrated Duhamel--Green trace formula from semigroup collapse,
rank-one integration and boundary cancellation. -/
theorem integratedDuhamel_eq_logarithmicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceNuclearDuhamelGreenCollapsedBoundaryData sliceMeasure
      nuclear shortTimeRegion longTimeRegion)
    (parameter : Real) :
    data.countertermDerivative parameter -
        (∫ time in shortTimeRegion,
          nuclear.extendedDuhamelTrace parameter time) -
        (∫ time in longTimeRegion,
          nuclear.extendedDuhamelTrace parameter time) =
      data.toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter :=
  data.toBoundaryMatching.integratedDuhamel_eq_logarithmicTrace parameter

/-- Public collapsed-boundary checkpoint. -/
theorem reference_nuclear_duhamel_green_collapsed_boundary_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceNuclearDuhamelGreenCollapsedBoundaryData sliceMeasure
      nuclear shortTimeRegion longTimeRegion) :
    (∀ parameter time,
      nuclear.duhamelTrace parameter time =
        intrinsicNuclearTrace
          (data.shortTime.semigroup.collapsedTraceClass parameter time)) ∧
    (∀ parameter,
      (∫ time in shortTimeRegion,
        nuclear.extendedDuhamelTrace parameter time) =
          intrinsicNuclearTrace
            (data.shortTime.integratedTraceClass parameter)) ∧
    (∀ parameter,
      (∫ time in longTimeRegion,
        nuclear.extendedDuhamelTrace parameter time) =
          intrinsicNuclearTrace
            (data.longTime.integratedTraceClass parameter)) ∧
    (∀ parameter,
      data.countertermOperator parameter -
          data.shortTime.integratedOperator parameter =
        data.logarithmicDerivativeOperator parameter +
          data.matchingOperator parameter) ∧
    (∀ parameter,
      data.longTime.integratedOperator parameter =
        data.matchingOperator parameter) ∧
    (∀ parameter,
      data.countertermDerivative parameter -
          (∫ time in shortTimeRegion,
            nuclear.extendedDuhamelTrace parameter time) -
          (∫ time in longTimeRegion,
            nuclear.extendedDuhamelTrace parameter time) =
        data.toBoundaryMatching.toOperatorIdentity.logarithmicTrace parameter) :=
  ⟨data.shortTime.semigroup.duhamelTrace_eq_insertionFullHeatTrace,
    data.shortTimeIntegral_eq_trace,
    data.longTimeIntegral_eq_trace,
    data.shortBoundaryIdentity,
    data.longBoundaryIdentity,
    data.integratedDuhamel_eq_logarithmicTrace⟩

end ReferenceNuclearDuhamelGreenCollapsedBoundaryData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelGreenCollapsedBoundary4D
end JanusFormal
