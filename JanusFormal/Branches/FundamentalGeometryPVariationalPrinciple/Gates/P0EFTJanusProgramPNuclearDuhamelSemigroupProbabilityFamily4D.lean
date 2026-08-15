import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelProbabilityAverage4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelSemigroupSlice4D

/-!
# Semigroup probability families for nuclear Duhamel traces

This file joins the two previous reductions.  At each parameter and positive
heat time, the Duhamel operator is represented by a probability average of
auxiliary slices

```text
K_left(a,t,s) (H'_a K_right(a,t,s)).
```

Every slice carries a nuclear expansion of `H'_a K_right`.  The semigroup law

```text
K_right(a,t,s) K_left(a,t,s) = K_full(a,t)
```

makes its trace independent of `s` after cyclic rotation.  Averaging over the
probability parameter therefore yields

```text
Tr(D_a(t)) = Tr(H'_a K_full(a,t)).
```

Only the original equality expressing the Duhamel trace as the slice average
is retained.  The constancy of the slice trace and the evaluation of the
average are derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelProbabilityAverage4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupSlice4D

variable {Slice E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- A parameterized Duhamel family whose simplex slices collapse by the heat
semigroup law. -/
structure NuclearDuhamelSemigroupProbabilityFamilyData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E)) where
  leftHeat : Real → HeatTime → Slice → E →L[Real] E
  rightHeat : Real → HeatTime → Slice → E →L[Real] E
  fullHeat : Real → HeatTime → E →L[Real] E
  insertion : Real → HeatTime → E →L[Real] E
  semigroup_eq : ∀ parameter time slice,
    (rightHeat parameter time slice).comp (leftHeat parameter time slice) =
      fullHeat parameter time
  insertionRightExpansion : ∀ parameter time slice,
    SummableRankOneOperatorExpansion
      ((insertion parameter time).comp (rightHeat parameter time slice))
  sliceTraceClass : ∀ parameter time slice,
    IntrinsicNuclearTraceData
      ((leftHeat parameter time slice).comp
        ((insertion parameter time).comp (rightHeat parameter time slice)))
  rotatedTraceClass : ∀ parameter time slice,
    IntrinsicNuclearTraceData
      (((insertion parameter time).comp (rightHeat parameter time slice)).comp
        (leftHeat parameter time slice))
  collapsedTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData
      ((insertion parameter time).comp (fullHeat parameter time))
  duhamelTrace_eq_sliceAverage : ∀ parameter time,
    nuclear.duhamelTrace parameter time =
      ∫ slice,
        intrinsicNuclearTrace (sliceTraceClass parameter time slice)
          ∂sliceMeasure

namespace NuclearDuhamelSemigroupProbabilityFamilyData

/-- The fixed-slice semigroup packet. -/
def sliceData
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (data : NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) (slice : Slice) :
    NuclearDuhamelSemigroupSliceData (E := E) where
  leftHeat := data.leftHeat parameter time slice
  rightHeat := data.rightHeat parameter time slice
  fullHeat := data.fullHeat parameter time
  insertion := data.insertion parameter time
  semigroup_eq := data.semigroup_eq parameter time slice
  insertionRightExpansion :=
    data.insertionRightExpansion parameter time slice
  sliceTraceClass := data.sliceTraceClass parameter time slice
  rotatedTraceClass := data.rotatedTraceClass parameter time slice
  collapsedTraceClass := data.collapsedTraceClass parameter time

/-- Conversion to the generic probability-average interface. -/
def toProbabilityAverage
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (data : NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear) :
    NuclearDuhamelProbabilityAverageData sliceMeasure nuclear where
  sliceOperator := fun parameter time slice =>
    (data.sliceData parameter time slice).sliceOperator
  collapsedOperator := fun parameter time =>
    (data.insertion parameter time).comp (data.fullHeat parameter time)
  sliceTraceClass := data.sliceTraceClass
  collapsedTraceClass := data.collapsedTraceClass
  sliceCyclicity := fun parameter time slice =>
    (data.sliceData parameter time slice).toSliceCyclicity
  duhamelTrace_eq_sliceAverage := data.duhamelTrace_eq_sliceAverage

/-- Every simplex slice has trace `Tr(H'_a K_full(a,t))`. -/
theorem sliceTrace_eq_insertionFullHeatTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (data : NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) (slice : Slice) :
    intrinsicNuclearTrace (data.sliceTraceClass parameter time slice) =
      intrinsicNuclearTrace (data.collapsedTraceClass parameter time) :=
  (data.sliceData parameter time slice).sliceTrace_eq_collapsedTrace

/-- The Duhamel trace collapses to the trace of the insertion times the full
heat operator. -/
theorem duhamelTrace_eq_insertionFullHeatTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (data : NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) :
    nuclear.duhamelTrace parameter time =
      intrinsicNuclearTrace (data.collapsedTraceClass parameter time) :=
  data.toProbabilityAverage.duhamelTrace_eq_collapsedTrace parameter time

/-- Public semigroup-probability Duhamel checkpoint. -/
theorem nuclear_duhamel_semigroup_probability_family_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (data : NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear) :
    (∀ parameter time slice,
      (data.rightHeat parameter time slice).comp
          (data.leftHeat parameter time slice) =
        data.fullHeat parameter time) ∧
    (∀ parameter time slice,
      intrinsicNuclearTrace (data.sliceTraceClass parameter time slice) =
        intrinsicNuclearTrace (data.collapsedTraceClass parameter time)) ∧
    (∀ parameter time,
      nuclear.duhamelTrace parameter time =
        intrinsicNuclearTrace (data.collapsedTraceClass parameter time)) :=
  ⟨data.semigroup_eq,
    data.sliceTrace_eq_insertionFullHeatTrace,
    data.duhamelTrace_eq_insertionFullHeatTrace⟩

end NuclearDuhamelSemigroupProbabilityFamilyData

end
end P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D
end JanusFormal
