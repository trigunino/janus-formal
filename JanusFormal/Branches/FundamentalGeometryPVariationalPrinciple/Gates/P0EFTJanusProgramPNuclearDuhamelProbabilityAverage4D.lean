import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelSliceCyclicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D

/-!
# Probability averages of cyclically equivalent Duhamel slices

The standard Duhamel insertion contains an auxiliary simplex parameter.  After
cyclically rotating the heat factors, every slice has the same intrinsic trace.
If the simplex parameter is integrated against a probability measure, its
average is therefore exactly that common trace.

This file isolates the argument

```text
Tr(D_a(t))
  = integral_slice Tr(D_a(t,s)) dμ(s)
  = Tr(D_collapsed,a(t)).
```

The second equality is derived from fixed-slice nuclear cyclicity and
`μ(univ) = 1`; it is not supplied as another scalar identity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelProbabilityAverage4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelSliceCyclicity4D

universe u v w

variable {Slice : Type u} {E : Type v}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- One Duhamel family represented as the probability average of slice
operators, all cyclically equivalent to one collapsed operator. -/
structure NuclearDuhamelProbabilityAverageData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E)) where
  sliceOperator : Real → HeatTime → Slice → E →L[Real] E
  collapsedOperator : Real → HeatTime → E →L[Real] E
  sliceTraceClass : ∀ parameter time slice,
    IntrinsicNuclearTraceData.{v, w} (sliceOperator parameter time slice)
  collapsedTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData.{v, w} (collapsedOperator parameter time)
  sliceCyclicity : ∀ parameter time slice,
    NuclearDuhamelSliceCyclicityData.{v, w}
      (sliceOperator parameter time slice)
      (collapsedOperator parameter time)
      (sliceTraceClass parameter time slice)
      (collapsedTraceClass parameter time)
  duhamelTrace_eq_sliceAverage : ∀ parameter time,
    nuclear.duhamelTrace parameter time =
      ∫ slice,
        intrinsicNuclearTrace (sliceTraceClass parameter time slice)
          ∂sliceMeasure

namespace NuclearDuhamelProbabilityAverageData

/-- Every auxiliary Duhamel slice has the collapsed intrinsic trace. -/
theorem sliceTrace_eq_collapsedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E)}
    (data : NuclearDuhamelProbabilityAverageData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) (slice : Slice) :
    intrinsicNuclearTrace (data.sliceTraceClass parameter time slice) =
      intrinsicNuclearTrace (data.collapsedTraceClass parameter time) :=
  P0EFTJanusProgramPNuclearDuhamelSliceCyclicity4D.NuclearDuhamelSliceCyclicityData.sliceTrace_eq_collapsedTrace
    (data.sliceCyclicity parameter time slice)

/-- The probability average of the slice traces equals their common collapsed
trace. -/
theorem sliceAverage_eq_collapsedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E)}
    (data : NuclearDuhamelProbabilityAverageData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) :
    (∫ slice,
      intrinsicNuclearTrace (data.sliceTraceClass parameter time slice)
        ∂sliceMeasure) =
      intrinsicNuclearTrace (data.collapsedTraceClass parameter time) := by
  calc
    (∫ slice,
        intrinsicNuclearTrace (data.sliceTraceClass parameter time slice)
          ∂sliceMeasure) =
      ∫ _slice : Slice,
        intrinsicNuclearTrace (data.collapsedTraceClass parameter time)
          ∂sliceMeasure := by
        apply integral_congr_ae
        filter_upwards [] with slice
        exact data.sliceTrace_eq_collapsedTrace parameter time slice
    _ = intrinsicNuclearTrace (data.collapsedTraceClass parameter time) := by
      simp

/-- The genuine Duhamel trace is the trace of the collapsed slice operator. -/
theorem duhamelTrace_eq_collapsedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E)}
    (data : NuclearDuhamelProbabilityAverageData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) :
    nuclear.duhamelTrace parameter time =
      intrinsicNuclearTrace (data.collapsedTraceClass parameter time) := by
  calc
    nuclear.duhamelTrace parameter time =
        ∫ slice,
          intrinsicNuclearTrace (data.sliceTraceClass parameter time slice)
            ∂sliceMeasure :=
      data.duhamelTrace_eq_sliceAverage parameter time
    _ = intrinsicNuclearTrace (data.collapsedTraceClass parameter time) :=
      data.sliceAverage_eq_collapsedTrace parameter time

/-- Public probability-averaged Duhamel checkpoint. -/
theorem nuclear_duhamel_probability_average_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E))
    (data : NuclearDuhamelProbabilityAverageData sliceMeasure nuclear) :
    (∀ parameter time slice,
      intrinsicNuclearTrace (data.sliceTraceClass parameter time slice) =
        intrinsicNuclearTrace (data.collapsedTraceClass parameter time)) ∧
    (∀ parameter time,
      (∫ slice,
        intrinsicNuclearTrace (data.sliceTraceClass parameter time slice)
          ∂sliceMeasure) =
        intrinsicNuclearTrace (data.collapsedTraceClass parameter time)) ∧
    (∀ parameter time,
      nuclear.duhamelTrace parameter time =
        intrinsicNuclearTrace (data.collapsedTraceClass parameter time)) :=
  ⟨data.sliceTrace_eq_collapsedTrace,
    data.sliceAverage_eq_collapsedTrace,
    data.duhamelTrace_eq_collapsedTrace⟩

end NuclearDuhamelProbabilityAverageData

end
end P0EFTJanusProgramPNuclearDuhamelProbabilityAverage4D
end JanusFormal
