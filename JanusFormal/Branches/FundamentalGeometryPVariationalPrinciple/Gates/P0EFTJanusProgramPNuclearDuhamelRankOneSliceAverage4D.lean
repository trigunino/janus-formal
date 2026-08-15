import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D

/-!
# Rank-one construction of Duhamel slice averages

A Duhamel operator is an average over an auxiliary simplex parameter.  The
semigroup-probability layer previously accepted the scalar equality

```text
Tr(D_a(t)) = integral_slice Tr(D_a(t,s)) dμ(s).
```

This file derives that identity from a common rank-one spectral frame.  The
left and right vectors are independent of the simplex parameter while the
scalar coefficients vary with it:

```text
D_a(t,s)
  = sum_i coefficient(a,t,s,i) rankOne(left(a,t,i), right(a,t,i)).
```

Averaging the coefficients gives a rank-one expansion of the genuine Duhamel
operator.  One certified exchange of the simplex integral with the trace
series then proves that intrinsic trace commutes with the average.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelRankOneSliceAverage4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D

universe u

variable {Slice E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E]

/-- Common rank-one spectral construction of a probability-averaged Duhamel
operator. -/
structure NuclearDuhamelRankOneSliceAverageData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E)) where
  sliceOperator : Real → HeatTime → Slice → E →L[Real] E
  sliceTraceClass : ∀ parameter time slice,
    IntrinsicNuclearTraceData (sliceOperator parameter time slice)
  Index : Type u
  coefficient : Real → HeatTime → Slice → Index → Real
  leftVector : Real → HeatTime → Index → E
  rightVector : Real → HeatTime → Index → E
  slice_nuclearNorm_summable : ∀ parameter time slice,
    Summable (fun index =>
      |coefficient parameter time slice index| *
        ‖leftVector parameter time index‖ *
          ‖rightVector parameter time index‖)
  slice_trace_summable : ∀ parameter time slice,
    Summable (fun index =>
      coefficient parameter time slice index *
        inner Real (leftVector parameter time index)
          (rightVector parameter time index))
  slice_operator_eq_tsum : ∀ parameter time slice,
    sliceOperator parameter time slice = ∑' index,
      coefficient parameter time slice index •
        InnerProductSpace.rankOne Real
          (leftVector parameter time index)
          (rightVector parameter time index)
  averagedCoefficient : Real → HeatTime → Index → Real
  averagedCoefficient_eq : ∀ parameter time index,
    averagedCoefficient parameter time index =
      ∫ slice, coefficient parameter time slice index ∂sliceMeasure
  duhamel_nuclearNorm_summable : ∀ parameter time,
    Summable (fun index =>
      |averagedCoefficient parameter time index| *
        ‖leftVector parameter time index‖ *
          ‖rightVector parameter time index‖)
  duhamel_trace_summable : ∀ parameter time,
    Summable (fun index =>
      averagedCoefficient parameter time index *
        inner Real (leftVector parameter time index)
          (rightVector parameter time index))
  duhamel_operator_eq_tsum : ∀ parameter time,
    nuclear.duhamelOperator parameter time = ∑' index,
      averagedCoefficient parameter time index •
        InnerProductSpace.rankOne Real
          (leftVector parameter time index)
          (rightVector parameter time index)
  trace_average_interchange : ∀ parameter time,
    (∫ slice,
      ∑' index,
        coefficient parameter time slice index *
          inner Real (leftVector parameter time index)
            (rightVector parameter time index)
        ∂sliceMeasure) =
      ∑' index,
        averagedCoefficient parameter time index *
          inner Real (leftVector parameter time index)
            (rightVector parameter time index)

namespace NuclearDuhamelRankOneSliceAverageData

/-- Rank-one expansion of one auxiliary slice. -/
def sliceExpansion
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (data : NuclearDuhamelRankOneSliceAverageData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) (slice : Slice) :
    SummableRankOneOperatorExpansion
      (data.sliceOperator parameter time slice) where
  Index := data.Index
  coefficient := data.coefficient parameter time slice
  leftVector := data.leftVector parameter time
  rightVector := data.rightVector parameter time
  summable_nuclearNorm :=
    data.slice_nuclearNorm_summable parameter time slice
  trace_summable := data.slice_trace_summable parameter time slice
  operator_eq_tsum := data.slice_operator_eq_tsum parameter time slice

/-- Rank-one expansion of the genuine averaged Duhamel operator. -/
def duhamelExpansion
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (data : NuclearDuhamelRankOneSliceAverageData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) :
    SummableRankOneOperatorExpansion
      (nuclear.duhamelOperator parameter time) where
  Index := data.Index
  coefficient := data.averagedCoefficient parameter time
  leftVector := data.leftVector parameter time
  rightVector := data.rightVector parameter time
  summable_nuclearNorm := data.duhamel_nuclearNorm_summable parameter time
  trace_summable := data.duhamel_trace_summable parameter time
  operator_eq_tsum := data.duhamel_operator_eq_tsum parameter time

/-- Intrinsic trace of one slice in the common spectral coordinates. -/
theorem sliceTrace_eq_tsum
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (data : NuclearDuhamelRankOneSliceAverageData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) (slice : Slice) :
    intrinsicNuclearTrace (data.sliceTraceClass parameter time slice) =
      ∑' index,
        data.coefficient parameter time slice index *
          inner Real (data.leftVector parameter time index)
            (data.rightVector parameter time index) := by
  exact
    ((data.sliceTraceClass parameter time slice).expansionTrace_eq
      (data.sliceExpansion parameter time slice)).symm

/-- Intrinsic trace of the genuine Duhamel operator in the averaged spectral
coordinates. -/
theorem duhamelTrace_eq_tsum
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (data : NuclearDuhamelRankOneSliceAverageData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) :
    nuclear.duhamelTrace parameter time =
      ∑' index,
        data.averagedCoefficient parameter time index *
          inner Real (data.leftVector parameter time index)
            (data.rightVector parameter time index) := by
  exact
    ((nuclear.duhamelTraceClass parameter time).expansionTrace_eq
      (data.duhamelExpansion parameter time)).symm

/-- The probability average of slice traces is the averaged spectral trace
series. -/
theorem sliceTraceAverage_eq_tsum
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (data : NuclearDuhamelRankOneSliceAverageData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) :
    (∫ slice,
      intrinsicNuclearTrace (data.sliceTraceClass parameter time slice)
        ∂sliceMeasure) =
      ∑' index,
        data.averagedCoefficient parameter time index *
          inner Real (data.leftVector parameter time index)
            (data.rightVector parameter time index) := by
  calc
    (∫ slice,
        intrinsicNuclearTrace (data.sliceTraceClass parameter time slice)
          ∂sliceMeasure) =
      ∫ slice,
        ∑' index,
          data.coefficient parameter time slice index *
            inner Real (data.leftVector parameter time index)
              (data.rightVector parameter time index)
          ∂sliceMeasure := by
        apply integral_congr_ae
        filter_upwards [] with slice
        exact data.sliceTrace_eq_tsum parameter time slice
    _ = ∑' index,
        data.averagedCoefficient parameter time index *
          inner Real (data.leftVector parameter time index)
            (data.rightVector parameter time index) :=
      data.trace_average_interchange parameter time

/-- Intrinsic trace commutes with the rank-one Duhamel probability average. -/
theorem duhamelTrace_eq_sliceAverage
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    (data : NuclearDuhamelRankOneSliceAverageData sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) :
    nuclear.duhamelTrace parameter time =
      ∫ slice,
        intrinsicNuclearTrace (data.sliceTraceClass parameter time slice)
          ∂sliceMeasure := by
  calc
    nuclear.duhamelTrace parameter time =
      ∑' index,
        data.averagedCoefficient parameter time index *
          inner Real (data.leftVector parameter time index)
            (data.rightVector parameter time index) :=
      data.duhamelTrace_eq_tsum parameter time
    _ = ∫ slice,
        intrinsicNuclearTrace (data.sliceTraceClass parameter time slice)
          ∂sliceMeasure :=
      (data.sliceTraceAverage_eq_tsum parameter time).symm

/-- Public rank-one slice-average checkpoint. -/
theorem nuclear_duhamel_rank_one_slice_average_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (data : NuclearDuhamelRankOneSliceAverageData sliceMeasure nuclear) :
    (∀ parameter time slice,
      intrinsicNuclearTrace (data.sliceTraceClass parameter time slice) =
        ∑' index,
          data.coefficient parameter time slice index *
            inner Real (data.leftVector parameter time index)
              (data.rightVector parameter time index)) ∧
    (∀ parameter time,
      nuclear.duhamelTrace parameter time =
        ∑' index,
          data.averagedCoefficient parameter time index *
            inner Real (data.leftVector parameter time index)
              (data.rightVector parameter time index)) ∧
    (∀ parameter time,
      nuclear.duhamelTrace parameter time =
        ∫ slice,
          intrinsicNuclearTrace (data.sliceTraceClass parameter time slice)
            ∂sliceMeasure) :=
  ⟨data.sliceTrace_eq_tsum,
    data.duhamelTrace_eq_tsum,
    data.duhamelTrace_eq_sliceAverage⟩

end NuclearDuhamelRankOneSliceAverageData

end
end P0EFTJanusProgramPNuclearDuhamelRankOneSliceAverage4D
end JanusFormal
