import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelRankOneSliceAverage4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D

/-!
# Semigroup collapse from rank-one Duhamel slice averages

The semigroup-probability family previously retained the scalar statement that
the genuine Duhamel trace equals the average of its slice traces.  The
rank-one slice-average theorem now derives that statement.

This file joins the constructions.  Each spectrally represented slice is
identified with

```text
K_left(a,t,s) (H'_a K_right(a,t,s)).
```

Its intrinsic trace certificate is transported through that operator equality.
Nuclear cyclicity and the semigroup law make every transported slice trace equal
to `Tr(H'_a K_full(a,t))`; the rank-one average theorem proves that the genuine
Duhamel trace is their probability average.

Thus the complete identity

```text
Tr(D_a(t)) = Tr(H'_a K_full(a,t))
```

is generated solely from operator equalities, nuclear expansions and the two
sum/integral exchanges attached to the slice average.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelSemigroupRankOneAverage4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelRankOneSliceAverage4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D

universe u v w

variable {Slice : Type u} {E : Type v}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Rank-one averaged Duhamel slices equipped with their heat-semigroup
factorization. -/
structure NuclearDuhamelSemigroupRankOneAverageData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E)) where
  sliceAverage : NuclearDuhamelRankOneSliceAverageData.{u, v, w}
    sliceMeasure nuclear
  leftHeat : Real → HeatTime → Slice → E →L[Real] E
  rightHeat : Real → HeatTime → Slice → E →L[Real] E
  fullHeat : Real → HeatTime → E →L[Real] E
  insertion : Real → HeatTime → E →L[Real] E
  sliceOperator_eq : ∀ parameter time slice,
    sliceAverage.sliceOperator parameter time slice =
      (leftHeat parameter time slice).comp
        ((insertion parameter time).comp (rightHeat parameter time slice))
  semigroup_eq : ∀ parameter time slice,
    (rightHeat parameter time slice).comp (leftHeat parameter time slice) =
      fullHeat parameter time
  insertionRightExpansion : ∀ parameter time slice,
    SummableRankOneOperatorExpansion.{w, v}
      ((insertion parameter time).comp (rightHeat parameter time slice))
  rotatedTraceClass : ∀ parameter time slice,
    IntrinsicNuclearTraceData.{v, w}
      (((insertion parameter time).comp (rightHeat parameter time slice)).comp
        (leftHeat parameter time slice))
  collapsedTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData.{v, w}
      ((insertion parameter time).comp (fullHeat parameter time))

namespace NuclearDuhamelSemigroupRankOneAverageData

/-- Transport the original slice trace certificate to the explicit
left-composition operator. -/
def leftCompositionTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E)}
    (data : NuclearDuhamelSemigroupRankOneAverageData.{u, v, w}
      sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) (slice : Slice) :
    IntrinsicNuclearTraceData.{v, w}
      ((data.leftHeat parameter time slice).comp
        ((data.insertion parameter time).comp
          (data.rightHeat parameter time slice))) :=
  P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator
    (data.sliceAverage.sliceTraceClass parameter time slice)
    (data.sliceOperator_eq parameter time slice)

/-- The transport does not change the intrinsic scalar trace. -/
theorem leftCompositionTrace_eq_sliceTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E)}
    (data : NuclearDuhamelSemigroupRankOneAverageData.{u, v, w}
      sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) (slice : Slice) :
    intrinsicNuclearTrace (data.leftCompositionTrace parameter time slice) =
      intrinsicNuclearTrace
        (data.sliceAverage.sliceTraceClass parameter time slice) :=
  P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator_intrinsicNuclearTrace
    (data.sliceAverage.sliceTraceClass parameter time slice)
    (data.sliceOperator_eq parameter time slice)

/-- Conversion to the semigroup-probability interface, with its slice-average
identity derived from the rank-one spectral construction. -/
def toSemigroupProbabilityFamily
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E)}
    (data : NuclearDuhamelSemigroupRankOneAverageData.{u, v, w}
      sliceMeasure nuclear) :
    NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear where
  leftHeat := data.leftHeat
  rightHeat := data.rightHeat
  fullHeat := data.fullHeat
  insertion := data.insertion
  semigroup_eq := data.semigroup_eq
  insertionRightExpansion := data.insertionRightExpansion
  sliceTraceClass := data.leftCompositionTrace
  rotatedTraceClass := data.rotatedTraceClass
  collapsedTraceClass := data.collapsedTraceClass
  duhamelTrace_eq_sliceAverage := by
    intro parameter time
    calc
      nuclear.duhamelTrace parameter time =
          ∫ slice,
            intrinsicNuclearTrace
              (data.sliceAverage.sliceTraceClass parameter time slice)
              ∂sliceMeasure :=
        data.sliceAverage.duhamelTrace_eq_sliceAverage parameter time
      _ = ∫ slice,
          intrinsicNuclearTrace
            (data.leftCompositionTrace parameter time slice)
            ∂sliceMeasure := by
        apply integral_congr_ae
        filter_upwards [] with slice
        exact (data.leftCompositionTrace_eq_sliceTrace parameter time slice).symm

/-- The genuine Duhamel trace equals the collapsed insertion/full-heat trace,
with the slice average itself generated spectrally. -/
theorem duhamelTrace_eq_insertionFullHeatTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E)}
    (data : NuclearDuhamelSemigroupRankOneAverageData.{u, v, w}
      sliceMeasure nuclear)
    (parameter : Real) (time : HeatTime) :
    nuclear.duhamelTrace parameter time =
      intrinsicNuclearTrace (data.collapsedTraceClass parameter time) :=
  data.toSemigroupProbabilityFamily.duhamelTrace_eq_insertionFullHeatTrace
    parameter time

/-- Public fully spectral semigroup-average checkpoint. -/
theorem nuclear_duhamel_semigroup_rank_one_average_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{v, w} (E := E))
    (data : NuclearDuhamelSemigroupRankOneAverageData.{u, v, w}
      sliceMeasure nuclear) :
    (∀ parameter time,
      nuclear.duhamelTrace parameter time =
        ∫ slice,
          intrinsicNuclearTrace
            (data.sliceAverage.sliceTraceClass parameter time slice)
            ∂sliceMeasure) ∧
    (∀ parameter time slice,
      (data.rightHeat parameter time slice).comp
          (data.leftHeat parameter time slice) =
        data.fullHeat parameter time) ∧
    (∀ parameter time,
      nuclear.duhamelTrace parameter time =
        intrinsicNuclearTrace (data.collapsedTraceClass parameter time)) :=
  ⟨data.sliceAverage.duhamelTrace_eq_sliceAverage,
    data.semigroup_eq,
    data.duhamelTrace_eq_insertionFullHeatTrace⟩

end NuclearDuhamelSemigroupRankOneAverageData

end
end P0EFTJanusProgramPNuclearDuhamelSemigroupRankOneAverage4D
end JanusFormal
