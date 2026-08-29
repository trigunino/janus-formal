import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D

/-!
# Rank-one integration after Duhamel semigroup collapse

The preceding semigroup-probability theorem reduces the scalar Duhamel trace to

```text
Tr(D_a(t)) = Tr(H'_a K_a(t)).
```

It is therefore unnecessary to construct a rank-one expansion of the averaged
Duhamel operator itself.  This file instead expands the simpler collapsed
operator `H'_a K_a(t)`, integrates its scalar coefficients and derives the
operator-valued regional integral.

The construction proves

```text
integral_region Tr(D_a(t)) dt
  = integral_region Tr(H'_a K_a(t)) dt
  = Tr(D_region,a).
```

Only the common spectral expansion of the collapsed operator and one
sum/integral interchange remain as analytic inputs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelCollapsedRankOneIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D

universe e i s

variable {Slice : Type s} {E : Type e}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Common spectral expansion of the collapsed insertion/full-heat operator on
one real-time region. -/
structure NuclearDuhamelCollapsedRankOneIntegralData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (timeRegion : Set Real) where
  semigroup :
    NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear
  weighted : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion
  Index : Type i
  coefficient : Real → Real → Index → Real
  leftVector : Real → Index → E
  rightVector : Real → Index → E
  pointwise_nuclearNorm_summable : ∀ parameter : Real, ∀ time : HeatTime,
    Summable (fun index =>
      |coefficient parameter time.1 index| *
        ‖leftVector parameter index‖ * ‖rightVector parameter index‖)
  pointwise_trace_summable : ∀ parameter : Real, ∀ time : HeatTime,
    Summable (fun index =>
      coefficient parameter time.1 index *
        inner Real (leftVector parameter index)
          (rightVector parameter index))
  collapsed_operator_eq_tsum : ∀ parameter : Real, ∀ time : HeatTime,
    (semigroup.insertion parameter time).comp
        (semigroup.fullHeat parameter time) = ∑' index,
      coefficient parameter time.1 index •
        InnerProductSpace.rankOne Real
          (leftVector parameter index) (rightVector parameter index)
  integratedCoefficient : Real → Index → Real
  integratedCoefficient_eq : ∀ parameter index,
    integratedCoefficient parameter index =
      ∫ time in timeRegion,
        if 0 < time then coefficient parameter time index else 0
  integratedOperator : Real → E →L[Real] E
  integrated_nuclearNorm_summable : ∀ parameter,
    Summable (fun index =>
      |integratedCoefficient parameter index| *
        ‖leftVector parameter index‖ * ‖rightVector parameter index‖)
  integrated_trace_summable : ∀ parameter,
    Summable (fun index =>
      integratedCoefficient parameter index *
        inner Real (leftVector parameter index)
          (rightVector parameter index))
  integrated_operator_eq_tsum : ∀ parameter,
    integratedOperator parameter = ∑' index,
      integratedCoefficient parameter index •
        InnerProductSpace.rankOne Real
          (leftVector parameter index) (rightVector parameter index)
  integratedTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{e, i} (integratedOperator parameter)
  trace_integral_interchange : ∀ parameter,
    (∫ time in timeRegion,
      ∑' index,
        (if 0 < time then coefficient parameter time index else 0) *
          inner Real (leftVector parameter index)
            (rightVector parameter index)) =
      ∑' index,
        integratedCoefficient parameter index *
          inner Real (leftVector parameter index)
            (rightVector parameter index)

namespace NuclearDuhamelCollapsedRankOneIntegralData

/-- Pointwise expansion of `H'_a K_a(t)`. -/
def pointwiseExpansion
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
      timeRegion)
    (parameter : Real) (time : HeatTime) :
    SummableRankOneOperatorExpansion
      ((data.semigroup.insertion parameter time).comp
        (data.semigroup.fullHeat parameter time)) where
  Index := data.Index
  coefficient := data.coefficient parameter time.1
  leftVector := data.leftVector parameter
  rightVector := data.rightVector parameter
  summable_nuclearNorm := data.pointwise_nuclearNorm_summable parameter time
  trace_summable := data.pointwise_trace_summable parameter time
  operator_eq_tsum := data.collapsed_operator_eq_tsum parameter time

/-- Expansion of the operator-valued regional integral. -/
def integratedExpansion
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
      timeRegion)
    (parameter : Real) :
    SummableRankOneOperatorExpansion (data.integratedOperator parameter) where
  Index := data.Index
  coefficient := data.integratedCoefficient parameter
  leftVector := data.leftVector parameter
  rightVector := data.rightVector parameter
  summable_nuclearNorm := data.integrated_nuclearNorm_summable parameter
  trace_summable := data.integrated_trace_summable parameter
  operator_eq_tsum := data.integrated_operator_eq_tsum parameter

/-- The genuine Duhamel trace is computed by the collapsed spectral series. -/
theorem duhamelTrace_eq_tsum
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
      timeRegion)
    (parameter : Real) (time : HeatTime) :
    nuclear.duhamelTrace parameter time =
      ∑' index,
        data.coefficient parameter time.1 index *
          inner Real (data.leftVector parameter index)
            (data.rightVector parameter index) := by
  calc
    nuclear.duhamelTrace parameter time =
        intrinsicNuclearTrace
          (data.semigroup.collapsedTraceClass parameter time) :=
      data.semigroup.duhamelTrace_eq_insertionFullHeatTrace parameter time
    _ = (data.pointwiseExpansion parameter time).expansionTrace :=
      ((data.semigroup.collapsedTraceClass parameter time).expansionTrace_eq
        (data.pointwiseExpansion parameter time)).symm
    _ = ∑' index,
        data.coefficient parameter time.1 index *
          inner Real (data.leftVector parameter index)
            (data.rightVector parameter index) := rfl

/-- Zero-extended Duhamel trace in the collapsed spectral coordinates. -/
theorem extendedDuhamelTrace_eq_tsum
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
      timeRegion)
    (parameter time : Real) :
    extendedDuhamelTrace nuclear parameter time =
      ∑' index,
        (if 0 < time then data.coefficient parameter time index else 0) *
          inner Real (data.leftVector parameter index)
            (data.rightVector parameter index) := by
  by_cases hTime : 0 < time
  · simp only [extendedDuhamelTrace, hTime, dite_true]
    exact data.duhamelTrace_eq_tsum parameter ⟨time, hTime⟩
  · simp [extendedDuhamelTrace, hTime]

/-- The time integral of the Duhamel trace is the intrinsic trace of the
integrated collapsed operator. -/
theorem scalarIntegral_eq_intrinsicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
      timeRegion)
    (parameter : Real) :
    (∫ time in timeRegion,
      extendedDuhamelTrace nuclear parameter time) =
        intrinsicNuclearTrace (data.integratedTraceClass parameter) := by
  calc
    (∫ time in timeRegion,
        extendedDuhamelTrace nuclear parameter time) =
      ∫ time in timeRegion,
        ∑' index,
          (if 0 < time then data.coefficient parameter time index else 0) *
            inner Real (data.leftVector parameter index)
              (data.rightVector parameter index) := by
        apply integral_congr_ae
        filter_upwards [] with time
        exact data.extendedDuhamelTrace_eq_tsum parameter time
    _ = ∑' index,
        data.integratedCoefficient parameter index *
          inner Real (data.leftVector parameter index)
            (data.rightVector parameter index) :=
      data.trace_integral_interchange parameter
    _ = (data.integratedExpansion parameter).expansionTrace := rfl
    _ = intrinsicNuclearTrace (data.integratedTraceClass parameter) :=
      (data.integratedTraceClass parameter).expansionTrace_eq
        (data.integratedExpansion parameter)

/-- Conversion to the generic operator-valued Duhamel integral interface. -/
def toOperatorIntegral
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
      timeRegion) :
    NuclearDuhamelOperatorIntegralData nuclear timeRegion where
  weighted := data.weighted
  integratedOperator := data.integratedOperator
  integratedTraceClass := data.integratedTraceClass
  scalarIntegral_eq_trace := data.scalarIntegral_eq_intrinsicTrace

/-- Public collapsed rank-one integral checkpoint. -/
theorem nuclear_duhamel_collapsed_rank_one_integral_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (timeRegion : Set Real)
    (data : NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
      timeRegion) :
    (∀ parameter time,
      nuclear.duhamelTrace parameter time =
        intrinsicNuclearTrace
          (data.semigroup.collapsedTraceClass parameter time)) ∧
    (∀ parameter : Real, ∀ time : HeatTime,
      nuclear.duhamelTrace parameter time =
        ∑' index,
          data.coefficient parameter time.1 index *
            inner Real (data.leftVector parameter index)
              (data.rightVector parameter index)) ∧
    (∀ parameter,
      (∫ time in timeRegion,
        extendedDuhamelTrace nuclear parameter time) =
          intrinsicNuclearTrace (data.integratedTraceClass parameter)) :=
  ⟨data.semigroup.duhamelTrace_eq_insertionFullHeatTrace,
    data.duhamelTrace_eq_tsum,
    data.scalarIntegral_eq_intrinsicTrace⟩

end NuclearDuhamelCollapsedRankOneIntegralData

end
end P0EFTJanusProgramPNuclearDuhamelCollapsedRankOneIntegral4D
end JanusFormal
