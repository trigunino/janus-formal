import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegral4D

/-!
# Long-time collapsed Duhamel integrals from exponential domination

This module combines the common rank-one expansion of `H'_a K_a(t)` with the
long-time exponential domination packet.  Both differentiation under the
weighted integral and integrability of its majorant are generated; the only
remaining spectral integration input is the rank-one sum/integral exchange.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D
open P0EFTJanusProgramPNuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegral4D

universe u

variable {Slice E : Type*}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

structure NuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegralData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (start : Real) where
  semigroup :
    NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear
  weighted :
    NuclearHeatDuhamelLongTimeExponentialDominatedWeightedIntegralData nuclear
      start
  Index : Type u
  coefficient : Real → Real → Index → Real
  leftVector : Real → Index → E
  rightVector : Real → Index → E
  pointwise_nuclearNorm_summable : ∀ parameter time : HeatTime,
    Summable (fun index =>
      |coefficient parameter time.1 index| *
        ‖leftVector parameter index‖ * ‖rightVector parameter index‖)
  pointwise_trace_summable : ∀ parameter time : HeatTime,
    Summable (fun index =>
      coefficient parameter time.1 index *
        inner Real (leftVector parameter index)
          (rightVector parameter index))
  collapsed_operator_eq_tsum : ∀ parameter time : HeatTime,
    (semigroup.insertion parameter time).comp
        (semigroup.fullHeat parameter time) = ∑' index,
      coefficient parameter time.1 index •
        InnerProductSpace.rankOne Real
          (leftVector parameter index) (rightVector parameter index)
  integratedCoefficient : Real → Index → Real
  integratedCoefficient_eq : ∀ parameter index,
    integratedCoefficient parameter index =
      ∫ time in Set.Ioi start,
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
    IntrinsicNuclearTraceData (integratedOperator parameter)
  trace_integral_interchange : ∀ parameter,
    (∫ time in Set.Ioi start,
      ∑' index,
        (if 0 < time then coefficient parameter time index else 0) *
          inner Real (leftVector parameter index)
            (rightVector parameter index)) =
      ∑' index,
        integratedCoefficient parameter index *
          inner Real (leftVector parameter index)
            (rightVector parameter index)

namespace NuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegralData

def toDominatedCollapsedRankOneIntegral
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {start : Real}
    (data :
      NuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegralData
        sliceMeasure nuclear start) :
    NuclearDuhamelDominatedCollapsedRankOneIntegralData sliceMeasure nuclear
      (Set.Ioi start) where
  semigroup := data.semigroup
  weighted := data.weighted.toDominatedWeightedIntegral
  Index := data.Index
  coefficient := data.coefficient
  leftVector := data.leftVector
  rightVector := data.rightVector
  pointwise_nuclearNorm_summable := data.pointwise_nuclearNorm_summable
  pointwise_trace_summable := data.pointwise_trace_summable
  collapsed_operator_eq_tsum := data.collapsed_operator_eq_tsum
  integratedCoefficient := data.integratedCoefficient
  integratedCoefficient_eq := data.integratedCoefficient_eq
  integratedOperator := data.integratedOperator
  integrated_nuclearNorm_summable := data.integrated_nuclearNorm_summable
  integrated_trace_summable := data.integrated_trace_summable
  integrated_operator_eq_tsum := data.integrated_operator_eq_tsum
  integratedTraceClass := data.integratedTraceClass
  trace_integral_interchange := data.trace_integral_interchange

/-- Long-time weighted differentiation generated from the exponential
majorant. -/
theorem weightedIntegral_hasDerivAt
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {start : Real}
    (data :
      NuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegralData
        sliceMeasure nuclear start)
    (parameter : Real) :
    HasDerivAt
      data.toDominatedCollapsedRankOneIntegral.toCollapsedRankOneIntegral.
        weighted.toWeightedHeatTraceVariation.contribution
      (-(∫ time in Set.Ioi start,
        nuclear.extendedDuhamelTrace parameter time)) parameter :=
  data.toDominatedCollapsedRankOneIntegral.weightedIntegral_hasDerivAt parameter

/-- The exponential majorant is integrable. -/
theorem bound_integrable
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {start : Real}
    (data :
      NuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegralData
        sliceMeasure nuclear start)
    (parameter : Real) :
    Integrable
      (P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D.
        longTimeExponentialBound (data.weighted.scale parameter)
          (data.weighted.rate parameter))
      (volume.restrict (Set.Ioi start)) :=
  data.weighted.bound_integrable parameter

/-- The Duhamel trace integral is the trace of the integrated spectral
operator. -/
theorem scalarIntegral_eq_intrinsicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {start : Real}
    (data :
      NuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegralData
        sliceMeasure nuclear start)
    (parameter : Real) :
    (∫ time in Set.Ioi start,
      nuclear.extendedDuhamelTrace parameter time) =
        intrinsicNuclearTrace (data.integratedTraceClass parameter) :=
  data.toDominatedCollapsedRankOneIntegral.
    scalarIntegral_eq_intrinsicTrace parameter

/-- Public long-time collapsed spectral checkpoint. -/
theorem nuclear_duhamel_long_time_exponential_dominated_collapsed_rank_one_integral_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (start : Real)
    (data :
      NuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegralData
        sliceMeasure nuclear start) :
    (∀ parameter,
      HasDerivAt
        data.toDominatedCollapsedRankOneIntegral.toCollapsedRankOneIntegral.
          weighted.toWeightedHeatTraceVariation.contribution
        (-(∫ time in Set.Ioi start,
          nuclear.extendedDuhamelTrace parameter time)) parameter) ∧
    (∀ parameter,
      (∫ time in Set.Ioi start,
        nuclear.extendedDuhamelTrace parameter time) =
          intrinsicNuclearTrace (data.integratedTraceClass parameter)) :=
  ⟨data.weightedIntegral_hasDerivAt,
    data.scalarIntegral_eq_intrinsicTrace⟩

end NuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegralData

end
end P0EFTJanusProgramPNuclearDuhamelLongTimeExponentialDominatedCollapsedRankOneIntegral4D
end JanusFormal
