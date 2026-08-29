import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D

/-!
# Short-time collapsed Duhamel integrals from quadratic domination

This combines the collapsed rank-one expansion of `H'_a K_a(t)` with the
quadratic short-time majorant.  Integrability of the majorant and weighted
differentiation are generated; only the spectral sum/integral interchange
remains as an input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelShortTimeQuadraticDominatedCollapsedRankOneIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D
open P0EFTJanusProgramPNuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData

universe e i s

variable {Slice : Type s} {E : Type e}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

structure NuclearDuhamelShortTimeQuadraticDominatedCollapsedRankOneIntegralData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (cutoff : Real) where
  semigroup :
    NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear
  weighted :
    NuclearHeatDuhamelShortTimeQuadraticDominatedWeightedIntegralData nuclear
      cutoff
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
      ∫ time in Set.Ioo 0 cutoff,
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
    (∫ time in Set.Ioo 0 cutoff,
      ∑' index,
        (if 0 < time then coefficient parameter time index else 0) *
          inner Real (leftVector parameter index)
            (rightVector parameter index)) =
      ∑' index,
        integratedCoefficient parameter index *
          inner Real (leftVector parameter index)
            (rightVector parameter index)

namespace NuclearDuhamelShortTimeQuadraticDominatedCollapsedRankOneIntegralData

def toDominatedCollapsedRankOneIntegral
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {cutoff : Real}
    (data :
      NuclearDuhamelShortTimeQuadraticDominatedCollapsedRankOneIntegralData
        sliceMeasure nuclear cutoff) :
    NuclearDuhamelDominatedCollapsedRankOneIntegralData sliceMeasure nuclear
      (Set.Ioo 0 cutoff) where
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

theorem weightedIntegral_hasDerivAt
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {cutoff : Real}
    (data :
      NuclearDuhamelShortTimeQuadraticDominatedCollapsedRankOneIntegralData
        sliceMeasure nuclear cutoff)
    (parameter : Real) :
    HasDerivAt
      data.toDominatedCollapsedRankOneIntegral.toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.contribution
      (-∫ time in Set.Ioo 0 cutoff,
        extendedDuhamelTrace nuclear parameter time) parameter :=
  data.toDominatedCollapsedRankOneIntegral.weightedIntegral_hasDerivAt parameter

theorem bound_integrable
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {cutoff : Real}
    (data :
      NuclearDuhamelShortTimeQuadraticDominatedCollapsedRankOneIntegralData
        sliceMeasure nuclear cutoff)
    (parameter : Real) :
    Integrable
      (shortTimeQuadraticBound (data.weighted.scale parameter))
      (volume.restrict (Set.Ioo 0 cutoff)) :=
  data.weighted.bound_integrable parameter

theorem scalarIntegral_eq_intrinsicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {cutoff : Real}
    (data :
      NuclearDuhamelShortTimeQuadraticDominatedCollapsedRankOneIntegralData
        sliceMeasure nuclear cutoff)
    (parameter : Real) :
    (∫ time in Set.Ioo 0 cutoff,
      extendedDuhamelTrace nuclear parameter time) =
        intrinsicNuclearTrace (data.integratedTraceClass parameter) :=
  data.toDominatedCollapsedRankOneIntegral.scalarIntegral_eq_intrinsicTrace
    parameter

/-- Public short-time collapsed spectral checkpoint. -/
theorem nuclear_duhamel_short_time_quadratic_dominated_collapsed_rank_one_integral_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (cutoff : Real)
    (data :
      NuclearDuhamelShortTimeQuadraticDominatedCollapsedRankOneIntegralData
        sliceMeasure nuclear cutoff) :
    (∀ parameter,
      HasDerivAt
        data.toDominatedCollapsedRankOneIntegral.toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.contribution
        (-∫ time in Set.Ioo 0 cutoff,
          extendedDuhamelTrace nuclear parameter time) parameter) ∧
    (∀ parameter,
      (∫ time in Set.Ioo 0 cutoff,
        extendedDuhamelTrace nuclear parameter time) =
          intrinsicNuclearTrace (data.integratedTraceClass parameter)) :=
  ⟨data.weightedIntegral_hasDerivAt,
    data.scalarIntegral_eq_intrinsicTrace⟩

end NuclearDuhamelShortTimeQuadraticDominatedCollapsedRankOneIntegralData

end
end P0EFTJanusProgramPNuclearDuhamelShortTimeQuadraticDominatedCollapsedRankOneIntegral4D
end JanusFormal
