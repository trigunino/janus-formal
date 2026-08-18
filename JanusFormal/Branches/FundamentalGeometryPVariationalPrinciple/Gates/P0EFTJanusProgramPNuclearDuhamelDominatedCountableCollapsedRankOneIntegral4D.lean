import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelTraceIntegralInterchange4D

/-!
# Dominated collapsed Duhamel integrals with countable interchange

This frontend replaces the scalar trace sum/integral interchange field of the
collapsed rank-one packet by the countable integrability certificate that
proves it.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelDominatedCountableCollapsedRankOneIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D
open P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearDuhamelTraceIntegralInterchange4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData

universe e i s

variable {Slice : Type s} {E : Type e}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- A dominated collapsed rank-one integral whose scalar interchange is
certified term by term. -/
structure NuclearDuhamelDominatedCountableCollapsedRankOneIntegralData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (timeRegion : Set Real) where
  semigroup :
    NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear
  weighted :
    NuclearHeatDuhamelDominatedWeightedIntegralData nuclear timeRegion
  Index : Type i
  index_countable : Countable Index
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
  traceInterchangeCertificate : ∀ parameter,
    CountableTraceIntegralInterchangeData
      (volume.restrict timeRegion)
      (fun index time =>
        (if 0 < time then coefficient parameter time index else 0) *
          inner Real (leftVector parameter index)
            (rightVector parameter index))

namespace NuclearDuhamelDominatedCountableCollapsedRankOneIntegralData

/-- Generate the former interchange hypothesis from countable Bochner
integrability. -/
def toDominatedCollapsedRankOneIntegral
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelDominatedCountableCollapsedRankOneIntegralData
      sliceMeasure nuclear timeRegion) :
    NuclearDuhamelDominatedCollapsedRankOneIntegralData sliceMeasure nuclear
      timeRegion where
  semigroup := data.semigroup
  weighted := data.weighted
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
  trace_integral_interchange := by
    letI := data.index_countable
    exact collapsedTrace_integral_interchange
      data.integratedCoefficient_eq data.traceInterchangeCertificate

/-- Public checkpoint: both weighted differentiation and the regional trace
identity now follow without a primitive sum/integral exchange field. -/
theorem nuclear_duhamel_dominated_countable_collapsed_rank_one_integral_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (timeRegion : Set Real)
    (data : NuclearDuhamelDominatedCountableCollapsedRankOneIntegralData
      sliceMeasure nuclear timeRegion) :
    (∀ parameter,
      HasDerivAt
        (data.toDominatedCollapsedRankOneIntegral.toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation).contribution
        (-(∫ time in timeRegion,
          extendedDuhamelTrace nuclear parameter time)) parameter) ∧
    (∀ parameter,
      (∫ time in timeRegion,
        extendedDuhamelTrace nuclear parameter time) =
          intrinsicNuclearTrace (data.integratedTraceClass parameter)) :=
  ⟨data.toDominatedCollapsedRankOneIntegral.weightedIntegral_hasDerivAt,
    data.toDominatedCollapsedRankOneIntegral.scalarIntegral_eq_intrinsicTrace⟩

end NuclearDuhamelDominatedCountableCollapsedRankOneIntegralData

end
end P0EFTJanusProgramPNuclearDuhamelDominatedCountableCollapsedRankOneIntegral4D
end JanusFormal
