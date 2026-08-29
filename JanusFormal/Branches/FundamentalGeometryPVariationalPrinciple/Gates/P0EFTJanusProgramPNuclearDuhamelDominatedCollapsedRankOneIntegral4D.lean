import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelCollapsedRankOneIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D

/-!
# Collapsed rank-one Duhamel integrals with generated differentiation

The collapsed spectral integral already derives

```text
integral_R Tr(D_a(t)) dt = Tr(D_R,a)
```

from a common rank-one expansion and one sum/integral interchange.  Its
`weighted` field, however, previously contained an independently supplied
parameter differentiation theorem.

This frontend replaces that field by the measurable and integrable domination
packet of `NuclearHeatDuhamelDominatedWeightedIntegralData`.  The resulting
collapsed integral therefore carries both

```text
partial_a integral_R w(t) Tr K_a(t) dt
  = - integral_R Tr D_a(t) dt
```

and the operator-valued spectral identity, without accepting the derivative
interchange as a primitive input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelCollapsedRankOneIntegral4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D
open P0EFTJanusProgramPNuclearHeatDuhamelDominatedWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData

universe e i s

variable {Slice : Type s} {E : Type e}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Common collapsed spectral expansion with a dominated weighted heat
integral. -/
structure NuclearDuhamelDominatedCollapsedRankOneIntegralData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (timeRegion : Set Real) where
  semigroup :
    NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear
  weighted :
    NuclearHeatDuhamelDominatedWeightedIntegralData nuclear timeRegion
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

namespace NuclearDuhamelDominatedCollapsedRankOneIntegralData

/-- Forget the domination witnesses only after generating the weighted
parameter-derivative theorem. -/
def toCollapsedRankOneIntegral
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelDominatedCollapsedRankOneIntegralData sliceMeasure
      nuclear timeRegion) :
    NuclearDuhamelCollapsedRankOneIntegralData sliceMeasure nuclear
      timeRegion where
  semigroup := data.semigroup
  weighted := data.weighted.toWeightedIntegral
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

/-- The collapsed scalar trace integral is the intrinsic trace of the regional
operator. -/
theorem scalarIntegral_eq_intrinsicTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelDominatedCollapsedRankOneIntegralData sliceMeasure
      nuclear timeRegion)
    (parameter : Real) :
    (∫ time in timeRegion,
      extendedDuhamelTrace nuclear parameter time) =
        intrinsicNuclearTrace (data.integratedTraceClass parameter) :=
  data.toCollapsedRankOneIntegral.scalarIntegral_eq_intrinsicTrace parameter

/-- Dominated differentiation of the weighted heat integral. -/
theorem weightedIntegral_hasDerivAt
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelDominatedCollapsedRankOneIntegralData sliceMeasure
      nuclear timeRegion)
    (parameter : Real) :
    HasDerivAt
      data.toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.contribution
      (-(∫ time in timeRegion,
        extendedDuhamelTrace nuclear parameter time)) parameter :=
  data.toCollapsedRankOneIntegral.weighted.toDuhamelWeightedHeatTraceVariation.hasDerivAt_contribution
    parameter

/-- Public dominated collapsed spectral-integral checkpoint. -/
theorem nuclear_duhamel_dominated_collapsed_rank_one_integral_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (timeRegion : Set Real)
    (data : NuclearDuhamelDominatedCollapsedRankOneIntegralData sliceMeasure
      nuclear timeRegion) :
    (∀ parameter,
      HasDerivAt
        data.toCollapsedRankOneIntegral.weighted.toWeightedHeatTraceVariation.contribution
        (-(∫ time in timeRegion,
          extendedDuhamelTrace nuclear parameter time)) parameter) ∧
    (∀ parameter,
      (∫ time in timeRegion,
        extendedDuhamelTrace nuclear parameter time) =
          intrinsicNuclearTrace (data.integratedTraceClass parameter)) :=
  ⟨data.weightedIntegral_hasDerivAt,
    data.scalarIntegral_eq_intrinsicTrace⟩

end NuclearDuhamelDominatedCollapsedRankOneIntegralData

end
end P0EFTJanusProgramPNuclearDuhamelDominatedCollapsedRankOneIntegral4D
end JanusFormal
