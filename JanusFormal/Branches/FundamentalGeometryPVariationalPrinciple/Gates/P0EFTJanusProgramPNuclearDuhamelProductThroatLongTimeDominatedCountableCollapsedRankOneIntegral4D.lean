import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelProductThroatLongTimeCollapsedRankOneIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelTraceIntegralInterchange4D

/-!
# Countable product-throat long-time rank-one interchange

The scalar sum/integral exchange is generated from a countable index and a
dominated termwise Bochner certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelProductThroatLongTimeDominatedCountableCollapsedRankOneIntegral4D

set_option autoImplicit false
noncomputable section

open Filter Set MeasureTheory
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupProbabilityFamily4D
open P0EFTJanusProgramPProductThroatNuclearHeatDuhamelLongTimeExponential4D
open P0EFTJanusProgramPNuclearDuhamelProductThroatLongTimeCollapsedRankOneIntegral4D
open P0EFTJanusProgramPNuclearDuhamelTraceIntegralInterchange4D

universe e i s

variable {Slice : Type s} {E : Type e}
  [MeasurableSpace Slice]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Product-throat long-time spectral packet with a generated scalar
sum/integral interchange. -/
structure NuclearDuhamelProductThroatLongTimeDominatedCountableCollapsedRankOneIntegralData
    (productData : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E))
    (start : Real) where
  semigroup : NuclearDuhamelSemigroupProbabilityFamilyData sliceMeasure nuclear
  weighted : ProductThroatNuclearHeatDuhamelLongTimeExponentialData
    productData fold twist nuclear start
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
        inner Real (leftVector parameter index) (rightVector parameter index))
  collapsed_operator_eq_tsum : ∀ parameter : Real, ∀ time : HeatTime,
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
        inner Real (leftVector parameter index) (rightVector parameter index))
  integrated_operator_eq_tsum : ∀ parameter,
    integratedOperator parameter = ∑' index,
      integratedCoefficient parameter index •
        InnerProductSpace.rankOne Real
          (leftVector parameter index) (rightVector parameter index)
  integratedTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{e, i} (integratedOperator parameter)
  traceInterchangeDomination : ∀ parameter,
    DominatedCountableTraceIntegralInterchangeData
      (volume.restrict (Set.Ioi start))
      (fun index time =>
        (if 0 < time then coefficient parameter time index else 0) *
          inner Real (leftVector parameter index) (rightVector parameter index))

namespace NuclearDuhamelProductThroatLongTimeDominatedCountableCollapsedRankOneIntegralData

/-- Generate the product-throat collapsed packet and its interchange field. -/
def toProductThroatLongTimeCollapsedRankOneIntegral
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data :
      NuclearDuhamelProductThroatLongTimeDominatedCountableCollapsedRankOneIntegralData
        productData fold twist sliceMeasure nuclear start) :
    NuclearDuhamelProductThroatLongTimeCollapsedRankOneIntegralData
      productData fold twist sliceMeasure nuclear start where
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
    exact collapsedTrace_integral_interchange data.integratedCoefficient_eq
      (fun parameter =>
        (data.traceInterchangeDomination parameter).toCountableTraceIntegralInterchangeData)

/-- Public product-throat countable-interchange checkpoint. -/
theorem nuclear_duhamel_product_throat_long_time_dominated_countable_gate
    {productData : ProductThroatSpectralData}
    {fold : Fold} {twist : CircleTwist}
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {nuclear : NuclearHeatDuhamelTraceVariationData.{e, i} (E := E)}
    {start : Real}
    (data :
      NuclearDuhamelProductThroatLongTimeDominatedCountableCollapsedRankOneIntegralData
        productData fold twist sliceMeasure nuclear start) :
    ∀ parameter,
      (∫ time in Set.Ioi start,
        ∑' index,
          (if 0 < time then data.coefficient parameter time index else 0) *
            inner Real (data.leftVector parameter index)
              (data.rightVector parameter index)) =
        ∑' index,
          data.integratedCoefficient parameter index *
            inner Real (data.leftVector parameter index)
              (data.rightVector parameter index) :=
  data.toProductThroatLongTimeCollapsedRankOneIntegral.trace_integral_interchange

end NuclearDuhamelProductThroatLongTimeDominatedCountableCollapsedRankOneIntegralData

end
end P0EFTJanusProgramPNuclearDuhamelProductThroatLongTimeDominatedCountableCollapsedRankOneIntegral4D
end JanusFormal
