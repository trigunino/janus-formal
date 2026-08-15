import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D

/-!
# Rank-one construction of nuclear Duhamel operator integrals

`NuclearDuhamelOperatorIntegralData` identifies a scalar time integral with the
intrinsic trace of an integrated nuclear operator.  This file gives a concrete
way to prove that identification.

A single index type and parameter-dependent left/right vectors are used for the
whole time region.  Only the scalar coefficients vary with time.  Pointwise
rank-one expansions represent the Duhamel operator, while the integrated
coefficients represent the operator-valued time integral.  One explicit
sum/integral interchange then proves

```text
integral Tr(D_a(t)) dt = Tr(integral D_a(t) dt).
```

The final scalar equality is therefore an output, not an additional field.
This interface matches the spectral expansions expected for the concrete
reference heat operators.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelRankOneIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Common rank-one spectral expansion for a Duhamel family on one real-time
region.  The basis vectors may vary with the family parameter but not with the
heat time. -/
structure NuclearDuhamelRankOneIntegralData
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (timeRegion : Set Real) where
  weighted : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion
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
  pointwise_operator_eq_tsum : ∀ parameter time : HeatTime,
    nuclear.duhamelOperator parameter time = ∑' index,
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
    IntrinsicNuclearTraceData (integratedOperator parameter)
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

namespace NuclearDuhamelRankOneIntegralData

/-- Pointwise rank-one expansion of the genuine positive-time Duhamel
operator. -/
def pointwiseExpansion
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelRankOneIntegralData nuclear timeRegion)
    (parameter : Real) (time : HeatTime) :
    SummableRankOneOperatorExpansion
      (nuclear.duhamelOperator parameter time) where
  Index := data.Index
  coefficient := data.coefficient parameter time.1
  leftVector := data.leftVector parameter
  rightVector := data.rightVector parameter
  summable_nuclearNorm := data.pointwise_nuclearNorm_summable parameter time
  trace_summable := data.pointwise_trace_summable parameter time
  operator_eq_tsum := data.pointwise_operator_eq_tsum parameter time

/-- Rank-one expansion of the operator-valued time integral. -/
def integratedExpansion
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelRankOneIntegralData nuclear timeRegion)
    (parameter : Real) :
    SummableRankOneOperatorExpansion (data.integratedOperator parameter) where
  Index := data.Index
  coefficient := data.integratedCoefficient parameter
  leftVector := data.leftVector parameter
  rightVector := data.rightVector parameter
  summable_nuclearNorm := data.integrated_nuclearNorm_summable parameter
  trace_summable := data.integrated_trace_summable parameter
  operator_eq_tsum := data.integrated_operator_eq_tsum parameter

/-- The intrinsic pointwise Duhamel trace is computed by the common spectral
rank-one expansion. -/
theorem duhamelTrace_eq_tsum
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelRankOneIntegralData nuclear timeRegion)
    (parameter : Real) (time : HeatTime) :
    nuclear.duhamelTrace parameter time =
      ∑' index,
        data.coefficient parameter time.1 index *
          inner Real (data.leftVector parameter index)
            (data.rightVector parameter index) := by
  exact
    (nuclear.duhamelTraceClass parameter time).expansionTrace_eq
      (data.pointwiseExpansion parameter time)

/-- The zero extension of the Duhamel trace is the corresponding zero-extended
spectral series. -/
theorem extendedDuhamelTrace_eq_tsum
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelRankOneIntegralData nuclear timeRegion)
    (parameter time : Real) :
    nuclear.extendedDuhamelTrace parameter time =
      ∑' index,
        (if 0 < time then data.coefficient parameter time index else 0) *
          inner Real (data.leftVector parameter index)
            (data.rightVector parameter index) := by
  by_cases hTime : 0 < time
  · simp only [NuclearHeatDuhamelTraceVariationData.extendedDuhamelTrace,
      hTime, dite_true]
    exact data.duhamelTrace_eq_tsum parameter ⟨time, hTime⟩
  · simp [NuclearHeatDuhamelTraceVariationData.extendedDuhamelTrace, hTime]

/-- The scalar Duhamel-trace integral is the intrinsic trace of the integrated
operator. -/
theorem scalarIntegral_eq_intrinsicTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelRankOneIntegralData nuclear timeRegion)
    (parameter : Real) :
    (∫ time in timeRegion,
      nuclear.extendedDuhamelTrace parameter time) =
        intrinsicNuclearTrace (data.integratedTraceClass parameter) := by
  calc
    (∫ time in timeRegion,
        nuclear.extendedDuhamelTrace parameter time) =
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

/-- Conversion to the operator-valued integral interface. -/
def toOperatorIntegral
    {nuclear : NuclearHeatDuhamelTraceVariationData (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelRankOneIntegralData nuclear timeRegion) :
    NuclearDuhamelOperatorIntegralData nuclear timeRegion where
  weighted := data.weighted
  integratedOperator := data.integratedOperator
  integratedTraceClass := data.integratedTraceClass
  scalarIntegral_eq_trace := data.scalarIntegral_eq_intrinsicTrace

/-- Public rank-one Duhamel-integral checkpoint. -/
theorem nuclear_duhamel_rank_one_integral_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData (E := E))
    (timeRegion : Set Real)
    (data : NuclearDuhamelRankOneIntegralData nuclear timeRegion) :
    (∀ parameter time : HeatTime,
      nuclear.duhamelTrace parameter time =
        ∑' index,
          data.coefficient parameter time.1 index *
            inner Real (data.leftVector parameter index)
              (data.rightVector parameter index)) ∧
    (∀ parameter,
      (∫ time in timeRegion,
        nuclear.extendedDuhamelTrace parameter time) =
          intrinsicNuclearTrace (data.integratedTraceClass parameter)) ∧
    (∀ parameter,
      data.toOperatorIntegral.weighted.toWeightedHeatTraceVariation.
          derivativeContribution parameter =
        -data.toOperatorIntegral.integratedTrace parameter) :=
  ⟨data.duhamelTrace_eq_tsum,
    data.scalarIntegral_eq_intrinsicTrace,
    data.toOperatorIntegral.derivativeContribution_eq_neg_integratedTrace⟩

end NuclearDuhamelRankOneIntegralData

end
end P0EFTJanusProgramPNuclearDuhamelRankOneIntegral4D
end JanusFormal
