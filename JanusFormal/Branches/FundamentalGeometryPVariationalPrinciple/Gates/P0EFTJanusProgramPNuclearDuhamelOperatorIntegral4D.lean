import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D

/-!
# Operator-valued nuclear Duhamel integrals

A weighted heat-variation packet identifies the derivative of one scalar heat
integral with minus the integral of the scalar Duhamel trace.  To connect this
statement to the Green logarithmic derivative, the time integral must itself
have an operator origin.

This file packages one such region.  The operator-valued integral is represented
by an intrinsic nuclear trace certificate and its scalar trace is required to
be exactly the integral of the pointwise Duhamel traces.  The derivative of the
weighted heat contribution is then automatically minus that intrinsic trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D
open P0EFTJanusProgramPNuclearHeatDuhamelWeightedIntegral4D.NuclearHeatDuhamelTraceVariationData
open P0EFTJanusProgramPWeightedHeatTraceIntegralVariation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- One real-time Duhamel region together with its intrinsic nuclear operator
integral. -/
structure NuclearDuhamelOperatorIntegralData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (timeRegion : Set Real) where
  weighted : NuclearHeatDuhamelWeightedIntegralData nuclear timeRegion
  integratedOperator : Real → E →L[Real] E
  integratedTraceClass : ∀ parameter,
    IntrinsicNuclearTraceData.{u, v} (integratedOperator parameter)
  scalarIntegral_eq_trace : ∀ parameter,
    (∫ time in timeRegion,
      extendedDuhamelTrace nuclear parameter time) =
        intrinsicNuclearTrace (integratedTraceClass parameter)

namespace NuclearDuhamelOperatorIntegralData

/-- Scalar trace of the operator-valued Duhamel integral. -/
def integratedTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelOperatorIntegralData.{u, v} nuclear timeRegion)
    (parameter : Real) : Real :=
  intrinsicNuclearTrace (data.integratedTraceClass parameter)

/-- The weighted finite-part contribution differentiates to minus the intrinsic
trace of the integrated Duhamel operator. -/
theorem derivativeContribution_eq_neg_integratedTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelOperatorIntegralData.{u, v} nuclear timeRegion)
    (parameter : Real) :
    data.weighted.toWeightedHeatTraceVariation.derivativeContribution parameter =
      -data.integratedTrace parameter := by
  rw [data.weighted.derivativeContribution_eq_neg_integral parameter]
  rw [data.scalarIntegral_eq_trace parameter]
  rfl

/-- The contribution itself has derivative minus the operator trace. -/
theorem hasDerivAt_contribution
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {timeRegion : Set Real}
    (data : NuclearDuhamelOperatorIntegralData.{u, v} nuclear timeRegion)
    (parameter : Real) :
    HasDerivAt data.weighted.toWeightedHeatTraceVariation.contribution
      (-data.integratedTrace parameter) parameter := by
  rw [← data.derivativeContribution_eq_neg_integratedTrace parameter]
  exact data.weighted.toWeightedHeatTraceVariation.hasDerivAt_integral parameter

/-- Public operator-valued Duhamel-integral checkpoint. -/
theorem nuclear_duhamel_operator_integral_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (timeRegion : Set Real)
    (data : NuclearDuhamelOperatorIntegralData.{u, v} nuclear timeRegion) :
    (∀ parameter,
      (∫ time in timeRegion,
        extendedDuhamelTrace nuclear parameter time) =
          data.integratedTrace parameter) ∧
    (∀ parameter,
      data.weighted.toWeightedHeatTraceVariation.derivativeContribution parameter =
        -data.integratedTrace parameter) ∧
    (∀ parameter,
      HasDerivAt data.weighted.toWeightedHeatTraceVariation.contribution
        (-data.integratedTrace parameter) parameter) :=
  ⟨data.scalarIntegral_eq_trace,
    data.derivativeContribution_eq_neg_integratedTrace,
    data.hasDerivAt_contribution⟩

end NuclearDuhamelOperatorIntegralData

end
end P0EFTJanusProgramPNuclearDuhamelOperatorIntegral4D
end JanusFormal
