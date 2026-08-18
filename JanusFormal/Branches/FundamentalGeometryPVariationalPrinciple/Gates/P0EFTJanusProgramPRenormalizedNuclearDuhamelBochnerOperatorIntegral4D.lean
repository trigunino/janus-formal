import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssembly4D

/-!
# Bochner construction of the renormalized short-time Duhamel operator

The UV-renormalized operator is integrated as one operator-valued function;
the raw Duhamel term and counterterm are never integrated separately.

The current intrinsic nuclear-trace API has no nuclear norm and hence no
continuous trace functional.  `IntrinsicNuclearTraceBochnerBridgeData` isolates
exactly that missing bridge: the Bochner integral is nuclear and intrinsic
trace commutes with this integral.  Given this bridge, the operator, its trace
certificate, and the scalar trace identity required by the boundary assembly
are outputs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRenormalizedNuclearDuhamelBochnerOperatorIntegral4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearHeatDuhamelCountertermSubtractedShortTimeQuadratic4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
open P0EFTJanusProgramPProductThroatSphereNuclearBasepointOperatorBoundaryFinitePartAssembly4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- The sole bridge not supplied by operator-norm Bochner integration: the
integral remains nuclear and intrinsic trace commutes with that integral. -/
structure IntrinsicNuclearTraceBochnerBridgeData
    (timeRegion : Set Real)
    (integrand : Real → E →L[Real] E)
    (pointwiseTraceClass : ∀ time,
      IntrinsicNuclearTraceData.{u, v} (integrand time)) where
  integralTraceClass :
    IntrinsicNuclearTraceData.{u, v} (∫ time in timeRegion, integrand time)
  trace_integral_commutes :
    intrinsicNuclearTrace integralTraceClass =
      ∫ time in timeRegion,
        intrinsicNuclearTrace (pointwiseTraceClass time)

/-- A single Bochner-integrable, already-renormalized short-time operator
integrand whose pointwise intrinsic trace is the renormalized scalar Duhamel
trace. -/
structure RenormalizedNuclearDuhamelBochnerOperatorIntegralData
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1) where
  operatorIntegrand : Real → Real → E →L[Real] E
  operatorIntegrable : ∀ parameter,
    Integrable (operatorIntegrand parameter)
      (volume.restrict (Set.Ioo (0 : Real) 1))
  pointwiseTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData.{u, v} (operatorIntegrand parameter time)
  pointwiseTrace_eq_renormalized : ∀ parameter,
    ∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1),
      intrinsicNuclearTrace (pointwiseTraceClass parameter time) =
        shortTime.renormalizedDuhamelTrace parameter time
  traceIntegralBridge : ∀ parameter,
    IntrinsicNuclearTraceBochnerBridgeData.{u, v}
      (Set.Ioo (0 : Real) 1) (operatorIntegrand parameter)
        (pointwiseTraceClass parameter)

namespace RenormalizedNuclearDuhamelBochnerOperatorIntegralData

/-- The integrated short-time operator is the Bochner integral, rather than
an independently supplied operator. -/
def integratedOperator
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : RenormalizedNuclearDuhamelBochnerOperatorIntegralData
      nuclear shortTime)
    (parameter : Real) : E →L[Real] E :=
  ∫ time in Set.Ioo (0 : Real) 1, data.operatorIntegrand parameter time

/-- Nuclearity of the integrated operator is exactly the nuclear bridge's
first output. -/
def integratedTraceClass
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : RenormalizedNuclearDuhamelBochnerOperatorIntegralData
      nuclear shortTime)
    (parameter : Real) :
    IntrinsicNuclearTraceData.{u, v} (data.integratedOperator parameter) :=
  (data.traceIntegralBridge parameter).integralTraceClass

/-- The pointwise intrinsic trace is integrable because it agrees almost
everywhere with the already-proved integrable renormalized Duhamel trace. -/
theorem pointwiseTrace_integrable
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : RenormalizedNuclearDuhamelBochnerOperatorIntegralData
      nuclear shortTime)
    (parameter : Real) :
    Integrable
      (fun time ↦
        intrinsicNuclearTrace (data.pointwiseTraceClass parameter time))
      (volume.restrict (Set.Ioo (0 : Real) 1)) := by
  apply (shortTime.renormalizedDuhamelTrace_integrable parameter).congr
  filter_upwards [data.pointwiseTrace_eq_renormalized parameter] with time hTime
  exact hTime.symm

/-- Trace of the single renormalized Bochner integral equals the scalar
renormalized Duhamel integral. -/
theorem scalarIntegral_eq_intrinsicTrace
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : RenormalizedNuclearDuhamelBochnerOperatorIntegralData
      nuclear shortTime)
    (parameter : Real) :
    (∫ time in Set.Ioo (0 : Real) 1,
      shortTime.renormalizedDuhamelTrace parameter time) =
        intrinsicNuclearTrace (data.integratedTraceClass parameter) := by
  calc
    (∫ time in Set.Ioo (0 : Real) 1,
        shortTime.renormalizedDuhamelTrace parameter time) =
      ∫ time in Set.Ioo (0 : Real) 1,
        intrinsicNuclearTrace
          (data.pointwiseTraceClass parameter time) := by
      apply integral_congr_ae
      filter_upwards [data.pointwiseTrace_eq_renormalized parameter] with time hTime
      exact hTime.symm
    _ = intrinsicNuclearTrace (data.integratedTraceClass parameter) :=
      (data.traceIntegralBridge parameter).trace_integral_commutes.symm

/-- Conversion to the renormalized operator-integral input of the signed
boundary assembly. -/
def toRenormalizedOperatorIntegral
    {nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E)}
    {shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1}
    (data : RenormalizedNuclearDuhamelBochnerOperatorIntegralData
      nuclear shortTime) :
    RenormalizedNuclearDuhamelOperatorIntegralData.{u, v} nuclear shortTime where
  integratedOperator := data.integratedOperator
  integratedTraceClass := data.integratedTraceClass
  scalarIntegral_eq_trace := data.scalarIntegral_eq_intrinsicTrace

/-- Public checkpoint: no independent integrated operator or scalar trace
identity remains in the Bochner input packet. -/
theorem renormalized_nuclear_duhamel_bochner_operator_integral_gate
    (nuclear : NuclearHeatDuhamelTraceVariationData.{u, v} (E := E))
    (shortTime : NuclearHeatDuhamelCountertermSubtractedShortTimeQuadraticData
      nuclear 1)
    (data : RenormalizedNuclearDuhamelBochnerOperatorIntegralData
      nuclear shortTime) :
    (data.toRenormalizedOperatorIntegral.integratedOperator =
      fun parameter ↦
        ∫ time in Set.Ioo (0 : Real) 1,
          data.operatorIntegrand parameter time) ∧
    (∀ parameter,
      (∫ time in Set.Ioo (0 : Real) 1,
        shortTime.renormalizedDuhamelTrace parameter time) =
          intrinsicNuclearTrace
            (data.toRenormalizedOperatorIntegral.integratedTraceClass
              parameter)) :=
  ⟨rfl, data.scalarIntegral_eq_intrinsicTrace⟩

end RenormalizedNuclearDuhamelBochnerOperatorIntegralData

end
end P0EFTJanusProgramPRenormalizedNuclearDuhamelBochnerOperatorIntegral4D
end JanusFormal
