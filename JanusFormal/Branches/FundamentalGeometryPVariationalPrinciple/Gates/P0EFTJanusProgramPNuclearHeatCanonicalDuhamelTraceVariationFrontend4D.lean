import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceIsometricEquivalenceTransport4D

/-!
# Canonical nuclear Duhamel trace-variation frontend

The nonzero heat-time factor canonically transports a nuclear certificate for
the Duhamel operator to one for its `-t` multiple.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatCanonicalDuhamelTraceVariationFrontend4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceSmul4D
open P0EFTJanusProgramPIntrinsicNuclearTraceIsometricEquivalenceTransport4D
open P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- A nonzero scalar multiple inherits intrinsic nuclear trace data. -/
def intrinsicNuclearTraceData_smul_of_ne_zero
    {operator : E →L[Real] E}
    (source : IntrinsicNuclearTraceData.{u, v} operator)
    (scalar : Real) (hScalar : scalar ≠ 0) :
    IntrinsicNuclearTraceData.{u, v} (scalar • operator) :=
  intrinsicNuclearTraceData_of_expansion (source.expansion.smul scalar) (by
    intro other
    let pulledRaw := other.smul scalar⁻¹
    have hOperator : scalar⁻¹ • (scalar • operator) = operator := by
      rw [smul_smul, inv_mul_cancel₀ hScalar, one_smul]
    let pulled := transportExpansionOperator pulledRaw hOperator
    have hTrace :
        scalar⁻¹ * other.expansionTrace =
          source.expansion.expansionTrace := by
      calc
        scalar⁻¹ * other.expansionTrace = pulledRaw.expansionTrace :=
          (other.smul_expansionTrace scalar⁻¹).symm
        _ = pulled.expansionTrace :=
          (transportExpansionOperator_expansionTrace pulledRaw hOperator).symm
        _ = source.expansion.expansionTrace :=
          source.presentation_independent pulled
    calc
      other.expansionTrace =
          scalar * (scalar⁻¹ * other.expansionTrace) := by
        rw [← mul_assoc, mul_inv_cancel₀ hScalar, one_mul]
      _ = scalar * source.expansion.expansionTrace :=
        congrArg (fun value : Real => scalar * value) hTrace
      _ = (source.expansion.smul scalar).expansionTrace :=
        (source.expansion.smul_expansionTrace scalar).symm)

@[simp] theorem intrinsicNuclearTraceData_smul_of_ne_zero_trace
    {operator : E →L[Real] E}
    (source : IntrinsicNuclearTraceData.{u, v} operator)
    (scalar : Real) (hScalar : scalar ≠ 0) :
    intrinsicNuclearTrace
        (intrinsicNuclearTraceData_smul_of_ne_zero source scalar hScalar) =
      scalar * intrinsicNuclearTrace source :=
  intrinsicNuclearTrace_smul scalar source
    (intrinsicNuclearTraceData_smul_of_ne_zero source scalar hScalar)

/-- The Duhamel certificate scaled by the canonical nonzero heat-time factor. -/
def canonicalDuhamelDerivativeTraceClass
    (duhamelOperator : Real → HeatTime → E →L[Real] E)
    (duhamelTraceClass : ∀ parameter time,
      IntrinsicNuclearTraceData.{u, v} (duhamelOperator parameter time))
    (parameter : Real) (time : HeatTime) :
    IntrinsicNuclearTraceData.{u, v}
      ((-(time.1) : Real) • duhamelOperator parameter time) :=
  intrinsicNuclearTraceData_smul_of_ne_zero
    (duhamelTraceClass parameter time) (-(time.1))
    (neg_ne_zero.mpr (ne_of_gt time.2))

/-- Minimal input for the canonical operator-level Duhamel identity. -/
structure NuclearHeatCanonicalDuhamelTraceVariationFrontendData where
  heatOperator : Real → HeatTime → E →L[Real] E
  duhamelOperator : Real → HeatTime → E →L[Real] E
  heatTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData.{u, v} (heatOperator parameter time)
  duhamelTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData.{u, v} (duhamelOperator parameter time)
  trace_hasDerivAt : ∀ parameter time,
    HasDerivAt
      (fun current => intrinsicNuclearTrace (heatTraceClass current time))
      (-(time.1) * intrinsicNuclearTrace
        (duhamelTraceClass parameter time))
      parameter

namespace NuclearHeatCanonicalDuhamelTraceVariationFrontendData

/-- Close the standard variation packet using the canonical `-t` multiple. -/
def toNuclearHeatDuhamelTraceVariationData
    (data : NuclearHeatCanonicalDuhamelTraceVariationFrontendData.{u, v}
      (E := E)) :
    NuclearHeatDuhamelTraceVariationData.{u, v} (E := E) where
  heatOperator := data.heatOperator
  heatDerivativeOperator := fun parameter time =>
    (-(time.1) : Real) • data.duhamelOperator parameter time
  duhamelOperator := data.duhamelOperator
  heatTraceClass := data.heatTraceClass
  heatDerivativeTraceClass :=
    canonicalDuhamelDerivativeTraceClass
      data.duhamelOperator data.duhamelTraceClass
  duhamelTraceClass := data.duhamelTraceClass
  heatDerivativeOperator_eq := by
    intro parameter time
    rfl
  trace_hasDerivAt := by
    intro parameter time
    simpa [canonicalDuhamelDerivativeTraceClass] using
      data.trace_hasDerivAt parameter time

end NuclearHeatCanonicalDuhamelTraceVariationFrontendData

end
end P0EFTJanusProgramPNuclearHeatCanonicalDuhamelTraceVariationFrontend4D
end JanusFormal
