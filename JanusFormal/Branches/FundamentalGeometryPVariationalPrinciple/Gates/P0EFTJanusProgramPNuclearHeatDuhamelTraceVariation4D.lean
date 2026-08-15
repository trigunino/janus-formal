import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceSmul4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D

/-!
# Intrinsic nuclear trace of a Duhamel heat derivative

Let `K_a(t)` be a nuclear heat family.  Suppose its parameter derivative is a
nuclear operator and the operator-level Duhamel identity is

```text
partial_a K_a(t) = (-t) • D_a(t).
```

If differentiation of the intrinsic scalar trace is identified with the trace
of the operator derivative, scalar linearity of the nuclear trace gives

```text
partial_a Tr(K_a(t)) = -t * Tr(D_a(t)).
```

This is the pointwise heat-trace formula consumed by the logarithmically
weighted short- and long-time integrals.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceSmul4D
open P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Nuclear heat family with an operator-level Duhamel derivative and scalar
trace differentiability. -/
structure NuclearHeatDuhamelTraceVariationData where
  heatOperator : Real → HeatTime → E →L[Real] E
  heatDerivativeOperator : Real → HeatTime → E →L[Real] E
  duhamelOperator : Real → HeatTime → E →L[Real] E
  heatTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData (heatOperator parameter time)
  heatDerivativeTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData (heatDerivativeOperator parameter time)
  duhamelTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData (duhamelOperator parameter time)
  heatDerivativeOperator_eq : ∀ parameter time,
    heatDerivativeOperator parameter time =
      (-(time.1) : Real) • duhamelOperator parameter time
  trace_hasDerivAt : ∀ parameter time,
    HasDerivAt
      (fun current => intrinsicNuclearTrace (heatTraceClass current time))
      (intrinsicNuclearTrace (heatDerivativeTraceClass parameter time))
      parameter

namespace NuclearHeatDuhamelTraceVariationData

/-- Scalar heat trace. -/
def heatTrace
    (data : NuclearHeatDuhamelTraceVariationData (E := E))
    (parameter : Real) (time : HeatTime) : Real :=
  intrinsicNuclearTrace (data.heatTraceClass parameter time)

/-- Scalar trace of the heat derivative operator. -/
def heatTraceDerivative
    (data : NuclearHeatDuhamelTraceVariationData (E := E))
    (parameter : Real) (time : HeatTime) : Real :=
  intrinsicNuclearTrace (data.heatDerivativeTraceClass parameter time)

/-- Scalar Duhamel trace. -/
def duhamelTrace
    (data : NuclearHeatDuhamelTraceVariationData (E := E))
    (parameter : Real) (time : HeatTime) : Real :=
  intrinsicNuclearTrace (data.duhamelTraceClass parameter time)

/-- Trace of the operator derivative is `-t` times the Duhamel trace. -/
theorem heatTraceDerivative_eq_neg_time_mul_duhamelTrace
    (data : NuclearHeatDuhamelTraceVariationData (E := E))
    (parameter : Real) (time : HeatTime) :
    data.heatTraceDerivative parameter time =
      -(time.1) * data.duhamelTrace parameter time := by
  let transported : IntrinsicNuclearTraceData
      ((-(time.1) : Real) • data.duhamelOperator parameter time) :=
    (data.heatDerivativeTraceClass parameter time).transportOperator
      (data.heatDerivativeOperator_eq parameter time)
  calc
    data.heatTraceDerivative parameter time =
        intrinsicNuclearTrace transported := by
      unfold heatTraceDerivative transported
      symm
      exact (data.heatDerivativeTraceClass parameter time).
        transportOperator_intrinsicNuclearTrace
          (data.heatDerivativeOperator_eq parameter time)
    _ = -(time.1) *
        intrinsicNuclearTrace (data.duhamelTraceClass parameter time) :=
      intrinsicNuclearTrace_smul (-(time.1))
        (data.duhamelTraceClass parameter time) transported
    _ = -(time.1) * data.duhamelTrace parameter time := rfl

/-- Pointwise scalar trace Duhamel formula. -/
theorem heatTrace_hasDerivAt
    (data : NuclearHeatDuhamelTraceVariationData (E := E))
    (parameter : Real) (time : HeatTime) :
    HasDerivAt (fun current => data.heatTrace current time)
      (-(time.1) * data.duhamelTrace parameter time) parameter := by
  rw [← data.heatTraceDerivative_eq_neg_time_mul_duhamelTrace parameter time]
  exact data.trace_hasDerivAt parameter time

/-- Public nuclear Duhamel trace checkpoint. -/
theorem nuclear_heat_duhamel_trace_variation_gate
    (data : NuclearHeatDuhamelTraceVariationData (E := E)) :
    (∀ parameter time,
      data.heatTraceDerivative parameter time =
        -(time.1) * data.duhamelTrace parameter time) ∧
    (∀ parameter time,
      HasDerivAt (fun current => data.heatTrace current time)
        (-(time.1) * data.duhamelTrace parameter time) parameter) :=
  ⟨data.heatTraceDerivative_eq_neg_time_mul_duhamelTrace,
    data.heatTrace_hasDerivAt⟩

end NuclearHeatDuhamelTraceVariationData

end
end P0EFTJanusProgramPNuclearHeatDuhamelTraceVariation4D
end JanusFormal
