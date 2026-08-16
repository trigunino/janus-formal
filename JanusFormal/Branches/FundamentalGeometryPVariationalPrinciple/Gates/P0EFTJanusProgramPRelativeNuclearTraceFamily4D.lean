import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinAnalyticDifference4D

/-!
# Relative nuclear trace families

A relative heat operator is defined operator-theoretically by

```text
K_rel(a,t) = K_actual(a,t) - K_reference(a,t).
```

When all three operators carry intrinsic nuclear-trace certificates, trace
additivity forces the scalar equality

```text
h_rel(a,t) = h_actual(a,t) - h_reference(a,t).
```

This file derives that equality from the operator identity and provides it in
the exact form consumed by the analytic Mellin-difference family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeNuclearTraceFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceSubtraction4D
open P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifference4D

variable {Parameter Time E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Actual/reference/relative nuclear operator family with the exact operator
subtraction law. -/
structure RelativeNuclearTraceFamilyData where
  actualOperator : Parameter → Time → E →L[Real] E
  referenceOperator : Parameter → Time → E →L[Real] E
  relativeOperator : Parameter → Time → E →L[Real] E
  operator_eq_sub : ∀ parameter time,
    relativeOperator parameter time =
      actualOperator parameter time - referenceOperator parameter time
  actualTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData (actualOperator parameter time)
  referenceTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData (referenceOperator parameter time)
  relativeTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData (relativeOperator parameter time)

namespace RelativeNuclearTraceFamilyData

/-- Actual scalar nuclear trace. -/
def actualTrace
    (data : RelativeNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E))
    (parameter : Parameter) (time : Time) : Real :=
  intrinsicNuclearTrace (data.actualTraceClass parameter time)

/-- Reference scalar nuclear trace. -/
def referenceTrace
    (data : RelativeNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E))
    (parameter : Parameter) (time : Time) : Real :=
  intrinsicNuclearTrace (data.referenceTraceClass parameter time)

/-- Relative scalar nuclear trace. -/
def relativeTrace
    (data : RelativeNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E))
    (parameter : Parameter) (time : Time) : Real :=
  intrinsicNuclearTrace (data.relativeTraceClass parameter time)

/-- Relative scalar trace is the actual trace minus the reference trace. -/
theorem relativeTrace_eq_difference
    (data : RelativeNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E))
    (parameter : Parameter) (time : Time) :
    data.relativeTrace parameter time =
      data.actualTrace parameter time - data.referenceTrace parameter time := by
  let transported : IntrinsicNuclearTraceData
      (data.actualOperator parameter time - data.referenceOperator parameter time) :=
    (data.relativeTraceClass parameter time).transportOperator
      (data.operator_eq_sub parameter time)
  calc
    data.relativeTrace parameter time = intrinsicNuclearTrace transported := by
      unfold relativeTrace transported
      symm
      exact (data.relativeTraceClass parameter time).
        transportOperator_intrinsicNuclearTrace
          (data.operator_eq_sub parameter time)
    _ = intrinsicNuclearTrace (data.actualTraceClass parameter time) -
        intrinsicNuclearTrace (data.referenceTraceClass parameter time) :=
      intrinsicNuclearTrace_sub
        (data.actualTraceClass parameter time)
        (data.referenceTraceClass parameter time) transported
    _ = data.actualTrace parameter time - data.referenceTrace parameter time :=
      rfl

/-- Equality of scalar trace functions for one parameter. -/
theorem relativeTrace_eq_difference_function
    (data : RelativeNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E))
    (parameter : Parameter) :
    data.relativeTrace parameter =
      heatTraceDifference (data.actualTrace parameter)
        (data.referenceTrace parameter) := by
  funext time
  exact data.relativeTrace_eq_difference parameter time

/-- Public relative nuclear-trace-family checkpoint. -/
theorem relative_nuclear_trace_family_gate
    (data : RelativeNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E)) :
    (∀ parameter time,
      data.relativeTrace parameter time =
        data.actualTrace parameter time - data.referenceTrace parameter time) ∧
    (∀ parameter,
      data.relativeTrace parameter =
        heatTraceDifference (data.actualTrace parameter)
          (data.referenceTrace parameter)) :=
  ⟨data.relativeTrace_eq_difference,
    data.relativeTrace_eq_difference_function⟩

end RelativeNuclearTraceFamilyData

end
end P0EFTJanusProgramPRelativeNuclearTraceFamily4D
end JanusFormal
