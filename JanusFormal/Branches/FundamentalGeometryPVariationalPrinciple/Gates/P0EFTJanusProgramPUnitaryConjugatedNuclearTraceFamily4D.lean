import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceUnitaryConjugation4D

/-!
# Nuclear trace families transported by unitary conjugation

Let `T_t` be a nuclear operator family and let `F_a` be any family of real
unitary equivalences.  Suppose the moving operator is exactly

```text
T_{a,t} = F_a T_t F_a⁻¹.
```

Intrinsic nuclear trace invariance under unitary conjugation then gives

```text
Tr(T_{a,t}) = Tr(T_t)
```

for every parameter and positive time.  Thus a unitarily transported heat
family has a parameter-independent scalar heat trace, even when its stored
nuclear presentations vary with the parameter.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPUnitaryConjugatedNuclearTraceFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
open P0EFTJanusProgramPIntrinsicNuclearTraceUnitaryConjugation4D

variable {Parameter Time E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Nuclear operator family obtained from one base family by unitary
conjugation. -/
structure UnitaryConjugatedNuclearTraceFamilyData where
  baseOperator : Time → E →L[Real] E
  movingOperator : Parameter → Time → E →L[Real] E
  unitary : Parameter → E ≃ₗᵢ[Real] E
  operator_eq_conjugate : ∀ parameter time,
    movingOperator parameter time =
      unitaryConjugatedOperator (unitary parameter) (baseOperator time)
  baseTraceClass : ∀ time,
    IntrinsicNuclearTraceData (baseOperator time)
  movingTraceClass : ∀ parameter time,
    IntrinsicNuclearTraceData (movingOperator parameter time)

namespace UnitaryConjugatedNuclearTraceFamilyData

/-- Scalar trace of the base operator family. -/
def baseTrace
    (data : UnitaryConjugatedNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E))
    (time : Time) : Real :=
  intrinsicNuclearTrace (data.baseTraceClass time)

/-- Scalar trace of the moving operator family. -/
def movingTrace
    (data : UnitaryConjugatedNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E))
    (parameter : Parameter) (time : Time) : Real :=
  intrinsicNuclearTrace (data.movingTraceClass parameter time)

/-- Unitary conjugation makes the moving scalar trace independent of the
parameter. -/
theorem movingTrace_eq_baseTrace
    (data : UnitaryConjugatedNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E))
    (parameter : Parameter) (time : Time) :
    data.movingTrace parameter time = data.baseTrace time := by
  let target : IntrinsicNuclearTraceData
      (unitaryConjugatedOperator (data.unitary parameter)
        (data.baseOperator time)) :=
    (data.movingTraceClass parameter time).transportOperator
      (data.operator_eq_conjugate parameter time)
  calc
    data.movingTrace parameter time = intrinsicNuclearTrace target := by
      unfold movingTrace target
      symm
      exact (data.movingTraceClass parameter time).
        transportOperator_intrinsicNuclearTrace
          (data.operator_eq_conjugate parameter time)
    _ = intrinsicNuclearTrace (data.baseTraceClass time) :=
      intrinsicNuclearTrace_unitaryConjugation (data.unitary parameter)
        (data.baseTraceClass time) target
    _ = data.baseTrace time := rfl

/-- Equality of the full scalar trace functions. -/
theorem movingTrace_eq_baseTrace_function
    (data : UnitaryConjugatedNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E))
    (parameter : Parameter) :
    data.movingTrace parameter = data.baseTrace := by
  funext time
  exact data.movingTrace_eq_baseTrace parameter time

/-- Public unitary nuclear-trace-family checkpoint. -/
theorem unitary_conjugated_nuclear_trace_family_gate
    (data : UnitaryConjugatedNuclearTraceFamilyData
      (Parameter := Parameter) (Time := Time) (E := E)) :
    (∀ parameter time,
      data.movingTrace parameter time = data.baseTrace time) ∧
    (∀ parameter,
      data.movingTrace parameter = data.baseTrace) :=
  ⟨data.movingTrace_eq_baseTrace,
    data.movingTrace_eq_baseTrace_function⟩

end UnitaryConjugatedNuclearTraceFamilyData

end
end P0EFTJanusProgramPUnitaryConjugatedNuclearTraceFamily4D
end JanusFormal
