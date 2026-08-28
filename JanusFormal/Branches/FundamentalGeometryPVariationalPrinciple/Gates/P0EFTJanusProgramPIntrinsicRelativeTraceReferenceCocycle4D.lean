import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D

/-!
# Change-of-reference cocycle for intrinsic logarithmic traces

Fix one actual reduced family `H_a` and several reference families `R^i_a` on
the same Hilbert space.  Once every logarithmic derivative has an intrinsic
nuclear trace, all change-of-reference identities are algebraic consequences:

`Tr(H/R_j) = Tr(H/R_i) + Tr(R_i/R_j)`.

This file packages that fact before any zeta or determinant coordinates are
introduced.  The reference-change traces satisfy identity, inversion and Cech
cocycle laws, while the local Bismut--Freed coefficients differ by precisely
the corresponding reference trace.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicRelativeTraceReferenceCocycle4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1500000

noncomputable section

open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D

universe u v w

variable {E : Type u} {Index : Type w}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- One actual logarithmic trace and a family of reference logarithmic traces. -/
structure IntrinsicRelativeTraceReferenceCocycleData
    (actual : Real → E →L[Real] E)
    (reference : Index → Real → E →L[Real] E) where
  actualTrace : IntrinsicLogarithmicDerivativeTraceData.{u, v} actual
  referenceTrace : ∀ index,
    IntrinsicLogarithmicDerivativeTraceData.{u, v} (reference index)

namespace IntrinsicRelativeTraceReferenceCocycleData

/-- Actual-minus-reference trace packet in chart `index`. -/
def localRelativeTraceData
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (index : Index) :
    RelativeIntrinsicLogarithmicDerivativeTraceData actual (reference index) where
  actualTrace := data.actualTrace
  referenceTrace := data.referenceTrace index

/-- Reference-`first` minus reference-`second` trace packet. -/
def referenceChangeTraceData
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (first second : Index) :
    RelativeIntrinsicLogarithmicDerivativeTraceData
      (reference first) (reference second) where
  actualTrace := data.referenceTrace first
  referenceTrace := data.referenceTrace second

/-- Local relative logarithmic trace `Tr(H/R_i)`. -/
def localTrace
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (index : Index) (parameter : Real) : Real :=
  (data.localRelativeTraceData index).trace parameter

/-- Intrinsic reference-change trace `Tr(R_i/R_j)`. -/
def referenceChangeTrace
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (first second : Index) (parameter : Real) : Real :=
  (data.referenceChangeTraceData first second).trace parameter

/-- Local Bismut--Freed coefficient in chart `index`. -/
def localCoefficient
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (index : Index) (parameter : Real) : Complex :=
  (-(data.localTrace index parameter) : Real)

/-- Changing reference adds the intrinsic reference-change trace. -/
theorem localTrace_changeReference
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (first second : Index) (parameter : Real) :
    data.localTrace second parameter =
      data.localTrace first parameter +
        data.referenceChangeTrace first second parameter := by
  unfold localTrace referenceChangeTrace localRelativeTraceData
    referenceChangeTraceData
    RelativeIntrinsicLogarithmicDerivativeTraceData.trace
    IntrinsicLogarithmicDerivativeTraceData.trace
  ring

/-- Difference form of the same identity. -/
theorem localTrace_sub
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (first second : Index) (parameter : Real) :
    data.localTrace second parameter - data.localTrace first parameter =
      data.referenceChangeTrace first second parameter := by
  rw [data.localTrace_changeReference first second parameter]
  ring

/-- Identity reference change. -/
@[simp]
theorem referenceChangeTrace_self
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (index : Index) (parameter : Real) :
    data.referenceChangeTrace index index parameter = 0 := by
  unfold referenceChangeTrace referenceChangeTraceData
    RelativeIntrinsicLogarithmicDerivativeTraceData.trace
  ring

/-- Reversing the reference change negates its trace. -/
theorem referenceChangeTrace_reverse
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (first second : Index) (parameter : Real) :
    data.referenceChangeTrace second first parameter =
      -data.referenceChangeTrace first second parameter := by
  unfold referenceChangeTrace referenceChangeTraceData
    RelativeIntrinsicLogarithmicDerivativeTraceData.trace
  ring

/-- Exact additive Cech cocycle for three references. -/
theorem referenceChangeTrace_cocycle
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (first second third : Index) (parameter : Real) :
    data.referenceChangeTrace first second parameter +
        data.referenceChangeTrace second third parameter =
      data.referenceChangeTrace first third parameter := by
  unfold referenceChangeTrace referenceChangeTraceData
    RelativeIntrinsicLogarithmicDerivativeTraceData.trace
  ring

/-- Difference of local Bismut--Freed coefficients is the reference-change
trace.  This is exactly the logarithmic derivative of the determinant
transition from chart `first` to chart `second`. -/
theorem localCoefficient_sub
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (first second : Index) (parameter : Real) :
    data.localCoefficient first parameter - data.localCoefficient second parameter =
      (data.referenceChangeTrace first second parameter : Complex) := by
  unfold localCoefficient
  rw [← data.localTrace_sub first second parameter]
  push_cast
  ring

/-- Every local coefficient is the intrinsic coefficient of its exact
actual-minus-reference packet. -/
theorem localCoefficient_eq
    {actual : Real → E →L[Real] E}
    {reference : Index → Real → E →L[Real] E}
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference)
    (index : Index) (parameter : Real) :
    data.localCoefficient index parameter =
      (data.localRelativeTraceData index).bismutFreedCoefficient parameter := by
  rfl

/-- Public reference-cocycle checkpoint. -/
theorem intrinsic_relative_trace_reference_cocycle_gate
    (actual : Real → E →L[Real] E)
    (reference : Index → Real → E →L[Real] E)
    (data : IntrinsicRelativeTraceReferenceCocycleData actual reference) :
    (∀ first second parameter,
      data.localTrace second parameter =
        data.localTrace first parameter +
          data.referenceChangeTrace first second parameter) ∧
      (∀ index parameter,
        data.referenceChangeTrace index index parameter = 0) ∧
      (∀ first second parameter,
        data.referenceChangeTrace second first parameter =
          -data.referenceChangeTrace first second parameter) ∧
      (∀ first second third parameter,
        data.referenceChangeTrace first second parameter +
            data.referenceChangeTrace second third parameter =
          data.referenceChangeTrace first third parameter) ∧
      (∀ first second parameter,
        data.localCoefficient first parameter -
            data.localCoefficient second parameter =
          (data.referenceChangeTrace first second parameter : Complex)) :=
  ⟨data.localTrace_changeReference,
    data.referenceChangeTrace_self,
    data.referenceChangeTrace_reverse,
    data.referenceChangeTrace_cocycle,
    data.localCoefficient_sub⟩

end IntrinsicRelativeTraceReferenceCocycleData

end
end P0EFTJanusProgramPIntrinsicRelativeTraceReferenceCocycle4D
end JanusFormal
