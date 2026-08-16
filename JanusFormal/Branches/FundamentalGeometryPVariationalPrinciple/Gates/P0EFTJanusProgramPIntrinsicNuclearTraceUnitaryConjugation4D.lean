import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Intrinsic nuclear trace under unitary conjugation

A summable rank-one expansion

```text
T = sum_i c_i |u_i><v_i|
```

is transported by a real unitary equivalence `U` to

```text
U T U⁻¹ = sum_i c_i |U u_i><U v_i|.
```

The nuclear summability bound is unchanged and every trace summand is preserved
because `U` preserves norms and inner products.  Therefore intrinsic nuclear
traces are invariant under unitary conjugation.

This is the operator-theoretic input needed to compare heat traces in a moving
D11 unitary frame without selecting a second presentation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicNuclearTraceUnitaryConjugation4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Bounded operator obtained by conjugating `operator` with a unitary
equivalence. -/
def unitaryConjugatedOperator
    (unitary : E ≃ₗᵢ[Real] E)
    (operator : E →L[Real] E) : E →L[Real] E :=
  unitary.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (operator.comp
      unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem unitaryConjugatedOperator_apply
    (unitary : E ≃ₗᵢ[Real] E)
    (operator : E →L[Real] E) (vector : E) :
    unitaryConjugatedOperator unitary operator vector =
      unitary (operator (unitary.symm vector)) :=
  rfl

/-- Conjugate a summable rank-one presentation by one unitary equivalence. -/
def SummableRankOneOperatorExpansion.unitaryConjugate
    {operator : E →L[Real] E}
    (data : SummableRankOneOperatorExpansion operator)
    (unitary : E ≃ₗᵢ[Real] E) :
    SummableRankOneOperatorExpansion
      (unitaryConjugatedOperator unitary operator) where
  Index := data.Index
  coefficient := data.coefficient
  leftVector := fun index => unitary (data.leftVector index)
  rightVector := fun index => unitary (data.rightVector index)
  summable_nuclearNorm := by
    simpa using data.summable_nuclearNorm
  trace_summable := by
    simpa using data.trace_summable
  operator_eq_tsum := by
    ext vector
    change unitary (operator (unitary.symm vector)) = _
    rw [data.operator_eq_tsum]
    simp [rankOneOperator, unitaryConjugatedOperator]

@[simp]
theorem SummableRankOneOperatorExpansion.unitaryConjugate_expansionTrace
    {operator : E →L[Real] E}
    (data : SummableRankOneOperatorExpansion operator)
    (unitary : E ≃ₗᵢ[Real] E) :
    (data.unitaryConjugate unitary).expansionTrace = data.expansionTrace := by
  simp [SummableRankOneOperatorExpansion.expansionTrace,
    SummableRankOneOperatorExpansion.unitaryConjugate]

/-- Intrinsic nuclear trace is invariant under unitary conjugation. -/
theorem intrinsicNuclearTrace_unitaryConjugation
    {operator : E →L[Real] E}
    (unitary : E ≃ₗᵢ[Real] E)
    (source : IntrinsicNuclearTraceData operator)
    (target : IntrinsicNuclearTraceData
      (unitaryConjugatedOperator unitary operator)) :
    intrinsicNuclearTrace target = intrinsicNuclearTrace source := by
  calc
    intrinsicNuclearTrace target =
        (source.expansion.unitaryConjugate unitary).expansionTrace :=
      (target.expansionTrace_eq
        (source.expansion.unitaryConjugate unitary)).symm
    _ = source.expansion.expansionTrace :=
      source.expansion.unitaryConjugate_expansionTrace unitary
    _ = intrinsicNuclearTrace source := rfl

/-- The transported explicit presentation and the two intrinsic traces agree. -/
theorem intrinsic_nuclear_trace_unitary_conjugation_gate
    {operator : E →L[Real] E}
    (unitary : E ≃ₗᵢ[Real] E)
    (source : IntrinsicNuclearTraceData operator)
    (target : IntrinsicNuclearTraceData
      (unitaryConjugatedOperator unitary operator)) :
    (source.expansion.unitaryConjugate unitary).expansionTrace =
        source.expansion.expansionTrace ∧
    intrinsicNuclearTrace target = intrinsicNuclearTrace source :=
  ⟨source.expansion.unitaryConjugate_expansionTrace unitary,
    intrinsicNuclearTrace_unitaryConjugation unitary source target⟩

end
end P0EFTJanusProgramPIntrinsicNuclearTraceUnitaryConjugation4D
end JanusFormal
