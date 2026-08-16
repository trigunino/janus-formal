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

end
end P0EFTJanusProgramPIntrinsicNuclearTraceUnitaryConjugation4D
namespace P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
namespace SummableRankOneOperatorExpansion

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPIntrinsicNuclearTraceUnitaryConjugation4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Conjugate a summable rank-one presentation by one unitary equivalence. -/
def unitaryConjugate
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
    have hSummable : Summable data.component :=
      Summable.of_norm data.component_norm_summable
    have hOperator : operator = ∑' index, data.component index := by
      simpa [SummableRankOneOperatorExpansion.component] using
        data.operator_eq_tsum
    let rightComposition :
        (E →L[Real] E) →L[Real] (E →L[Real] E) :=
      (ContinuousLinearMap.compL Real E E E).flip
        unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap
    let leftComposition :
        (E →L[Real] E) →L[Real] (E →L[Real] E) :=
      ContinuousLinearMap.compL Real E E E
        unitary.toContinuousLinearEquiv.toContinuousLinearMap
    calc
      unitaryConjugatedOperator unitary operator =
          leftComposition (rightComposition operator) := rfl
      _ = leftComposition (rightComposition
          (∑' index, data.component index)) :=
        congrArg (fun current => leftComposition (rightComposition current))
          hOperator
      _ = leftComposition (∑' index, rightComposition (data.component index)) :=
        congrArg leftComposition (rightComposition.map_tsum hSummable)
      _ = ∑' index, leftComposition (rightComposition (data.component index)) :=
        leftComposition.map_tsum
          (hSummable.map rightComposition rightComposition.continuous)
      _ = ∑' index, data.coefficient index •
          InnerProductSpace.rankOne Real (unitary (data.leftVector index))
            (unitary (data.rightVector index)) := by
        apply tsum_congr
        intro index
        ext vector
        simp [leftComposition, rightComposition,
          SummableRankOneOperatorExpansion.component,
          InnerProductSpace.rankOne_apply,
          unitary.inner_map_eq_flip]

@[simp]
theorem unitaryConjugate_expansionTrace
    {operator : E →L[Real] E}
    (data : SummableRankOneOperatorExpansion operator)
    (unitary : E ≃ₗᵢ[Real] E) :
    (data.unitaryConjugate unitary).expansionTrace = data.expansionTrace := by
  simp [SummableRankOneOperatorExpansion.expansionTrace,
    SummableRankOneOperatorExpansion.unitaryConjugate]

end
end SummableRankOneOperatorExpansion
end P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
namespace P0EFTJanusProgramPIntrinsicNuclearTraceUnitaryConjugation4D

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Intrinsic nuclear trace is invariant under unitary conjugation. -/
theorem intrinsicNuclearTrace_unitaryConjugation
    {operator : E →L[Real] E}
    (unitary : E ≃ₗᵢ[Real] E)
    (source : IntrinsicNuclearTraceData.{u, v} operator)
    (target : IntrinsicNuclearTraceData.{u, v}
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
    (source : IntrinsicNuclearTraceData.{u, v} operator)
    (target : IntrinsicNuclearTraceData.{u, v}
      (unitaryConjugatedOperator unitary operator)) :
    (source.expansion.unitaryConjugate unitary).expansionTrace =
        source.expansion.expansionTrace ∧
    intrinsicNuclearTrace target = intrinsicNuclearTrace source :=
  ⟨source.expansion.unitaryConjugate_expansionTrace unitary,
    intrinsicNuclearTrace_unitaryConjugation unitary source target⟩

end
end P0EFTJanusProgramPIntrinsicNuclearTraceUnitaryConjugation4D
end JanusFormal
