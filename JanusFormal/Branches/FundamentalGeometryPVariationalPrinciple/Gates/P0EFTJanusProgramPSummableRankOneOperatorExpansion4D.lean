import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSummableCompactOperatorExpansion4D

/-!
# Summable rank-one expansions and their trace series

A determinant-level relative heat input should expose more than compactness.
This certificate records an explicit norm-summable rank-one expansion and a
summable scalar trace series.  It converts canonically to the compact expansion
used by the preceding frontier.

The scalar series is kept explicit: representation independence and the
identification with an intrinsic operator trace belong to the next trace
uniqueness theorem, not to the definition below.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

set_option autoImplicit false
noncomputable section

universe u

open P0EFTJanusProgramPSummableCompactOperatorExpansion4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E]

/-- Explicit nuclear-style rank-one expansion with a summable trace series. -/
structure SummableRankOneOperatorExpansion
    (operator : E →L[Real] E) where
  Index : Type u
  coefficient : Index → Real
  leftVector : Index → E
  rightVector : Index → E
  summable_nuclearNorm : Summable (fun index =>
    |coefficient index| * ‖leftVector index‖ * ‖rightVector index‖)
  trace_summable : Summable (fun index =>
    coefficient index * inner Real (leftVector index) (rightVector index))
  operator_eq_tsum : operator = ∑' index,
    coefficient index •
      InnerProductSpace.rankOne Real
        (leftVector index) (rightVector index)

/-- One component of the expansion. -/
def SummableRankOneOperatorExpansion.component
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion operator)
    (index : expansion.Index) : E →L[Real] E :=
  expansion.coefficient index •
    InnerProductSpace.rankOne Real
      (expansion.leftVector index) (expansion.rightVector index)

/-- Exact component norm. -/
theorem SummableRankOneOperatorExpansion.component_norm
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion operator)
    (index : expansion.Index) :
    ‖expansion.component index‖ =
      |expansion.coefficient index| * ‖expansion.leftVector index‖ *
        ‖expansion.rightVector index‖ := by
  rw [SummableRankOneOperatorExpansion.component, norm_smul,
    InnerProductSpace.norm_rankOne, Real.norm_eq_abs]
  ring

/-- The component norms are summable. -/
theorem SummableRankOneOperatorExpansion.component_norm_summable
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion operator) :
    Summable (fun index => ‖expansion.component index‖) := by
  simpa only [expansion.component_norm] using expansion.summable_nuclearNorm

/-- Every component is compact. -/
theorem SummableRankOneOperatorExpansion.component_compact
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion operator)
    (index : expansion.Index) :
    IsCompactOperator (expansion.component index) := by
  rw [SummableRankOneOperatorExpansion.component]
  have hRankOne : IsCompactOperator
      (InnerProductSpace.rankOne Real
        (expansion.leftVector index) (expansion.rightVector index)) := by
    rw [InnerProductSpace.rankOne_def']
    exact
      (isCompactOperator_of_locallyCompactSpace_dom
        (innerSL Real (expansion.leftVector index))).clm_comp
          (ContinuousLinearMap.toSpanSingleton Real
            (expansion.rightVector index))
  exact hRankOne.smul (expansion.coefficient index)

/-- Forget trace information and retain the canonical compact expansion. -/
def SummableRankOneOperatorExpansion.toCompactExpansion
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion operator) :
    SummableCompactOperatorExpansion operator where
  Index := expansion.Index
  component := expansion.component
  component_compact := expansion.component_compact
  summable_norm := expansion.component_norm_summable
  operator_eq_tsum := by
    simpa [SummableRankOneOperatorExpansion.component] using
      expansion.operator_eq_tsum

/-- The represented operator is compact. -/
theorem SummableRankOneOperatorExpansion.operator_compact
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion operator) :
    IsCompactOperator operator :=
  expansion.toCompactExpansion.operator_compact

/-- Scalar trace series attached to the explicit rank-one presentation. -/
def SummableRankOneOperatorExpansion.expansionTrace
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion operator) : Real :=
  ∑' index,
    expansion.coefficient index *
      inner Real (expansion.leftVector index) (expansion.rightVector index)

/-- The trace series is the sum of its certified summable family. -/
theorem SummableRankOneOperatorExpansion.hasSum_expansionTrace
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion operator) :
    HasSum
      (fun index => expansion.coefficient index *
        inner Real (expansion.leftVector index) (expansion.rightVector index))
      expansion.expansionTrace :=
  expansion.trace_summable.hasSum

/-- Public rank-one expansion checkpoint. -/
theorem summable_rank_one_operator_expansion_gate
    (operator : E →L[Real] E)
    (expansion : SummableRankOneOperatorExpansion operator) :
    IsCompactOperator operator ∧
      Summable (fun index =>
        expansion.coefficient index *
          inner Real (expansion.leftVector index) (expansion.rightVector index)) :=
  ⟨expansion.operator_compact, expansion.trace_summable⟩

end
end P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
end JanusFormal
