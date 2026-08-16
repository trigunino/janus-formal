import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Summable compact-operator expansions

A norm-summable family of compact continuous linear maps has a compact operator
sum.  This small reusable certificate is the appropriate analytic object for
relative heat and determinant work: unlike the bounded Hessian exponential
itself, a *difference* of two evolutions may have such an expansion in an
infinite-dimensional space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSummableCompactOperatorExpansion4D

set_option autoImplicit false
noncomputable section

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- Explicit norm-summable expansion of one bounded operator into compact
components. -/
structure SummableCompactOperatorExpansion
    (operator : E →L[Real] E) where
  Index : Type u
  component : Index → E →L[Real] E
  component_compact : ∀ index, IsCompactOperator (component index)
  summable_norm : Summable (fun index => ‖component index‖)
  operator_eq_tsum : operator = ∑' index, component index

/-- The operator represented by a summable compact expansion is compact. -/
theorem SummableCompactOperatorExpansion.operator_compact
    {operator : E →L[Real] E}
    (expansion : SummableCompactOperatorExpansion operator) :
    IsCompactOperator operator := by
  letI : DecidableEq expansion.Index := Classical.decEq _
  have hSummable : Summable expansion.component :=
    Summable.of_norm expansion.summable_norm
  rw [expansion.operator_eq_tsum]
  refine isCompactOperator_of_tendsto
    (l := (SummationFilter.unconditional expansion.Index).filter)
    (F := fun modes : Finset expansion.Index =>
      ∑ index ∈ modes, expansion.component index)
    (f := ∑' index, expansion.component index)
    hSummable.hasSum ?_
  filter_upwards [] with modes
  refine Finset.sum_induction
    (fun index => expansion.component index)
    (fun current => IsCompactOperator current)
    (fun _ _ hFirst hSecond => hFirst.add hSecond)
    isCompactOperator_zero ?_
  intro index _
  exact expansion.component_compact index

/-- A zero expansion. -/
def SummableCompactOperatorExpansion.zero :
    SummableCompactOperatorExpansion (0 : E →L[Real] E) where
  Index := Empty
  component := Empty.elim
  component_compact := fun index => index.elim
  summable_norm := by simp
  operator_eq_tsum := by simp

/-- Sum two explicit compact expansions using a disjoint index sum. -/
def SummableCompactOperatorExpansion.add
    {first second : E →L[Real] E}
    (firstExpansion : SummableCompactOperatorExpansion first)
    (secondExpansion : SummableCompactOperatorExpansion second) :
    SummableCompactOperatorExpansion (first + second) where
  Index := firstExpansion.Index ⊕ secondExpansion.Index
  component
    | Sum.inl index => firstExpansion.component index
    | Sum.inr index => secondExpansion.component index
  component_compact
    | Sum.inl index => firstExpansion.component_compact index
    | Sum.inr index => secondExpansion.component_compact index
  summable_norm := by
    refine (Summable.sum
      (α := firstExpansion.Index) (β := secondExpansion.Index) (M := Real)
      (fun index : firstExpansion.Index ⊕ secondExpansion.Index =>
        match index with
        | Sum.inl index => ‖firstExpansion.component index‖
        | Sum.inr index => ‖secondExpansion.component index‖)
      firstExpansion.summable_norm
      secondExpansion.summable_norm).congr ?_
    intro index
    cases index <;> rfl
  operator_eq_tsum := by
    have hFirst : Summable firstExpansion.component :=
      firstExpansion.summable_norm.of_norm
    have hSecond : Summable secondExpansion.component :=
      secondExpansion.summable_norm.of_norm
    change first + second = ∑' index :
      firstExpansion.Index ⊕ secondExpansion.Index, match index with
        | Sum.inl index => firstExpansion.component index
        | Sum.inr index => secondExpansion.component index
    convert (by
      calc
        first + second =
            (∑' index, firstExpansion.component index) +
              ∑' index, secondExpansion.component index :=
          congrArg₂ (· + ·) firstExpansion.operator_eq_tsum
            secondExpansion.operator_eq_tsum
        _ = ∑' index, match index with
            | Sum.inl index => firstExpansion.component index
            | Sum.inr index => secondExpansion.component index := by
          have hTsum := Summable.tsum_sum
            (α := firstExpansion.Index) (β := secondExpansion.Index)
            (M := E →L[Real] E)
            (f := fun index : firstExpansion.Index ⊕ secondExpansion.Index =>
              match index with
              | Sum.inl index => firstExpansion.component index
              | Sum.inr index => secondExpansion.component index)
            hFirst hSecond
          convert hTsum.symm using 1 <;> rfl) using 1
    apply tsum_congr
    intro index
    cases index <;> rfl

/-- Negate a summable compact expansion. -/
def SummableCompactOperatorExpansion.neg
    {operator : E →L[Real] E}
    (expansion : SummableCompactOperatorExpansion operator) :
    SummableCompactOperatorExpansion (-operator) where
  Index := expansion.Index
  component := fun index => -expansion.component index
  component_compact := fun index =>
    (expansion.component_compact index).neg
  summable_norm := by
    simpa using expansion.summable_norm
  operator_eq_tsum := by
    calc
      -operator = -(∑' index, expansion.component index) :=
        congrArg Neg.neg expansion.operator_eq_tsum
      _ = ∑' index, -expansion.component index := tsum_neg.symm

/-- Difference of two summable compact expansions. -/
def SummableCompactOperatorExpansion.sub
    {first second : E →L[Real] E}
    (firstExpansion : SummableCompactOperatorExpansion first)
    (secondExpansion : SummableCompactOperatorExpansion second) :
    SummableCompactOperatorExpansion (first - second) := by
  simpa [sub_eq_add_neg] using
    firstExpansion.add secondExpansion.neg

/-- Public compact-expansion checkpoint. -/
theorem summable_compact_operator_expansion_gate
    (operator : E →L[Real] E)
    (expansion : SummableCompactOperatorExpansion operator) :
    IsCompactOperator operator :=
  expansion.operator_compact

end
end P0EFTJanusProgramPSummableCompactOperatorExpansion4D
end JanusFormal
