import Mathlib.Analysis.InnerProductSpace.Trace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTrace4D

/-!
# Reusable uniqueness of nuclear rank-one traces

The intrinsic trace packet needs one theorem saying that two norm-summable
rank-one presentations of the same operator have the same scalar trace.  This
file records that theorem once for an ambient Hilbert space, rather than once
for every integrated operator.

In finite dimension the theorem is constructed from `LinearMap.trace`.  In
infinite dimension it remains the genuine nuclear-trace uniqueness theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicNuclearTraceExpansionUniqueness4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- One ambient-space theorem asserting uniqueness of the scalar trace of all
norm-summable rank-one presentations. -/
structure NuclearRankOneTraceUniquenessData where
  expansionTrace_eq :
    ∀ {operator : E →L[Real] E}
      (first second : SummableRankOneOperatorExpansion.{v} operator),
      first.expansionTrace = second.expansionTrace

namespace NuclearRankOneTraceUniquenessData

/-- One existing intrinsic trace certificate compares any two presentations
of its operator. -/
theorem expansionTrace_eq_of_intrinsicTraceData
    {operator : E →L[Real] E}
    (traceClass : IntrinsicNuclearTraceData.{u, v} operator)
    (first second : SummableRankOneOperatorExpansion.{v} operator) :
    first.expansionTrace = second.expansionTrace := by
  calc
    first.expansionTrace = intrinsicNuclearTrace traceClass :=
      traceClass.expansionTrace_eq first
    _ = second.expansionTrace := (traceClass.expansionTrace_eq second).symm

/-- A reusable ambient uniqueness theorem turns any certified expansion into
an intrinsic nuclear trace certificate. -/
def intrinsicTraceData
    (uniqueness : NuclearRankOneTraceUniquenessData.{u, v} (E := E))
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{v} operator) :
    IntrinsicNuclearTraceData.{u, v} operator where
  expansion := expansion
  presentation_independent := fun other ↦
    uniqueness.expansionTrace_eq other expansion

/-- Any constructor of intrinsic trace data from one presentation supplies
the reusable ambient uniqueness theorem. -/
def ofIntrinsicTraceConstructor
    (construct : ∀ {operator : E →L[Real] E},
      SummableRankOneOperatorExpansion.{v} operator →
        IntrinsicNuclearTraceData.{u, v} operator) :
    NuclearRankOneTraceUniquenessData.{u, v} (E := E) where
  expansionTrace_eq := by
    intro operator first second
    exact expansionTrace_eq_of_intrinsicTraceData (construct first) first second

end NuclearRankOneTraceUniquenessData

section FiniteDimensional

variable [FiniteDimensional Real E]

/-- Finite-dimensional operator trace as a continuous linear functional on
continuous endomorphisms. -/
private def finiteDimensionalOperatorTraceLinear :
    (E →L[Real] E) →ₗ[Real] Real where
  toFun operator := LinearMap.trace Real E operator.toLinearMap
  map_add' first second := by simp
  map_smul' scalar operator := by simp

private def finiteDimensionalOperatorTrace :
    (E →L[Real] E) →L[Real] Real :=
  { finiteDimensionalOperatorTraceLinear (E := E) with
    cont := (finiteDimensionalOperatorTraceLinear
      (E := E)).continuous_of_finiteDimensional }

/-- Every summable rank-one presentation computes the ordinary
finite-dimensional operator trace. -/
theorem expansionTrace_eq_finiteDimensionalTrace
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{v} operator) :
    expansion.expansionTrace =
      LinearMap.trace Real E operator.toLinearMap := by
  have hTraceSum := (finiteDimensionalOperatorTrace (E := E)).hasSum
    (Summable.of_norm expansion.component_norm_summable).hasSum
  have hTraceSeries : HasSum
      (fun index ↦ expansion.coefficient index *
        inner Real (expansion.leftVector index) (expansion.rightVector index))
      (finiteDimensionalOperatorTrace (E := E)
        (∑' index, expansion.component index)) := by
    apply hTraceSum.congr
    intro index
    simp [finiteDimensionalOperatorTrace,
      finiteDimensionalOperatorTraceLinear,
      SummableRankOneOperatorExpansion.component,
      InnerProductSpace.trace_rankOne, real_inner_comm]
  calc
    expansion.expansionTrace =
        finiteDimensionalOperatorTrace (E := E)
          (∑' index, expansion.component index) :=
      expansion.hasSum_expansionTrace.unique hTraceSeries
    _ = finiteDimensionalOperatorTrace (E := E) operator := by
      congr 1
      calc
        (∑' index, expansion.component index) =
            ∑' index, expansion.coefficient index •
              InnerProductSpace.rankOne Real
                (expansion.leftVector index) (expansion.rightVector index) := by
          apply tsum_congr
          intro index
          rfl
        _ = operator := expansion.operator_eq_tsum.symm
    _ = LinearMap.trace Real E operator.toLinearMap := rfl

/-- In finite dimension, Mathlib's canonical trace closes rank-one
presentation independence with no additional hypothesis. -/
def finiteDimensionalNuclearRankOneTraceUniquenessData :
    NuclearRankOneTraceUniquenessData.{u, v} (E := E) where
  expansionTrace_eq := by
    intro operator first second
    rw [expansionTrace_eq_finiteDimensionalTrace first,
      expansionTrace_eq_finiteDimensionalTrace second]

/-- Canonical finite-dimensional intrinsic trace certificate generated from
one summable rank-one presentation. -/
def finiteDimensionalIntrinsicNuclearTraceData
    {operator : E →L[Real] E}
    (expansion : SummableRankOneOperatorExpansion.{v} operator) :
    IntrinsicNuclearTraceData.{u, v} operator :=
  finiteDimensionalNuclearRankOneTraceUniquenessData.intrinsicTraceData expansion

end FiniteDimensional

end
end P0EFTJanusProgramPIntrinsicNuclearTraceExpansionUniqueness4D
end JanusFormal
