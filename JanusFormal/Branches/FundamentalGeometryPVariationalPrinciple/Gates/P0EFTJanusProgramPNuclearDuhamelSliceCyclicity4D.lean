import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D

/-!
# Cyclic reduction of one Duhamel slice

A Duhamel integrand at fixed parameter, heat time and simplex variable is
usually presented as one bounded heat factor composed with one nuclear
insertion.  Rotating the bounded factor through the nuclear trace produces a
second composition which can then be collapsed by the semigroup law.

This file isolates that argument.  It starts from one nuclear expansion of the
common nuclear factor and derives

```text
Tr(slice operator) = Tr(collapsed operator)
```

by the following chain:

1. identify the slice operator with `B T`;
2. use intrinsic nuclear cyclicity to replace `Tr(B T)` by `Tr(T B)`;
3. identify `T B` with the collapsed operator;
4. remove all presentation choices using intrinsic trace uniqueness.

Neither equality of the scalar traces nor separate aligned rank-one expansions
of the two compositions are supplied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelSliceCyclicity4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D
open P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- One nuclear Duhamel slice and its cyclically collapsed operator. -/
structure NuclearDuhamelSliceCyclicityData
    (sliceOperator collapsedOperator : E →L[Real] E)
    (sliceTrace : IntrinsicNuclearTraceData.{u, v} sliceOperator)
    (collapsedTrace : IntrinsicNuclearTraceData.{u, v} collapsedOperator) where
  nuclearFactor : E →L[Real] E
  boundedFactor : E →L[Real] E
  nuclearExpansion : SummableRankOneOperatorExpansion.{v, u} nuclearFactor
  leftCompositionTrace :
    IntrinsicNuclearTraceData.{u, v} (boundedFactor.comp nuclearFactor)
  rightCompositionTrace :
    IntrinsicNuclearTraceData.{u, v} (nuclearFactor.comp boundedFactor)
  slice_eq_leftComposition :
    sliceOperator = boundedFactor.comp nuclearFactor
  rightComposition_eq_collapsed :
    nuclearFactor.comp boundedFactor = collapsedOperator

namespace NuclearDuhamelSliceCyclicityData

/-- Trace of the slice operator equals the trace of the cyclically collapsed
operator. -/
theorem sliceTrace_eq_collapsedTrace
    {sliceOperator collapsedOperator : E →L[Real] E}
    {sliceTrace : IntrinsicNuclearTraceData.{u, v} sliceOperator}
    {collapsedTrace : IntrinsicNuclearTraceData.{u, v} collapsedOperator}
    (data : NuclearDuhamelSliceCyclicityData sliceOperator collapsedOperator
      sliceTrace collapsedTrace) :
    intrinsicNuclearTrace sliceTrace =
      intrinsicNuclearTrace collapsedTrace := by
  let leftOnSlice : IntrinsicNuclearTraceData.{u, v} sliceOperator :=
    P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator
      data.leftCompositionTrace
      data.slice_eq_leftComposition.symm
  let rightOnCollapsed : IntrinsicNuclearTraceData.{u, v} collapsedOperator :=
    P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator
      data.rightCompositionTrace
      data.rightComposition_eq_collapsed
  calc
    intrinsicNuclearTrace sliceTrace =
        intrinsicNuclearTrace leftOnSlice :=
      intrinsicNuclearTrace_unique sliceTrace leftOnSlice
    _ = intrinsicNuclearTrace data.leftCompositionTrace :=
      P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator_intrinsicNuclearTrace
        data.leftCompositionTrace
        data.slice_eq_leftComposition.symm
    _ = intrinsicNuclearTrace data.rightCompositionTrace :=
      P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D.SummableRankOneOperatorExpansion.intrinsicNuclearTrace_comp_comm_of_expansion
        data.nuclearExpansion data.boundedFactor data.leftCompositionTrace
        data.rightCompositionTrace
    _ = intrinsicNuclearTrace rightOnCollapsed := by
      symm
      exact
        P0EFTJanusProgramPIntrinsicNuclearTraceTransport4D.IntrinsicNuclearTraceData.transportOperator_intrinsicNuclearTrace
          data.rightCompositionTrace
        data.rightComposition_eq_collapsed
    _ = intrinsicNuclearTrace collapsedTrace :=
      intrinsicNuclearTrace_unique rightOnCollapsed collapsedTrace

/-- The collapsed intrinsic trace is independent of the particular trace
certificates selected for either operator. -/
theorem sliceTrace_eq_anyCollapsedTrace
    {sliceOperator collapsedOperator : E →L[Real] E}
    {sliceTrace : IntrinsicNuclearTraceData.{u, v} sliceOperator}
    {collapsedTrace : IntrinsicNuclearTraceData.{u, v} collapsedOperator}
    (data : NuclearDuhamelSliceCyclicityData sliceOperator collapsedOperator
      sliceTrace collapsedTrace)
    (otherCollapsedTrace : IntrinsicNuclearTraceData.{u, v} collapsedOperator) :
    intrinsicNuclearTrace sliceTrace =
      intrinsicNuclearTrace otherCollapsedTrace := by
  calc
    intrinsicNuclearTrace sliceTrace =
        intrinsicNuclearTrace collapsedTrace :=
      data.sliceTrace_eq_collapsedTrace
    _ = intrinsicNuclearTrace otherCollapsedTrace :=
      intrinsicNuclearTrace_unique collapsedTrace otherCollapsedTrace

/-- Public fixed-slice cyclicity checkpoint. -/
theorem nuclear_duhamel_slice_cyclicity_gate
    (sliceOperator collapsedOperator : E →L[Real] E)
    (sliceTrace : IntrinsicNuclearTraceData.{u, v} sliceOperator)
    (collapsedTrace : IntrinsicNuclearTraceData.{u, v} collapsedOperator)
    (data : NuclearDuhamelSliceCyclicityData sliceOperator collapsedOperator
      sliceTrace collapsedTrace) :
    intrinsicNuclearTrace sliceTrace =
      intrinsicNuclearTrace collapsedTrace :=
  data.sliceTrace_eq_collapsedTrace

end NuclearDuhamelSliceCyclicityData

end
end P0EFTJanusProgramPNuclearDuhamelSliceCyclicity4D
end JanusFormal
