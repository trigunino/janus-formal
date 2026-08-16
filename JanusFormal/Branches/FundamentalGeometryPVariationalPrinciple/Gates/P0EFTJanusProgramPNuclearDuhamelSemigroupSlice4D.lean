import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelSliceCyclicity4D

/-!
# Semigroup collapse of one nuclear Duhamel slice

For a Duhamel insertion, one fixed auxiliary slice has the operator form

```text
K_left (H' K_right).
```

Assume `H' K_right` is nuclear.  Cyclicity moves `K_left` to the right:

```text
Tr(K_left (H' K_right))
  = Tr((H' K_right) K_left).
```

Associativity and the heat semigroup identity

```text
K_right K_left = K_full
```

then reduce the slice trace to

```text
Tr(H' K_full).
```

This file constructs the complete slice-cyclicity packet from exactly these
operator ingredients.  Equality of the rotated and collapsed scalar traces is
not an input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelSemigroupSlice4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearDuhamelSliceCyclicity4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- One heat-semigroup Duhamel slice with a nuclear insertion/right factor. -/
structure NuclearDuhamelSemigroupSliceData where
  leftHeat : E →L[Real] E
  rightHeat : E →L[Real] E
  fullHeat : E →L[Real] E
  insertion : E →L[Real] E
  semigroup_eq : rightHeat.comp leftHeat = fullHeat
  insertionRightExpansion :
    SummableRankOneOperatorExpansion.{v, u} (insertion.comp rightHeat)
  sliceTraceClass :
    IntrinsicNuclearTraceData.{u, v}
      (leftHeat.comp (insertion.comp rightHeat))
  rotatedTraceClass :
    IntrinsicNuclearTraceData.{u, v}
      ((insertion.comp rightHeat).comp leftHeat)
  collapsedTraceClass :
    IntrinsicNuclearTraceData.{u, v} (insertion.comp fullHeat)

namespace NuclearDuhamelSemigroupSliceData

/-- The genuine slice operator. -/
def sliceOperator (data : NuclearDuhamelSemigroupSliceData.{u, v} (E := E)) :
    E →L[Real] E :=
  data.leftHeat.comp (data.insertion.comp data.rightHeat)

/-- The cyclically collapsed insertion/heat operator. -/
def collapsedOperator (data : NuclearDuhamelSemigroupSliceData.{u, v} (E := E)) :
    E →L[Real] E :=
  data.insertion.comp data.fullHeat

/-- Associativity followed by the semigroup law collapses the rotated
composition. -/
theorem rotatedOperator_eq_collapsedOperator
    (data : NuclearDuhamelSemigroupSliceData.{u, v} (E := E)) :
    (data.insertion.comp data.rightHeat).comp data.leftHeat =
      data.collapsedOperator := by
  calc
    (data.insertion.comp data.rightHeat).comp data.leftHeat =
        data.insertion.comp (data.rightHeat.comp data.leftHeat) :=
      ContinuousLinearMap.comp_assoc _ _ _
    _ = data.insertion.comp data.fullHeat := by
      rw [data.semigroup_eq]
    _ = data.collapsedOperator := rfl

/-- Generic cyclicity packet generated from the heat factors and semigroup
law. -/
def toSliceCyclicity
    (data : NuclearDuhamelSemigroupSliceData.{u, v} (E := E)) :
    NuclearDuhamelSliceCyclicityData.{u, v}
      data.sliceOperator data.collapsedOperator
      data.sliceTraceClass data.collapsedTraceClass where
  nuclearFactor := data.insertion.comp data.rightHeat
  boundedFactor := data.leftHeat
  nuclearExpansion := data.insertionRightExpansion
  leftCompositionTrace := data.sliceTraceClass
  rightCompositionTrace := data.rotatedTraceClass
  slice_eq_leftComposition := rfl
  rightComposition_eq_collapsed :=
    data.rotatedOperator_eq_collapsedOperator

/-- The trace of the original Duhamel slice is the trace of `H' K_full`. -/
theorem sliceTrace_eq_collapsedTrace
    (data : NuclearDuhamelSemigroupSliceData.{u, v} (E := E)) :
    intrinsicNuclearTrace data.sliceTraceClass =
      intrinsicNuclearTrace data.collapsedTraceClass :=
  P0EFTJanusProgramPNuclearDuhamelSliceCyclicity4D.NuclearDuhamelSliceCyclicityData.sliceTrace_eq_collapsedTrace
    data.toSliceCyclicity

/-- Public semigroup-slice checkpoint. -/
theorem nuclear_duhamel_semigroup_slice_gate
    (data : NuclearDuhamelSemigroupSliceData.{u, v} (E := E)) :
    data.rightHeat.comp data.leftHeat = data.fullHeat ∧
    (data.insertion.comp data.rightHeat).comp data.leftHeat =
      data.insertion.comp data.fullHeat ∧
    intrinsicNuclearTrace data.sliceTraceClass =
      intrinsicNuclearTrace data.collapsedTraceClass :=
  ⟨data.semigroup_eq,
    data.rotatedOperator_eq_collapsedOperator,
    data.sliceTrace_eq_collapsedTrace⟩

end NuclearDuhamelSemigroupSliceData

end
end P0EFTJanusProgramPNuclearDuhamelSemigroupSlice4D
end JanusFormal
