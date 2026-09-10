import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06TruncatedShiftCoordinateInjection4D

/-!
# Successor reindexing for bounded spatial multi-indices

This gate identifies the indices of order at most `n` with the indices of
order at most `n + 1` having a positive coefficient in a fixed direction.
It also records the analogous retyping equivalence for the lower-order range.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06TruncatedIndexSuccessorEquiv4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06TruncatedShiftCoordinateInjection4D

universe u

/-- Add one copy of `direction` to a bounded spatial multi-index. -/
def programPT06TruncatedIndexSuccessor
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order) :
    { successor : ThroatSpatialTruncatedIndex (order + 1) //
      successor.1 direction ≠ 0 } :=
  ⟨⟨index.1 + throatSpatialCoordinateMultiIndex direction, by
      rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
      omega⟩,
    by simp [throatSpatialCoordinateMultiIndex]⟩

@[simp] theorem programPT06TruncatedIndexSuccessor_value
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order) :
    (programPT06TruncatedIndexSuccessor order direction index).1.1 =
      index.1 + throatSpatialCoordinateMultiIndex direction := by
  rfl

@[simp] theorem programPT06TruncatedIndexSuccessor_coordinate
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order) :
    (programPT06TruncatedIndexSuccessor order direction index).1.1 direction =
      index.1 direction + 1 := by
  simp [programPT06TruncatedIndexSuccessor,
    throatSpatialCoordinateMultiIndex]

/-- Remove the selected positive coefficient and retype the predecessor at
the lower truncation order. -/
def programPT06TruncatedIndexSuccessorPredecessor
    (order : Nat) (direction : Fin 3)
    (index : { bounded : ThroatSpatialTruncatedIndex (order + 1) //
      bounded.1 direction ≠ 0 }) :
    ThroatSpatialTruncatedIndex order :=
  ⟨(programPT06TruncatedIndexPredecessor
      (order + 1) direction index.1 index.2).1, by
    have hLower := programPT06TruncatedIndexPredecessor_order_add_one
      (order + 1) direction index.1 index.2
    have hUpper := index.1.2
    omega⟩

@[simp] theorem programPT06TruncatedIndexSuccessorPredecessor_value
    (order : Nat) (direction : Fin 3)
    (index : { bounded : ThroatSpatialTruncatedIndex (order + 1) //
      bounded.1 direction ≠ 0 }) :
    (programPT06TruncatedIndexSuccessorPredecessor
        order direction index).1 =
      (programPT06TruncatedIndexPredecessor
        (order + 1) direction index.1 index.2).1 := by
  rfl

theorem programPT06TruncatedIndexSuccessorPredecessor_left
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06TruncatedIndexSuccessorPredecessor order direction
        (programPT06TruncatedIndexSuccessor order direction index) =
      index := by
  apply Subtype.ext
  exact add_right_cancel (by
    simpa only [programPT06TruncatedIndexSuccessor_value,
      programPT06TruncatedIndexSuccessorPredecessor_value] using
      programPT06TruncatedIndexPredecessor_add_coordinate
        (order + 1) direction
        (programPT06TruncatedIndexSuccessor order direction index).1
        (programPT06TruncatedIndexSuccessor order direction index).2)

theorem programPT06TruncatedIndexSuccessorPredecessor_right
    (order : Nat) (direction : Fin 3)
    (index : { bounded : ThroatSpatialTruncatedIndex (order + 1) //
      bounded.1 direction ≠ 0 }) :
    programPT06TruncatedIndexSuccessor order direction
        (programPT06TruncatedIndexSuccessorPredecessor order direction index) =
      index := by
  apply Subtype.ext
  apply Subtype.ext
  simpa only [programPT06TruncatedIndexSuccessor_value,
    programPT06TruncatedIndexSuccessorPredecessor_value] using
    programPT06TruncatedIndexPredecessor_add_coordinate
      (order + 1) direction index.1 index.2

/-- Successor equivalence between order-`n` indices and the positive
`direction` part of the order-`n + 1` indices. -/
def programPT06TruncatedIndexSuccessorEquiv
    (order : Nat) (direction : Fin 3) :
    ThroatSpatialTruncatedIndex order ≃
      { index : ThroatSpatialTruncatedIndex (order + 1) //
        index.1 direction ≠ 0 } where
  toFun := programPT06TruncatedIndexSuccessor order direction
  invFun := programPT06TruncatedIndexSuccessorPredecessor order direction
  left_inv := programPT06TruncatedIndexSuccessorPredecessor_left order direction
  right_inv := programPT06TruncatedIndexSuccessorPredecessor_right order direction

@[simp] theorem programPT06TruncatedIndexSuccessorEquiv_apply
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06TruncatedIndexSuccessorEquiv order direction index =
      programPT06TruncatedIndexSuccessor order direction index := by
  rfl

@[simp] theorem programPT06TruncatedIndexSuccessorEquiv_symm_apply
    (order : Nat) (direction : Fin 3)
    (index : { bounded : ThroatSpatialTruncatedIndex (order + 1) //
      bounded.1 direction ≠ 0 }) :
    (programPT06TruncatedIndexSuccessorEquiv order direction).symm index =
      programPT06TruncatedIndexSuccessorPredecessor order direction index := by
  rfl

/-- Reindex a finite sum over the positive-coordinate part by predecessors. -/
theorem programPT06TruncatedIndexSuccessorEquiv_sum_comp
    {M : Type u} [AddCommMonoid M]
    (order : Nat) (direction : Fin 3)
    (summand : { index : ThroatSpatialTruncatedIndex (order + 1) //
      index.1 direction ≠ 0 } → M) :
    (∑ index : ThroatSpatialTruncatedIndex order,
        summand (programPT06TruncatedIndexSuccessorEquiv
          order direction index)) =
      ∑ index, summand index :=
  (programPT06TruncatedIndexSuccessorEquiv order direction).sum_comp summand

/-- Embed an order-`n` index in order `n + 1`, retaining its sharper order
bound as part of the target subtype. -/
def programPT06TruncatedIndexLowerOrderEmbedding
    (order : Nat) (index : ThroatSpatialTruncatedIndex order) :
    { embedded : ThroatSpatialTruncatedIndex (order + 1) //
      throatSpatialMultiIndexOrder embedded.1 ≤ order } :=
  ⟨⟨index.1, index.2.trans (by omega)⟩, index.2⟩

@[simp] theorem programPT06TruncatedIndexLowerOrderEmbedding_value
    (order : Nat) (index : ThroatSpatialTruncatedIndex order) :
    (programPT06TruncatedIndexLowerOrderEmbedding order index).1.1 =
      index.1 := by
  rfl

/-- Retype an order-`n + 1` index carrying an order-`n` bound. -/
def programPT06TruncatedIndexLowerOrderRetype
    (order : Nat)
    (index : { embedded : ThroatSpatialTruncatedIndex (order + 1) //
      throatSpatialMultiIndexOrder embedded.1 ≤ order }) :
    ThroatSpatialTruncatedIndex order :=
  ⟨index.1.1, index.2⟩

@[simp] theorem programPT06TruncatedIndexLowerOrderRetype_value
    (order : Nat)
    (index : { embedded : ThroatSpatialTruncatedIndex (order + 1) //
      throatSpatialMultiIndexOrder embedded.1 ≤ order }) :
    (programPT06TruncatedIndexLowerOrderRetype order index).1 = index.1.1 := by
  rfl

/-- Retyping equivalence for the lower-order part of the next truncation. -/
def programPT06TruncatedIndexLowerOrderEquiv (order : Nat) :
    ThroatSpatialTruncatedIndex order ≃
      { index : ThroatSpatialTruncatedIndex (order + 1) //
        throatSpatialMultiIndexOrder index.1 ≤ order } where
  toFun := programPT06TruncatedIndexLowerOrderEmbedding order
  invFun := programPT06TruncatedIndexLowerOrderRetype order
  left_inv := by
    intro index
    apply Subtype.ext
    rfl
  right_inv := by
    intro index
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp] theorem programPT06TruncatedIndexLowerOrderEquiv_apply
    (order : Nat) (index : ThroatSpatialTruncatedIndex order) :
    programPT06TruncatedIndexLowerOrderEquiv order index =
      programPT06TruncatedIndexLowerOrderEmbedding order index := by
  rfl

@[simp] theorem programPT06TruncatedIndexLowerOrderEquiv_symm_apply
    (order : Nat)
    (index : { embedded : ThroatSpatialTruncatedIndex (order + 1) //
      throatSpatialMultiIndexOrder embedded.1 ≤ order }) :
    (programPT06TruncatedIndexLowerOrderEquiv order).symm index =
      programPT06TruncatedIndexLowerOrderRetype order index := by
  rfl

/-- Reindex a finite sum over the lower-order part of the next truncation. -/
theorem programPT06TruncatedIndexLowerOrderEquiv_sum_comp
    {M : Type u} [AddCommMonoid M] (order : Nat)
    (summand : { index : ThroatSpatialTruncatedIndex (order + 1) //
      throatSpatialMultiIndexOrder index.1 ≤ order } → M) :
    (∑ index : ThroatSpatialTruncatedIndex order,
        summand (programPT06TruncatedIndexLowerOrderEquiv order index)) =
      ∑ index, summand index :=
  (programPT06TruncatedIndexLowerOrderEquiv order).sum_comp summand

end
end P0EFTJanusProgramPT06TruncatedIndexSuccessorEquiv4D
end JanusFormal
