import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AmbientVerticalTotalDerivativeIdentity4D

/-!
# Truncated shifts of coordinate injections

This gate identifies the action of a fixed-order truncated jet shift on a
single coordinate injection.  A shift annihilates an injection whose selected
multi-index has zero coefficient in the shift direction.  Otherwise it moves
that injection to the unique predecessor multi-index.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06TruncatedShiftCoordinateInjection4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev SpatialJet (Fiber : Type u) (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

/-- Remove one copy of `direction` from a bounded multi-index whose
coefficient in that direction is nonzero. -/
def programPT06TruncatedIndexPredecessor
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order)
    (_hCoordinate : index.1 direction ≠ 0) :
    ThroatSpatialTruncatedIndex order :=
  ⟨index.1 - throatSpatialCoordinateMultiIndex direction, by
    apply (Finsupp.degree_mono ?_).trans index.2
    intro coordinate
    exact Nat.sub_le _ _⟩

@[simp] theorem programPT06TruncatedIndexPredecessor_value
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order)
    (hCoordinate : index.1 direction ≠ 0) :
    (programPT06TruncatedIndexPredecessor
        order direction index hCoordinate).1 =
      index.1 - throatSpatialCoordinateMultiIndex direction := by
  rfl

/-- Adding the removed coordinate reconstructs the original multi-index. -/
theorem programPT06TruncatedIndexPredecessor_add_coordinate
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order)
    (hCoordinate : index.1 direction ≠ 0) :
    (programPT06TruncatedIndexPredecessor
          order direction index hCoordinate).1 +
        throatSpatialCoordinateMultiIndex direction = index.1 := by
  change
    (index.1 - throatSpatialCoordinateMultiIndex direction) +
        throatSpatialCoordinateMultiIndex direction = index.1
  simpa [throatSpatialCoordinateMultiIndex] using
    Finsupp.sub_add_single_one_cancel hCoordinate

/-- Removing a nonzero coordinate lowers total multi-index order by one. -/
theorem programPT06TruncatedIndexPredecessor_order_add_one
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order)
    (hCoordinate : index.1 direction ≠ 0) :
    throatSpatialMultiIndexOrder
          (programPT06TruncatedIndexPredecessor
            order direction index hCoordinate).1 + 1 =
      throatSpatialMultiIndexOrder index.1 := by
  have hOrder := congrArg throatSpatialMultiIndexOrder
    (programPT06TruncatedIndexPredecessor_add_coordinate
      order direction index hCoordinate)
  rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex] at hOrder
  exact hOrder

/-- A shifted bounded index is the original index exactly when its source is
the predecessor. -/
theorem programPT06TruncatedShiftedIndex_eq_iff_predecessor
    (order : Nat) (direction : Fin 3)
    (index coordinate : ThroatSpatialTruncatedIndex order)
    (hCoordinate : index.1 direction ≠ 0)
    (hShift : throatSpatialMultiIndexOrder
        (coordinate.1 + throatSpatialCoordinateMultiIndex direction) ≤ order) :
    (⟨coordinate.1 + throatSpatialCoordinateMultiIndex direction, hShift⟩ :
        ThroatSpatialTruncatedIndex order) = index ↔
      coordinate = programPT06TruncatedIndexPredecessor
        order direction index hCoordinate := by
  constructor
  · intro hEqual
    apply Subtype.ext
    have hUnderlying := congrArg Subtype.val hEqual
    have hReconstruct :=
      programPT06TruncatedIndexPredecessor_add_coordinate
        order direction index hCoordinate
    exact add_right_cancel (hUnderlying.trans hReconstruct.symm)
  · intro hEqual
    subst coordinate
    apply Subtype.ext
    exact programPT06TruncatedIndexPredecessor_add_coordinate
      order direction index hCoordinate

/-- A truncated shift annihilates a coordinate injection when the injected
multi-index has no coefficient in the shift direction. -/
theorem programPT06TruncatedJetShift_coordinateInjection_eq_zero
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order)
    (hCoordinate : index.1 direction = 0) (variation : Fiber) :
    programPT06TruncatedJetShiftContinuousLinearMap
        (Fiber := Fiber) order direction
        (programPT06ThroatSpatialJetCoordinateInjection index variation) =
      (0 : SpatialJet Fiber order) := by
  funext coordinate
  rw [programPT06TruncatedJetShiftContinuousLinearMap_apply]
  split_ifs with hShift
  · exact programPT06ThroatSpatialJetCoordinateInjection_of_ne
      index
      ⟨coordinate.1 + throatSpatialCoordinateMultiIndex direction, hShift⟩
      (by
        intro hEqual
        have hAtDirection := congrArg
          (fun bounded : ThroatSpatialTruncatedIndex order =>
            bounded.1 direction) hEqual
        simp [throatSpatialCoordinateMultiIndex, hCoordinate] at hAtDirection)
      variation
  · rfl

/-- If the selected coefficient is nonzero, a truncated shift moves the
coordinate injection to its predecessor. -/
theorem programPT06TruncatedJetShift_coordinateInjection_eq_predecessor
    (order : Nat) (direction : Fin 3)
    (index : ThroatSpatialTruncatedIndex order)
    (hCoordinate : index.1 direction ≠ 0) (variation : Fiber) :
    programPT06TruncatedJetShiftContinuousLinearMap
        (Fiber := Fiber) order direction
        (programPT06ThroatSpatialJetCoordinateInjection index variation) =
      programPT06ThroatSpatialJetCoordinateInjection
        (programPT06TruncatedIndexPredecessor
          order direction index hCoordinate) variation := by
  funext coordinate
  rw [programPT06TruncatedJetShiftContinuousLinearMap_apply]
  by_cases hShift : throatSpatialMultiIndexOrder
      (coordinate.1 + throatSpatialCoordinateMultiIndex direction) ≤ order
  · rw [dif_pos hShift]
    by_cases hPredecessor : coordinate =
        programPT06TruncatedIndexPredecessor
          order direction index hCoordinate
    · have hShifted :
          (⟨coordinate.1 + throatSpatialCoordinateMultiIndex direction,
              hShift⟩ : ThroatSpatialTruncatedIndex order) = index :=
        (programPT06TruncatedShiftedIndex_eq_iff_predecessor
          order direction index coordinate hCoordinate hShift).2 hPredecessor
      rw [hShifted, hPredecessor]
      simp only [programPT06ThroatSpatialJetCoordinateInjection_same]
    · have hShifted :
          (⟨coordinate.1 + throatSpatialCoordinateMultiIndex direction,
              hShift⟩ : ThroatSpatialTruncatedIndex order) ≠ index := by
        intro hEqual
        exact hPredecessor
          ((programPT06TruncatedShiftedIndex_eq_iff_predecessor
            order direction index coordinate hCoordinate hShift).1 hEqual)
      rw [programPT06ThroatSpatialJetCoordinateInjection_of_ne
          index _ hShifted variation,
        programPT06ThroatSpatialJetCoordinateInjection_of_ne
          _ coordinate hPredecessor variation]
  · rw [dif_neg hShift]
    have hPredecessor : coordinate ≠
        programPT06TruncatedIndexPredecessor
          order direction index hCoordinate := by
      intro hEqual
      apply hShift
      rw [hEqual,
        programPT06TruncatedIndexPredecessor_add_coordinate]
      exact index.2
    exact (programPT06ThroatSpatialJetCoordinateInjection_of_ne
      _ coordinate hPredecessor variation).symm

end
end P0EFTJanusProgramPT06TruncatedShiftCoordinateInjection4D
end JanusFormal
