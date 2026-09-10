import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06TruncatedShiftCoordinateInjection4D

/-!
# Ambient vertical-total derivative commutator

This gate specializes the ambient Cartan identity to one jet coordinate.  A
vertical partial commutes with a total derivative when the selected
multi-index has no component in that direction.  Otherwise the commutator is
the vertical partial at the unique predecessor multi-index.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AmbientVerticalTotalDerivativeCommutator4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06MultiindexLocalEulerComplex4D
open P0EFTJanusProgramPT06AmbientVerticalTotalDerivativeIdentity4D
open P0EFTJanusProgramPT06TruncatedShiftCoordinateInjection4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev SpatialJet (Fiber : Type u) (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet Fiber order

/-- Pointwise commutation when the selected coordinate has no component in
the total-derivative direction. -/
theorem programPT06AmbientVerticalTotalDerivative_commute_of_coordinate_eq_zero_apply
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Real)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order)
    (hCoordinate : index.1 direction = 0) (variation : Fiber) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) jet index variation =
      programPT06AmbientLocalFunctionTotalDerivative order direction
          (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
            localFunction y index) jet variation := by
  rw [programPT06AmbientVerticalTotalDerivativeIdentity_apply
      order direction localFunction hLocalFunction jet index variation,
    programPT06TruncatedJetShift_coordinateInjection_eq_zero
      (Fiber := Fiber) order direction index hCoordinate variation]
  simp

/-- Pointwise commutator formula when the selected coordinate has a nonzero
component in the total-derivative direction. -/
theorem programPT06AmbientVerticalTotalDerivative_commute_of_coordinate_ne_zero_apply
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Real)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order)
    (hCoordinate : index.1 direction ≠ 0) (variation : Fiber) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) jet index variation =
      programPT06AmbientLocalFunctionTotalDerivative order direction
          (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
            localFunction y index) jet variation +
        programPT06ThroatSpatialVerticalPartialDerivative localFunction jet
          (programPT06TruncatedIndexPredecessor
            order direction index hCoordinate) variation := by
  rw [programPT06AmbientVerticalTotalDerivativeIdentity_apply
      order direction localFunction hLocalFunction jet index variation,
    programPT06TruncatedJetShift_coordinateInjection_eq_predecessor
      (Fiber := Fiber) order direction index hCoordinate variation]
  rfl

/-- Covector-valued commutation when the selected coordinate has no
component in the total-derivative direction. -/
theorem programPT06AmbientVerticalTotalDerivative_commute_of_coordinate_eq_zero
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Real)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order)
    (hCoordinate : index.1 direction = 0) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) jet index =
      programPT06AmbientLocalFunctionTotalDerivative order direction
        (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
          localFunction y index) jet := by
  apply ContinuousLinearMap.ext
  intro variation
  exact
    programPT06AmbientVerticalTotalDerivative_commute_of_coordinate_eq_zero_apply
      order direction localFunction hLocalFunction jet index hCoordinate variation

/-- Covector-valued commutator formula at the predecessor multi-index. -/
theorem programPT06AmbientVerticalTotalDerivative_commute_of_coordinate_ne_zero
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Real)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order)
    (hCoordinate : index.1 direction ≠ 0) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) jet index =
      programPT06AmbientLocalFunctionTotalDerivative order direction
          (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
            localFunction y index) jet +
        programPT06ThroatSpatialVerticalPartialDerivative localFunction jet
          (programPT06TruncatedIndexPredecessor
            order direction index hCoordinate) := by
  apply ContinuousLinearMap.ext
  intro variation
  simpa only [add_apply] using
    programPT06AmbientVerticalTotalDerivative_commute_of_coordinate_ne_zero_apply
      order direction localFunction hLocalFunction jet index hCoordinate variation

/-- Uniform covector-valued commutator formula, split by the coefficient of
the selected multi-index in the total-derivative direction. -/
theorem programPT06AmbientVerticalTotalDerivative_commutator
    (order : Nat) (direction : Fin 3)
    (localFunction : SpatialJet Fiber order → Real)
    (hLocalFunction : ContDiff Real 2 localFunction)
    (jet : SpatialJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06AmbientLocalFunctionTotalDerivative
          order direction localFunction) jet index =
      if hCoordinate : index.1 direction = 0 then
        programPT06AmbientLocalFunctionTotalDerivative order direction
          (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
            localFunction y index) jet
      else
        programPT06AmbientLocalFunctionTotalDerivative order direction
            (fun y ↦ programPT06ThroatSpatialVerticalPartialDerivative
              localFunction y index) jet +
          programPT06ThroatSpatialVerticalPartialDerivative localFunction jet
            (programPT06TruncatedIndexPredecessor
              order direction index hCoordinate) := by
  split_ifs with hCoordinate
  · exact
      programPT06AmbientVerticalTotalDerivative_commute_of_coordinate_eq_zero
        order direction localFunction hLocalFunction jet index hCoordinate
  · exact
      programPT06AmbientVerticalTotalDerivative_commute_of_coordinate_ne_zero
        order direction localFunction hLocalFunction jet index hCoordinate

end
end P0EFTJanusProgramPT06AmbientVerticalTotalDerivativeCommutator4D
end JanusFormal
