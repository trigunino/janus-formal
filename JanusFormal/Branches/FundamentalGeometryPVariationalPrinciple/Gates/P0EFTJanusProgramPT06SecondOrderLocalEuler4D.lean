import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialFinsuppSecondJetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D

/-!
# Second-order local Euler operator

This gate defines the spatial Euler expression of a scalar local function on
genuine order-two throat jets.  Its three terms are the vertical derivative
in the value slot, the negative first total derivatives of the order-one
partials, and the symmetrized second total derivatives of the order-two
partials.

The off-diagonal weight `1 / 2` compensates for summation over both ordered
pairs of throat directions.  Mathlib's `fderiv` is totalized by zero away from
differentiability points, so the intended variational interpretation requires
the corresponding regularity.  No horizontal exactness or terminal T06
classification is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06SecondOrderLocalEuler4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppSecondJetBridge4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- The value multi-index in the genuine order-two truncated index space. -/
def programPT06SecondOrderZeroMultiIndex :
    ThroatSpatialTruncatedIndex 2 :=
  ⟨0, by simp⟩

/-- The first-order multi-index in one throat direction. -/
def programPT06SecondOrderFirstMultiIndex
    (direction : Fin 3) : ThroatSpatialTruncatedIndex 2 :=
  ⟨throatSpatialCoordinateMultiIndex direction, by simp⟩

/-- The second-order multi-index obtained from two throat directions. -/
def programPT06SecondOrderSecondMultiIndex
    (first second : Fin 3) : ThroatSpatialTruncatedIndex 2 :=
  ⟨throatSpatialCoordinateMultiIndex first +
      throatSpatialCoordinateMultiIndex second, by
    rw [throatSpatialMultiIndexOrder_add,
      throatSpatialMultiIndexOrder_coordinateMultiIndex,
      throatSpatialMultiIndexOrder_coordinateMultiIndex]⟩

theorem programPT06SecondOrderSecondMultiIndex_comm
    (first second : Fin 3) :
    programPT06SecondOrderSecondMultiIndex first second =
      programPT06SecondOrderSecondMultiIndex second first := by
  apply Subtype.ext
  exact add_comm _ _

/-- Vertical partial of a second-order local function in its value slot. -/
def programPT06SecondOrderLocalVerticalPartialZero
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real) :
    ThroatSpatialMultiindexJet2 Fiber → (Fiber →L[Real] Real) :=
  fun jet =>
    programPT06ThroatSpatialVerticalPartialDerivative
      localLagrangian jet programPT06SecondOrderZeroMultiIndex

/-- Vertical partial in the first-order slot indexed by one direction. -/
def programPT06SecondOrderLocalVerticalPartialOne
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real)
    (direction : Fin 3) :
    ThroatSpatialMultiindexJet2 Fiber → (Fiber →L[Real] Real) :=
  fun jet =>
    programPT06ThroatSpatialVerticalPartialDerivative
      localLagrangian jet
      (programPT06SecondOrderFirstMultiIndex direction)

/-- Vertical partial in the symmetric second-order slot indexed by two
directions. -/
def programPT06SecondOrderLocalVerticalPartialTwo
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real)
    (first second : Fin 3) :
    ThroatSpatialMultiindexJet2 Fiber → (Fiber →L[Real] Real) :=
  fun jet =>
    programPT06ThroatSpatialVerticalPartialDerivative
      localLagrangian jet
      (programPT06SecondOrderSecondMultiIndex first second)

@[simp] theorem programPT06SecondOrderLocalVerticalPartialZero_apply
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real)
    (jet : ThroatSpatialMultiindexJet2 Fiber) (variation : Fiber) :
    programPT06SecondOrderLocalVerticalPartialZero
        localLagrangian jet variation =
      fderiv Real localLagrangian jet
        (programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex variation) :=
  rfl

@[simp] theorem programPT06SecondOrderLocalVerticalPartialOne_apply
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real)
    (direction : Fin 3) (jet : ThroatSpatialMultiindexJet2 Fiber)
    (variation : Fiber) :
    programPT06SecondOrderLocalVerticalPartialOne
        localLagrangian direction jet variation =
      fderiv Real localLagrangian jet
        (programPT06ThroatSpatialJetCoordinateInjection
          (programPT06SecondOrderFirstMultiIndex direction) variation) :=
  rfl

@[simp] theorem programPT06SecondOrderLocalVerticalPartialTwo_apply
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real)
    (first second : Fin 3) (jet : ThroatSpatialMultiindexJet2 Fiber)
    (variation : Fiber) :
    programPT06SecondOrderLocalVerticalPartialTwo
        localLagrangian first second jet variation =
      fderiv Real localLagrangian jet
        (programPT06ThroatSpatialJetCoordinateInjection
          (programPT06SecondOrderSecondMultiIndex first second) variation) :=
  rfl

@[simp] theorem programPT06SecondOrderLocalVerticalPartialOne_constant
    (constant : Real) (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne
        (fun _ : ThroatSpatialMultiindexJet2 Fiber => constant) direction = 0 := by
  ext jet variation
  simp [programPT06SecondOrderLocalVerticalPartialOne,
    programPT06ThroatSpatialVerticalPartialDerivative]

@[simp] theorem programPT06SecondOrderLocalVerticalPartialTwo_constant
    (constant : Real) (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (fun _ : ThroatSpatialMultiindexJet2 Fiber => constant) first second = 0 := by
  ext jet variation
  simp [programPT06SecondOrderLocalVerticalPartialTwo,
    programPT06ThroatSpatialVerticalPartialDerivative]

@[simp] theorem programPT06SecondOrderLocalVerticalPartialOne_linear
    (linear : ThroatSpatialMultiindexJet2 Fiber →L[Real] Real)
    (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne linear direction =
      fun _ => linear.comp
        (programPT06ThroatSpatialJetCoordinateInjection
          (programPT06SecondOrderFirstMultiIndex direction)) := by
  funext jet
  exact programPT06ThroatSpatialVerticalPartialDerivative_linear
    linear jet (programPT06SecondOrderFirstMultiIndex direction)

@[simp] theorem programPT06SecondOrderLocalVerticalPartialTwo_linear
    (linear : ThroatSpatialMultiindexJet2 Fiber →L[Real] Real)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo linear first second =
      fun _ => linear.comp
        (programPT06ThroatSpatialJetCoordinateInjection
          (programPT06SecondOrderSecondMultiIndex first second)) := by
  funext jet
  exact programPT06ThroatSpatialVerticalPartialDerivative_linear
    linear jet (programPT06SecondOrderSecondMultiIndex first second)

/-- First total-derivative term occurring in the Euler expression. -/
def programPT06SecondOrderLocalEulerFirstTotalTerm
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real)
    (direction : Fin 3) :
    ThroatSpatialMultiindexJet3 Fiber → (Fiber →L[Real] Real) :=
  programPT06ThroatSpatialLocalFunctionTotalDerivative direction
    (programPT06SecondOrderLocalVerticalPartialOne
      localLagrangian direction)

/-- Iterated total-derivative term occurring in the Euler expression. -/
def programPT06SecondOrderLocalEulerSecondTotalTerm
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real)
    (first second : Fin 3) :
    ThroatSpatialMultiindexJet4 Fiber → (Fiber →L[Real] Real) :=
  programPT06ThroatSpatialLocalFunctionTotalDerivative first
    (programPT06ThroatSpatialLocalFunctionTotalDerivative second
      (programPT06SecondOrderLocalVerticalPartialTwo
        localLagrangian first second))

@[simp] theorem programPT06SecondOrderLocalEulerFirstTotalTerm_constant
    (constant : Real) (direction : Fin 3) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (fun _ : ThroatSpatialMultiindexJet2 Fiber => constant) direction = 0 := by
  simp [programPT06SecondOrderLocalEulerFirstTotalTerm]

@[simp] theorem programPT06SecondOrderLocalEulerSecondTotalTerm_constant
    (constant : Real) (first second : Fin 3) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (fun _ : ThroatSpatialMultiindexJet2 Fiber => constant) first second = 0 := by
  simp [programPT06SecondOrderLocalEulerSecondTotalTerm]

@[simp] theorem programPT06SecondOrderLocalEulerFirstTotalTerm_linear
    (linear : ThroatSpatialMultiindexJet2 Fiber →L[Real] Real)
    (direction : Fin 3) :
    programPT06SecondOrderLocalEulerFirstTotalTerm linear direction = 0 := by
  simp [programPT06SecondOrderLocalEulerFirstTotalTerm]

@[simp] theorem programPT06SecondOrderLocalEulerSecondTotalTerm_linear
    (linear : ThroatSpatialMultiindexJet2 Fiber →L[Real] Real)
    (first second : Fin 3) :
    programPT06SecondOrderLocalEulerSecondTotalTerm linear first second = 0 := by
  simp [programPT06SecondOrderLocalEulerSecondTotalTerm]

/-- Weight for summing a symmetric second-order multi-index over ordered
pairs. -/
def programPT06SecondOrderEulerSymmetryWeight
    (first second : Fin 3) : Real :=
  if first = second then 1 else 1 / 2

@[simp] theorem programPT06SecondOrderEulerSymmetryWeight_self
    (direction : Fin 3) :
    programPT06SecondOrderEulerSymmetryWeight direction direction = 1 := by
  simp [programPT06SecondOrderEulerSymmetryWeight]

theorem programPT06SecondOrderEulerSymmetryWeight_of_ne
    {first second : Fin 3} (hDirections : first ≠ second) :
    programPT06SecondOrderEulerSymmetryWeight first second = 1 / 2 := by
  simp [programPT06SecondOrderEulerSymmetryWeight, hDirections]

/-- Genuine second-order spatial Euler operator. -/
def programPT06SecondOrderLocalEuler
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real) :
    ThroatSpatialMultiindexJet4 Fiber → (Fiber →L[Real] Real) :=
  fun jet =>
    programPT06SecondOrderLocalVerticalPartialZero localLagrangian
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) -
    (∑ direction : Fin 3,
      programPT06SecondOrderLocalEulerFirstTotalTerm
        localLagrangian direction
        (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)) +
    ∑ first : Fin 3, ∑ second : Fin 3,
      programPT06SecondOrderEulerSymmetryWeight first second •
        programPT06SecondOrderLocalEulerSecondTotalTerm
          localLagrangian first second jet

theorem programPT06SecondOrderLocalEuler_formula
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real)
    (jet : ThroatSpatialMultiindexJet4 Fiber) :
    programPT06SecondOrderLocalEuler localLagrangian jet =
      programPT06SecondOrderLocalVerticalPartialZero localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) -
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalEulerFirstTotalTerm
          localLagrangian direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)) +
      ∑ first : Fin 3, ∑ second : Fin 3,
        programPT06SecondOrderEulerSymmetryWeight first second •
          programPT06SecondOrderLocalEulerSecondTotalTerm
            localLagrangian first second jet :=
  rfl

@[simp] theorem programPT06SecondOrderLocalEuler_apply
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real)
    (jet : ThroatSpatialMultiindexJet4 Fiber) (variation : Fiber) :
    programPT06SecondOrderLocalEuler localLagrangian jet variation =
      programPT06SecondOrderLocalVerticalPartialZero localLagrangian
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet)
          variation -
        (∑ direction : Fin 3,
          programPT06SecondOrderLocalEulerFirstTotalTerm
            localLagrangian direction
            (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)
            variation) +
        ∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second •
            programPT06SecondOrderLocalEulerSecondTotalTerm
              localLagrangian first second jet variation := by
  simp [programPT06SecondOrderLocalEuler]

/-- A constant local Lagrangian has zero Euler expression. -/
@[simp] theorem programPT06SecondOrderLocalEuler_constant
    (constant : Real) (jet : ThroatSpatialMultiindexJet4 Fiber) :
    programPT06SecondOrderLocalEuler
        (fun _ : ThroatSpatialMultiindexJet2 Fiber => constant) jet = 0 := by
  simp [programPT06SecondOrderLocalEuler,
    programPT06SecondOrderLocalVerticalPartialZero,
    programPT06SecondOrderLocalVerticalPartialOne,
    programPT06SecondOrderLocalVerticalPartialTwo,
    programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06ThroatSpatialVerticalPartialDerivative,
    programPT06ThroatSpatialLocalFunctionTotalDerivative]

/-- For a continuous linear local Lagrangian, only its value-slot coefficient
survives in the Euler expression. -/
@[simp] theorem programPT06SecondOrderLocalEuler_linear
    (linear : ThroatSpatialMultiindexJet2 Fiber →L[Real] Real)
    (jet : ThroatSpatialMultiindexJet4 Fiber) :
    programPT06SecondOrderLocalEuler linear jet =
      linear.comp
        (programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex) := by
  simp [programPT06SecondOrderLocalEuler,
    programPT06SecondOrderLocalVerticalPartialZero,
    programPT06SecondOrderLocalVerticalPartialOne,
    programPT06SecondOrderLocalVerticalPartialTwo,
    programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06ThroatSpatialVerticalPartialDerivative,
    programPT06ThroatSpatialLocalFunctionTotalDerivative]

end
end P0EFTJanusProgramPT06SecondOrderLocalEuler4D
end JanusFormal
