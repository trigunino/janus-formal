import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderLocalEuler4D

/-!
# Soundness of affine horizontal divergences

This gate defines an order-one horizontal current with affine components and
its total divergence, an order-two local scalar function.  For this certified
regular class the divergence is a continuous linear function of the order-two
jet, supported away from the value coordinate.  Its local Euler expression
therefore vanishes.

The result proves only `range dH <= kernel Euler` for affine order-one
currents.  It proves neither the converse, the corresponding statement for
arbitrary smooth currents, nor terminal T06 exactness.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- An order-one horizontal current whose three components are affine local
functions. -/
structure ProgramPT06AffineHorizontalCurrent4D (Fiber : Type u)
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] where
  constant : Fin 3 → Real
  linear : Fin 3 → (ThroatSpatialMultiindexJet1 Fiber →L[Real] Real)

/-- Evaluation of one affine current component. -/
def programPT06AffineHorizontalCurrentComponent
    (current : ProgramPT06AffineHorizontalCurrent4D Fiber)
    (direction : Fin 3) : ThroatSpatialMultiindexJet1 Fiber → Real :=
  fun jet => current.constant direction + current.linear direction jet

private def firstTotalShiftedIndex
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 1) :
    ThroatSpatialTruncatedIndex 2 :=
  ⟨index.1 + throatSpatialCoordinateMultiIndex direction, by
    rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
    omega⟩

/-- Continuous linear form of the order-two to order-one total-derivative
shift. -/
def programPT06FirstTotalDerivativeContinuousLinearMap
    (direction : Fin 3) :
    ThroatSpatialMultiindexJet2 Fiber →L[Real]
      ThroatSpatialMultiindexJet1 Fiber :=
  ContinuousLinearMap.pi fun index =>
    (ContinuousLinearMap.proj (firstTotalShiftedIndex direction index) :
      ThroatSpatialMultiindexJet2 Fiber →L[Real] Fiber)

@[simp] theorem programPT06FirstTotalDerivativeContinuousLinearMap_apply
    (direction : Fin 3) (jet : ThroatSpatialMultiindexJet2 Fiber) :
    programPT06FirstTotalDerivativeContinuousLinearMap (Fiber := Fiber)
        direction jet =
      throatSpatialTotalDerivative direction jet := by
  rfl

/-- Total derivative of one affine current component. -/
def programPT06AffineHorizontalCurrentComponentTotalDerivative
    (current : ProgramPT06AffineHorizontalCurrent4D Fiber)
    (direction : Fin 3) : ThroatSpatialMultiindexJet2 Fiber → Real :=
  fun jet =>
    current.linear direction
      (programPT06FirstTotalDerivativeContinuousLinearMap (Fiber := Fiber)
        direction jet)

@[simp] theorem
    programPT06AffineHorizontalCurrentComponentTotalDerivative_apply
    (current : ProgramPT06AffineHorizontalCurrent4D Fiber)
    (direction : Fin 3) (jet : ThroatSpatialMultiindexJet2 Fiber) :
    programPT06AffineHorizontalCurrentComponentTotalDerivative
        current direction jet =
      current.linear direction
        (throatSpatialTotalDerivative direction jet) := by
  simp [programPT06AffineHorizontalCurrentComponentTotalDerivative]

/-- Total horizontal divergence `dH` of an affine order-one current. -/
def programPT06AffineHorizontalCurrentDivergence
    (current : ProgramPT06AffineHorizontalCurrent4D Fiber) :
    ThroatSpatialMultiindexJet2 Fiber → Real :=
  fun jet =>
    ∑ direction : Fin 3,
      programPT06AffineHorizontalCurrentComponentTotalDerivative
        current direction jet

@[simp] theorem programPT06AffineHorizontalCurrentDivergence_apply
    (current : ProgramPT06AffineHorizontalCurrent4D Fiber)
    (jet : ThroatSpatialMultiindexJet2 Fiber) :
    programPT06AffineHorizontalCurrentDivergence current jet =
      ∑ direction : Fin 3,
        current.linear direction
          (throatSpatialTotalDerivative direction jet) := by
  simp [programPT06AffineHorizontalCurrentDivergence]

/-- The continuous linear map underlying the divergence. -/
def programPT06AffineHorizontalCurrentDivergenceLinearMap
    (current : ProgramPT06AffineHorizontalCurrent4D Fiber) :
    ThroatSpatialMultiindexJet2 Fiber →L[Real] Real :=
  ∑ direction : Fin 3,
    (current.linear direction).comp
      (programPT06FirstTotalDerivativeContinuousLinearMap (Fiber := Fiber)
        direction)

theorem programPT06AffineHorizontalCurrentDivergence_eq_linearMap
    (current : ProgramPT06AffineHorizontalCurrent4D Fiber) :
    programPT06AffineHorizontalCurrentDivergence current =
      programPT06AffineHorizontalCurrentDivergenceLinearMap current := by
  funext jet
  simp [programPT06AffineHorizontalCurrentDivergence,
    programPT06AffineHorizontalCurrentDivergenceLinearMap]

private theorem firstTotalShiftedIndex_ne_zero
    (direction : Fin 3) (index : ThroatSpatialTruncatedIndex 1) :
    firstTotalShiftedIndex direction index ≠
      programPT06SecondOrderZeroMultiIndex := by
  intro hIndex
  have hOrder := congrArg
    (fun bounded : ThroatSpatialTruncatedIndex 2 =>
      throatSpatialMultiIndexOrder bounded.1) hIndex
  change
    throatSpatialMultiIndexOrder
        (index.1 + throatSpatialCoordinateMultiIndex direction) =
      throatSpatialMultiIndexOrder 0 at hOrder
  rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex,
    throatSpatialMultiIndexOrder_zero] at hOrder
  omega

/-- A formal total derivative kills a variation supported only in the value
coordinate, since every shifted coordinate has positive order. -/
@[simp] theorem throatSpatialTotalDerivative_valueCoordinateInjection
    (direction : Fin 3) (variation : Fiber) :
    throatSpatialTotalDerivative direction
        (programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex variation) =
      (0 : ThroatSpatialMultiindexJet1 Fiber) := by
  funext index
  change
    programPT06ThroatSpatialJetCoordinateInjection
        programPT06SecondOrderZeroMultiIndex variation
        (firstTotalShiftedIndex direction index) = 0
  exact programPT06ThroatSpatialJetCoordinateInjection_of_ne
    programPT06SecondOrderZeroMultiIndex
    (firstTotalShiftedIndex direction index)
    (firstTotalShiftedIndex_ne_zero direction index) variation

/-- The divergence linear map has zero coefficient in the value slot. -/
theorem
    programPT06AffineHorizontalCurrentDivergenceLinearMap_comp_value_eq_zero
    (current : ProgramPT06AffineHorizontalCurrent4D Fiber) :
    (programPT06AffineHorizontalCurrentDivergenceLinearMap current).comp
        (programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex) = 0 := by
  apply ContinuousLinearMap.ext
  intro variation
  simp [programPT06AffineHorizontalCurrentDivergenceLinearMap]

/-- Sound direction for the explicit affine current class: every total
horizontal divergence has zero second-order local Euler expression. -/
theorem programPT06SecondOrderLocalEuler_horizontalDivergence_eq_zero
    (current : ProgramPT06AffineHorizontalCurrent4D Fiber)
    (jet : ThroatSpatialMultiindexJet4 Fiber) :
    programPT06SecondOrderLocalEuler
        (programPT06AffineHorizontalCurrentDivergence current) jet = 0 := by
  rw [programPT06AffineHorizontalCurrentDivergence_eq_linearMap,
    programPT06SecondOrderLocalEuler_linear]
  exact
    programPT06AffineHorizontalCurrentDivergenceLinearMap_comp_value_eq_zero
      current

end
end P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D
end JanusFormal
