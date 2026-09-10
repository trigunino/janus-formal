import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AffineSecondOrderExactness4D

/-!
# BRST naturality of the affine second-order T06 complex

This gate prolongs any square-zero continuous linear fiber differential to
the genuine spatial jet tower.  Pullback along that prolongation defines a
square-zero differential on affine second-order densities, commutes with the
affine horizontal differential, and intertwines the affine Euler map.

The result is generic.  A physical specialization still requires a
square-zero differential on the chosen physical fiber.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AffineSecondOrderBRSTNaturality4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06AffineSecondOrderExactness4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
  [FiniteDimensional Real Fiber]

/-- A continuous linear BRST-type differential on one model fiber. -/
structure ProgramPT06SquareZeroContinuousFiberDifferential4D where
  differential : Fiber →L[Real] Fiber
  square_zero : ∀ value, differential (differential value) = 0

/-- Coefficientwise prolongation of a fiber differential to a genuine
spatial jet of arbitrary finite order. -/
def programPT06ContinuousFiberDifferentialJetProlongation
    (brst : ProgramPT06SquareZeroContinuousFiberDifferential4D (Fiber := Fiber))
    (order : Nat) :
    TruncatedThroatSpatialMultiindexJet Fiber order →L[Real]
      TruncatedThroatSpatialMultiindexJet Fiber order :=
  ContinuousLinearMap.pi fun index =>
    brst.differential.comp (ContinuousLinearMap.proj index)

@[simp] theorem programPT06ContinuousFiberDifferentialJetProlongation_apply
    (brst : ProgramPT06SquareZeroContinuousFiberDifferential4D (Fiber := Fiber))
    (order : Nat) (jet : TruncatedThroatSpatialMultiindexJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ContinuousFiberDifferentialJetProlongation brst order jet index =
      brst.differential (jet index) :=
  rfl

/-- The prolonged jet differential is square-zero. -/
theorem programPT06ContinuousFiberDifferentialJetProlongation_square_zero
    (brst : ProgramPT06SquareZeroContinuousFiberDifferential4D (Fiber := Fiber))
    (order : Nat) (jet : TruncatedThroatSpatialMultiindexJet Fiber order) :
    programPT06ContinuousFiberDifferentialJetProlongation brst order
        (programPT06ContinuousFiberDifferentialJetProlongation brst order jet) =
      0 := by
  funext index
  exact brst.square_zero (jet index)

/-- Jet prolongation commutes with every formal total derivative. -/
theorem
    programPT06ContinuousFiberDifferentialJetProlongation_commutes_totalDerivative
    (brst : ProgramPT06SquareZeroContinuousFiberDifferential4D (Fiber := Fiber))
    {order : Nat} (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06ContinuousFiberDifferentialJetProlongation brst
          (order + 1) jet) =
      programPT06ContinuousFiberDifferentialJetProlongation brst order
        (throatSpatialTotalDerivative direction jet) := by
  rfl

/-- Prolongation commutes with injection into any single jet coordinate. -/
@[simp] theorem
    programPT06ContinuousFiberDifferentialJetProlongation_coordinateInjection
    (brst : ProgramPT06SquareZeroContinuousFiberDifferential4D (Fiber := Fiber))
    (order : Nat) (index : ThroatSpatialTruncatedIndex order)
    (variation : Fiber) :
    programPT06ContinuousFiberDifferentialJetProlongation brst order
        (programPT06ThroatSpatialJetCoordinateInjection index variation) =
      programPT06ThroatSpatialJetCoordinateInjection index
        (brst.differential variation) := by
  funext coordinate
  by_cases hCoordinate : coordinate = index
  · subst coordinate
    simp
  · simp [programPT06ThroatSpatialJetCoordinateInjection, hCoordinate]

/-- Pullback differential on linear order-one horizontal currents. -/
def programPT06AffineSecondOrderCurrentBRST
    (brst : ProgramPT06SquareZeroContinuousFiberDifferential4D (Fiber := Fiber))
    (current : ProgramPT06LinearFirstOrderHorizontalCurrent4D (Fiber := Fiber)) :
    ProgramPT06LinearFirstOrderHorizontalCurrent4D (Fiber := Fiber) :=
  fun direction =>
    (current direction).comp
      (programPT06ContinuousFiberDifferentialJetProlongation brst 1)

/-- Pullback differential on affine second-order densities. -/
def programPT06AffineSecondOrderDensityBRST
    (brst : ProgramPT06SquareZeroContinuousFiberDifferential4D (Fiber := Fiber))
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber)) :
    ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber) :=
  (0, density.2.comp
    (programPT06ContinuousFiberDifferentialJetProlongation brst 2))

/-- The induced differential on affine densities is square-zero. -/
theorem programPT06AffineSecondOrderDensityBRST_square_zero
    (brst : ProgramPT06SquareZeroContinuousFiberDifferential4D (Fiber := Fiber))
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber)) :
    programPT06AffineSecondOrderDensityBRST brst
        (programPT06AffineSecondOrderDensityBRST brst density) = 0 := by
  apply Prod.ext
  · rfl
  · apply ContinuousLinearMap.ext
    intro jet
    change density.2
      (programPT06ContinuousFiberDifferentialJetProlongation brst 2
        (programPT06ContinuousFiberDifferentialJetProlongation brst 2 jet)) = 0
    rw [programPT06ContinuousFiberDifferentialJetProlongation_square_zero,
      map_zero]

/-- The affine horizontal differential is natural for the prolonged fiber
differential. -/
theorem programPT06AffineSecondOrderBRST_commutes_augmentedDH
    (brst : ProgramPT06SquareZeroContinuousFiberDifferential4D (Fiber := Fiber))
    (input : Real ×
      ProgramPT06LinearFirstOrderHorizontalCurrent4D (Fiber := Fiber)) :
    programPT06AffineSecondOrderDensityBRST brst
        (programPT06AffineSecondOrderAugmentedDH (Fiber := Fiber) input) =
      programPT06AffineSecondOrderAugmentedDH (Fiber := Fiber)
        (0, programPT06AffineSecondOrderCurrentBRST brst input.2) := by
  apply Prod.ext
  · rfl
  · apply ContinuousLinearMap.ext
    intro jet
    simp [programPT06AffineSecondOrderDensityBRST,
      programPT06AffineSecondOrderAugmentedDH,
      programPT06AffineSecondOrderLocalDH,
      programPT06AffineSecondOrderCurrentBRST,
      throatSpatialTotalDerivativeLinear]
    apply Finset.sum_congr rfl
    intro direction _
    rw [programPT06ContinuousFiberDifferentialJetProlongation_commutes_totalDerivative]

/-- The affine Euler coefficient intertwines the density BRST differential
with the original fiber differential. -/
theorem programPT06AffineSecondOrderLocalEuler_BRST_natural
    (brst : ProgramPT06SquareZeroContinuousFiberDifferential4D (Fiber := Fiber))
    (density : ProgramPT06AffineSecondOrderLocalDensity4D (Fiber := Fiber)) :
    programPT06AffineSecondOrderLocalEuler (Fiber := Fiber)
        (programPT06AffineSecondOrderDensityBRST brst density) =
      (programPT06AffineSecondOrderLocalEuler (Fiber := Fiber) density).comp
        brst.differential := by
  apply ContinuousLinearMap.ext
  intro variation
  change density.2
      (programPT06ContinuousFiberDifferentialJetProlongation brst 2
        (programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex variation)) =
    density.2
      (programPT06ThroatSpatialJetCoordinateInjection
        programPT06SecondOrderZeroMultiIndex
        (brst.differential variation))
  rw [programPT06ContinuousFiberDifferentialJetProlongation_coordinateInjection]

end
end P0EFTJanusProgramPT06AffineSecondOrderBRSTNaturality4D
end JanusFormal
