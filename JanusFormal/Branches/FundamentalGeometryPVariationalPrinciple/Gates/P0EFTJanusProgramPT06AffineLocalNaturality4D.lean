import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AffineLocalVariationalComplex4D

/-!
# Naturality of the affine local T06 complex

Every continuous linear field endomorphism induces coefficientwise or
pullback maps on the local multi-index jet tower, affine currents and affine
densities.  Formal total derivatives, `dH` and the local Euler map are natural
for these maps.  A
square-zero field differential also commutes with the induced density action
whenever it commutes with the field endomorphism.

The base point and spacetime indices stay fixed.  This is a mechanism needed
by a future deck realization, not a group action or a physical deck/BV action
on the complete Candidate-A carrier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AffineLocalNaturality4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPPhysicalMultiindexJetTower4D
open P0EFTJanusProgramPT06AffineLocalVariationalComplex4D

universe u

variable (FieldFiber : Type u)
  [NormedAddCommGroup FieldFiber] [NormedSpace Real FieldFiber]

/-- Coefficientwise action of a continuous linear field endomorphism on a
finite four-dimensional multi-index jet. -/
def programPT06AffineJetAction
    (action : FieldFiber →L[Real] FieldFiber) (order : Nat)
    (jet : TruncatedMultiindexJet4D FieldFiber order) :
    TruncatedMultiindexJet4D FieldFiber order :=
  fun index => action (jet index)

/-- Coefficientwise jet actions commute with every formal total derivative. -/
theorem programPT06AffineJetAction_commutes_totalDerivative
    (action : FieldFiber →L[Real] FieldFiber) (order : Nat)
    (direction : Fin 4)
    (jet : TruncatedMultiindexJet4D FieldFiber (order + 1)) :
    totalDerivative direction
        (programPT06AffineJetAction FieldFiber action (order + 1) jet) =
      programPT06AffineJetAction FieldFiber action order
        (totalDerivative direction jet) := by
  rfl

/-- Pullback action on affine zeroth-order currents. -/
def programPT06AffineCurrentAction
    (action : FieldFiber →L[Real] FieldFiber)
    (current : ProgramPT06AffineZerothOrderCurrent4D FieldFiber) :
    ProgramPT06AffineZerothOrderCurrent4D FieldFiber :=
  fun direction => (current direction).comp action

/-- Pullback action on affine first-order densities. -/
def programPT06AffineDensityAction
    (action : FieldFiber →L[Real] FieldFiber)
    (density : ProgramPT06AffineFirstOrderDensity4D FieldFiber) :
    ProgramPT06AffineFirstOrderDensity4D FieldFiber :=
  (density.1, (density.2.1.comp action,
    fun direction => (density.2.2 direction).comp action))

/-- Density evaluation after pullback agrees with evaluation on the acted-on
jet. -/
theorem programPT06AffineDensityAction_evaluation
    (action : FieldFiber →L[Real] FieldFiber)
    (density : ProgramPT06AffineFirstOrderDensity4D FieldFiber)
    (jet : TruncatedMultiindexJet4D FieldFiber 1) :
    programPT06AffineDensityEvaluation FieldFiber
        (programPT06AffineDensityAction FieldFiber action density) jet =
      programPT06AffineDensityEvaluation FieldFiber density
        (programPT06AffineJetAction FieldFiber action 1 jet) := by
  rfl

/-- The local horizontal differential is natural under every linear field
action. -/
theorem programPT06AffineDensityAction_commutes_localDH
    (action : FieldFiber →L[Real] FieldFiber)
    (current : ProgramPT06AffineZerothOrderCurrent4D FieldFiber) :
    programPT06AffineDensityAction FieldFiber action
        (programPT06AffineCurrentLocalDH FieldFiber current) =
      programPT06AffineCurrentLocalDH FieldFiber
        (programPT06AffineCurrentAction FieldFiber action current) := by
  rfl

/-- The local Euler coefficient transforms by pullback under every linear
field action. -/
theorem programPT06AffineLocalEuler_natural
    (action : FieldFiber →L[Real] FieldFiber)
    (density : ProgramPT06AffineFirstOrderDensity4D FieldFiber) :
    programPT06AffineLocalEuler FieldFiber
        (programPT06AffineDensityAction FieldFiber action density) =
      (programPT06AffineLocalEuler FieldFiber density).comp action := by
  rfl

/-- A commuting field action also commutes with the induced BRST-type
differential on affine densities. -/
theorem programPT06AffineDensityAction_commutes_BRST
    (action : FieldFiber →L[Real] FieldFiber)
    (brst : ProgramPT06SquareZeroFieldDifferential4D FieldFiber)
    (hCommutes : brst.differential.comp action =
      action.comp brst.differential)
    (density : ProgramPT06AffineFirstOrderDensity4D FieldFiber) :
    programPT06AffineDensityAction FieldFiber action
        (programPT06AffineDensityBRST FieldFiber brst density) =
      programPT06AffineDensityBRST FieldFiber brst
        (programPT06AffineDensityAction FieldFiber action density) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply ContinuousLinearMap.ext
      intro field
      have hAtField := DFunLike.congr_fun hCommutes field
      exact congrArg density.2.1 hAtField
    · funext direction
      apply ContinuousLinearMap.ext
      intro field
      have hAtField := DFunLike.congr_fun hCommutes field
      exact congrArg (density.2.2 direction) hAtField

end

end P0EFTJanusProgramPT06AffineLocalNaturality4D
end JanusFormal
