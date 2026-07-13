import Mathlib.Analysis.Complex.Circle
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusDeterminantSquareRootDefect

namespace JanusFormal
namespace P0EFTJanusCirclePhaseTwoTorsion

set_option autoImplicit false

noncomputable section

open P0EFTJanusCentralLiftCocycleObstruction
open P0EFTJanusSpinCDiagonalDefectCancellation
open P0EFTJanusDeterminantSquareRootDefect

universe u

/-- The distinguished phase involution in `U(1)` is the complex phase `-1`. -/
def circlePhaseInvolution : CentralPhaseInvolution Circle where
  minusOne := -1
  minusOne_ne_one := Circle.neg_ne_self 1
  minusOne_sq := by
    apply Circle.ext
    norm_num
  minusOne_central := by
    intro phase
    exact mul_comm _ _

/-- The only elements of the complex unit circle with square one are `+1` and
`-1`. -/
theorem circle_square_eq_one_dichotomy
    (phase : Circle)
    (hSquare : phase * phase = 1) :
    phase = 1 ∨ phase = -1 := by
  have hCoeSquare : (phase : ℂ) * (phase : ℂ) = 1 := by
    simpa using congrArg (fun value : Circle => (value : ℂ)) hSquare
  have hFactor :
      ((phase : ℂ) - 1) * ((phase : ℂ) + 1) = 0 := by
    calc
      ((phase : ℂ) - 1) * ((phase : ℂ) + 1) =
          (phase : ℂ) * (phase : ℂ) - 1 := by
        ring
      _ = 0 := by
        rw [hCoeSquare]
        ring
  rcases mul_eq_zero.mp hFactor with hOne | hMinusOne
  · left
    apply Circle.ext
    exact sub_eq_zero.mp hOne
  · right
    apply Circle.ext
    have hCoe : (phase : ℂ) = -(1 : ℂ) :=
      eq_neg_of_add_eq_zero_left hMinusOne
    simpa using hCoe

/-- Concrete two-torsion phase data for `U(1)`. -/
def circleTwoTorsionPhaseData : TwoTorsionPhaseData Circle where
  toCentralPhaseInvolution := circlePhaseInvolution
  square_dichotomy := circle_square_eq_one_dichotomy

@[simp]
theorem circleTwoTorsionPhaseData_minusOne :
    circleTwoTorsionPhaseData.minusOne = (-1 : Circle) := by
  rfl

/-- Consequently, every triple defect of local square roots of a circle-valued
line cocycle is exactly `+1` or `-1`. -/
theorem circle_squareRoot_phaseDefect_dichotomy
    {Index : Type u}
    (determinantLine : TransitionCocycle Index Circle)
    (choice : SquareRootTransitionChoice determinantLine)
    (i j k : Index) :
    phaseDefect choice.root i j k = 1 ∨
      phaseDefect choice.root i j k = (-1 : Circle) := by
  simpa using squareRoot_phaseDefect_dichotomy
    determinantLine choice circleTwoTorsionPhaseData i j k

/-- Matching the Spin defect class with the trivial/nontrivial circle-phase
class gives the diagonal SpinC cancellation condition. -/
theorem matching_circle_defects_implies_diagonalCancellation
    {SpinGroup : Type u} {BaseGroup : Type*}
    [Group SpinGroup] [Group BaseGroup]
    {Index : Type*}
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (orientedCocycle : TransitionCocycle Index BaseGroup)
    (spinLift : ChosenTransitionLift
      spinCover.toCentralCoverData orientedCocycle)
    (determinantLine : TransitionCocycle Index Circle)
    (rootChoice : SquareRootTransitionChoice determinantLine)
    (hMatch : ∀ i j k,
      liftDefect spinCover.toCentralCoverData orientedCocycle spinLift i j k = 1 ↔
        phaseDefect rootChoice.root i j k = 1) :
    DiagonalDefectsCancel spinCover orientedCocycle spinLift
      circlePhaseInvolution rootChoice.root := by
  exact matching_defect_classes_implies_diagonalCancellation
    spinCover orientedCocycle spinLift determinantLine rootChoice
    circleTwoTorsionPhaseData hMatch

/-- Boundary after the concrete `U(1)` two-torsion theorem. -/
structure CirclePhaseTwoTorsionStatus where
  complexCirclePhaseGroupInserted : Prop
  minusOnePhaseConstructed : Prop
  minusOneNontrivialProved : Prop
  squareOneDichotomyProved : Prop
  squareRootDefectsClassified : Prop
  circleDefectMatchingWithSpinProved : Prop
  determinantLineCocycleDerivedFromGeometry : Prop
  localSquareRootsConstructedOnGoodCover : Prop
  characteristicClassMatchingProved : Prop
  spinCPrincipalBundleConstructed : Prop

/-- Closure of the concrete phase/Spin matching stage. -/
def circlePhaseTwoTorsionClosed
    (s : CirclePhaseTwoTorsionStatus) : Prop :=
  s.complexCirclePhaseGroupInserted /\
  s.minusOnePhaseConstructed /\
  s.minusOneNontrivialProved /\
  s.squareOneDichotomyProved /\
  s.squareRootDefectsClassified /\
  s.circleDefectMatchingWithSpinProved /\
  s.determinantLineCocycleDerivedFromGeometry /\
  s.localSquareRootsConstructedOnGoodCover /\
  s.characteristicClassMatchingProved /\
  s.spinCPrincipalBundleConstructed

/-- The circle two-torsion theorem does not establish the geometric equality of
Spin and determinant-line obstruction classes. -/
theorem missing_characteristic_matching_blocks_concrete_spinC
    (s : CirclePhaseTwoTorsionStatus)
    (hMissing : Not s.characteristicClassMatchingProved) :
    Not (circlePhaseTwoTorsionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusCirclePhaseTwoTorsion
end JanusFormal
