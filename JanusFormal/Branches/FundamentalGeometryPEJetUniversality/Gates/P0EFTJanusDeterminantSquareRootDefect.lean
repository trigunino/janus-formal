import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSpinCDiagonalDefectCancellation

namespace JanusFormal
namespace P0EFTJanusDeterminantSquareRootDefect

set_option autoImplicit false

noncomputable section

open P0EFTJanusCentralLiftCocycleObstruction
open P0EFTJanusSpinCDiagonalDefectCancellation

universe u v w x

/-- Local choices of square roots of a commutative determinant-line transition
cocycle. The roots need not themselves satisfy the Čech cocycle law. -/
structure SquareRootTransitionChoice
    {PhaseGroup : Type u} [CommGroup PhaseGroup]
    {Index : Type v}
    (determinantLine : TransitionCocycle Index PhaseGroup) where
  root : Index → Index → PhaseGroup
  squares : ∀ i j, root i j * root i j = determinantLine.transition i j

/-- The defect of locally chosen square roots has square one. This is the exact
algebraic source of the `±1` triple-overlap sign in a SpinC construction. -/
theorem squareRoot_phaseDefect_sq
    {PhaseGroup : Type u} [CommGroup PhaseGroup]
    {Index : Type v}
    (determinantLine : TransitionCocycle Index PhaseGroup)
    (choice : SquareRootTransitionChoice determinantLine)
    (i j k : Index) :
    phaseDefect choice.root i j k *
        phaseDefect choice.root i j k = 1 := by
  unfold phaseDefect
  calc
    (((choice.root j k * choice.root i j) * (choice.root i k)⁻¹) *
        ((choice.root j k * choice.root i j) * (choice.root i k)⁻¹)) =
      (choice.root j k * choice.root j k) *
        (choice.root i j * choice.root i j) *
        (choice.root i k * choice.root i k)⁻¹ := by
      rw [mul_inv_rev]
      ac_rfl
    _ = determinantLine.transition j k *
        determinantLine.transition i j *
        (determinantLine.transition i k)⁻¹ := by
      rw [choice.squares j k, choice.squares i j, choice.squares i k]
    _ = 1 := by
      rw [determinantLine.transition_cocycle i j k]
      exact mul_inv_cancel _

/-- A phase group whose two-torsion consists exactly of `1` and one distinguished
central involution. The intended concrete phase group is `U(1)`. -/
structure TwoTorsionPhaseData
    (PhaseGroup : Type u) [CommGroup PhaseGroup]
    extends CentralPhaseInvolution PhaseGroup where
  square_dichotomy : ∀ phase : PhaseGroup,
    phase * phase = 1 →
      phase = 1 ∨ phase = minusOne

/-- Each square-root triple defect is either trivial or the distinguished phase
involution. -/
theorem squareRoot_phaseDefect_dichotomy
    {PhaseGroup : Type u} [CommGroup PhaseGroup]
    {Index : Type v}
    (determinantLine : TransitionCocycle Index PhaseGroup)
    (choice : SquareRootTransitionChoice determinantLine)
    (phaseData : TwoTorsionPhaseData PhaseGroup)
    (i j k : Index) :
    phaseDefect choice.root i j k = 1 ∨
      phaseDefect choice.root i j k = phaseData.minusOne :=
  phaseData.square_dichotomy _
    (squareRoot_phaseDefect_sq determinantLine choice i j k)

/-- Equality of the trivial/nontrivial defect class is enough to establish the
diagonal SpinC cancellation condition. -/
theorem matching_defect_classes_implies_diagonalCancellation
    {SpinGroup : Type u} {BaseGroup : Type v}
    [Group SpinGroup] [Group BaseGroup]
    {PhaseGroup : Type w} [CommGroup PhaseGroup]
    {Index : Type x}
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (orientedCocycle : TransitionCocycle Index BaseGroup)
    (spinLift : ChosenTransitionLift
      spinCover.toCentralCoverData orientedCocycle)
    (determinantLine : TransitionCocycle Index PhaseGroup)
    (rootChoice : SquareRootTransitionChoice determinantLine)
    (phaseData : TwoTorsionPhaseData PhaseGroup)
    (hMatch : ∀ i j k,
      liftDefect spinCover.toCentralCoverData orientedCocycle spinLift i j k = 1 ↔
        phaseDefect rootChoice.root i j k = 1) :
    DiagonalDefectsCancel spinCover orientedCocycle spinLift
      phaseData.toCentralPhaseInvolution rootChoice.root := by
  intro i j k
  rcases doubleCover_liftDefect_dichotomy
      spinCover orientedCocycle spinLift i j k with
    hSpinTrivial | hSpinMinusOne
  · left
    exact ⟨hSpinTrivial, (hMatch i j k).1 hSpinTrivial⟩
  · right
    refine ⟨hSpinMinusOne, ?_⟩
    rcases squareRoot_phaseDefect_dichotomy
        determinantLine rootChoice phaseData i j k with
      hPhaseTrivial | hPhaseMinusOne
    · have hSpinTrivial := (hMatch i j k).2 hPhaseTrivial
      have hImpossible : spinCover.minusOne = 1 :=
        hSpinMinusOne.symm.trans hSpinTrivial
      exact False.elim (spinCover.minusOne_ne_one hImpossible)
    · exact hPhaseMinusOne

/-- Once matching defect classes are established, the abstract diagonal quotient
theorem produces a genuine SpinC cocycle. -/
theorem matching_squareRoot_defects_implies_spinCCocycle
    {SpinGroup : Type u} {BaseGroup : Type v}
    [Group SpinGroup] [Group BaseGroup]
    {PhaseGroup : Type w} [CommGroup PhaseGroup]
    {SpinCGroup : Type*} [Group SpinCGroup]
    {Index : Type x}
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (orientedCocycle : TransitionCocycle Index BaseGroup)
    (spinLift : ChosenTransitionLift
      spinCover.toCentralCoverData orientedCocycle)
    (determinantLine : TransitionCocycle Index PhaseGroup)
    (rootChoice : SquareRootTransitionChoice determinantLine)
    (phaseData : TwoTorsionPhaseData PhaseGroup)
    (spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup)
    (hSpinMinusOne : spinC.spinMinusOne = spinCover.minusOne)
    (hPhaseMinusOne : spinC.phaseMinusOne = phaseData.minusOne)
    (hMatch : ∀ i j k,
      liftDefect spinCover.toCentralCoverData orientedCocycle spinLift i j k = 1 ↔
        phaseDefect rootChoice.root i j k = 1) :
    ∀ i j k,
      spinCTransition spinCover orientedCocycle spinLift rootChoice.root spinC j k *
        spinCTransition spinCover orientedCocycle spinLift rootChoice.root spinC i j =
      spinCTransition spinCover orientedCocycle spinLift rootChoice.root spinC i k := by
  exact diagonalDefectCancellation_implies_spinCCocycle
    spinCover orientedCocycle spinLift phaseData.toCentralPhaseInvolution
    rootChoice.root spinC hSpinMinusOne hPhaseMinusOne
    (matching_defect_classes_implies_diagonalCancellation
      spinCover orientedCocycle spinLift determinantLine rootChoice phaseData hMatch)

/-- Boundary after the determinant-square-root defect theorem. -/
structure DeterminantSquareRootDefectStatus where
  determinantLineCocycleConstructed : Prop
  localSquareRootsChosen : Prop
  squareRootDefectSquareOneProved : Prop
  phaseTwoTorsionClassified : Prop
  spinDefectClassConstructed : Prop
  phaseDefectClassConstructed : Prop
  defectClassMatchingProved : Prop
  diagonalCancellationDerived : Prop
  spinCCocycleDerived : Prop
  circlePhaseGroupInstantiated : Prop
  determinantLineGeometricallyIdentified : Prop
  characteristicClassCriterionProved : Prop

/-- Closure of the determinant square-root / SpinC compensation stage. -/
def determinantSquareRootDefectClosed
    (s : DeterminantSquareRootDefectStatus) : Prop :=
  s.determinantLineCocycleConstructed /\
  s.localSquareRootsChosen /\
  s.squareRootDefectSquareOneProved /\
  s.phaseTwoTorsionClassified /\
  s.spinDefectClassConstructed /\
  s.phaseDefectClassConstructed /\
  s.defectClassMatchingProved /\
  s.diagonalCancellationDerived /\
  s.spinCCocycleDerived /\
  s.circlePhaseGroupInstantiated /\
  s.determinantLineGeometricallyIdentified /\
  s.characteristicClassCriterionProved

/-- Local roots and two-torsion alone do not prove that the determinant-line
defect matches the Spin lifting obstruction. -/
theorem missing_defect_matching_blocks_spinC_construction
    (s : DeterminantSquareRootDefectStatus)
    (hMissing : Not s.defectClassMatchingProved) :
    Not (determinantSquareRootDefectClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.1

end

end P0EFTJanusDeterminantSquareRootDefect
end JanusFormal
