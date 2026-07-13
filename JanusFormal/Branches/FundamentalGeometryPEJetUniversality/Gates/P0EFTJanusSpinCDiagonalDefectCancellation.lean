import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCentralLiftCocycleObstruction

namespace JanusFormal
namespace P0EFTJanusSpinCDiagonalDefectCancellation

set_option autoImplicit false

noncomputable section

open P0EFTJanusCentralLiftCocycleObstruction

universe u v w x y

/-- A phase group with a distinguished central involution. The intended
instantiation is the element `-1` in `U(1)`. -/
structure CentralPhaseInvolution
    (PhaseGroup : Type u) [Group PhaseGroup] where
  minusOne : PhaseGroup
  minusOne_ne_one : minusOne ≠ 1
  minusOne_sq : minusOne * minusOne = 1
  minusOne_central : ∀ phase : PhaseGroup,
    minusOne * phase = phase * minusOne

/-- Abstract SpinC-style diagonal quotient. The map kills the pair consisting
of the nontrivial Spin kernel element and the phase involution. A concrete
SpinC group should arise from the quotient `(Spin × U(1)) / {±(1,1)}`. -/
structure SpinCDiagonalQuotientData
    (SpinGroup : Type u) (PhaseGroup : Type v) (SpinCGroup : Type w)
    [Group SpinGroup] [Group PhaseGroup] [Group SpinCGroup] where
  quotient : (SpinGroup × PhaseGroup) →* SpinCGroup
  spinMinusOne : SpinGroup
  phaseMinusOne : PhaseGroup
  diagonalMinusOne_killed :
    quotient (spinMinusOne, phaseMinusOne) = 1

/-- Triple-overlap defect of a phase transition family. -/
def phaseDefect
    {PhaseGroup : Type v} [Group PhaseGroup]
    {Index : Type x}
    (phase : Index → Index → PhaseGroup)
    (i j k : Index) : PhaseGroup :=
  (phase j k * phase i j) * (phase i k)⁻¹

/-- SpinC transition obtained by pairing a chosen Spin lift with a phase
transition and applying the diagonal quotient map. -/
def spinCTransition
    {SpinGroup : Type u} {PhaseGroup : Type v} {SpinCGroup : Type w}
    [Group SpinGroup] [Group PhaseGroup] [Group SpinCGroup]
    {BaseGroup : Type y} [Group BaseGroup]
    {Index : Type x}
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (spinLift : ChosenTransitionLift spinCover.toCentralCoverData base)
    (phase : Index → Index → PhaseGroup)
    (spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup)
    (i j : Index) : SpinCGroup :=
  spinC.quotient (spinLift.lift i j, phase i j)

/-- The paired Spin/phase defect on a triple overlap. -/
def pairedDefect
    {SpinGroup : Type u} {PhaseGroup : Type v}
    [Group SpinGroup] [Group PhaseGroup]
    {BaseGroup : Type y} [Group BaseGroup]
    {Index : Type x}
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (spinLift : ChosenTransitionLift spinCover.toCentralCoverData base)
    (phase : Index → Index → PhaseGroup)
    (i j k : Index) : SpinGroup × PhaseGroup :=
  (liftDefect spinCover.toCentralCoverData base spinLift i j k,
    phaseDefect phase i j k)

/-- Defect cancellation condition: each triple defect is either jointly trivial
or jointly equal to the two distinguished `-1` elements. -/
def DiagonalDefectsCancel
    {SpinGroup : Type u} {PhaseGroup : Type v}
    [Group SpinGroup] [Group PhaseGroup]
    {BaseGroup : Type y} [Group BaseGroup]
    {Index : Type x}
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (spinLift : ChosenTransitionLift spinCover.toCentralCoverData base)
    (phaseData : CentralPhaseInvolution PhaseGroup)
    (phase : Index → Index → PhaseGroup) : Prop :=
  ∀ i j k,
    (liftDefect spinCover.toCentralCoverData base spinLift i j k = 1 ∧
      phaseDefect phase i j k = 1) ∨
    (liftDefect spinCover.toCentralCoverData base spinLift i j k =
        spinCover.minusOne ∧
      phaseDefect phase i j k = phaseData.minusOne)

/-- Image of the paired defect under the SpinC quotient is trivial whenever the
Spin and phase defects cancel diagonally. -/
theorem quotient_pairedDefect_eq_one
    {SpinGroup : Type u} {PhaseGroup : Type v} {SpinCGroup : Type w}
    [Group SpinGroup] [Group PhaseGroup] [Group SpinCGroup]
    {BaseGroup : Type y} [Group BaseGroup]
    {Index : Type x}
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (spinLift : ChosenTransitionLift spinCover.toCentralCoverData base)
    (phaseData : CentralPhaseInvolution PhaseGroup)
    (phase : Index → Index → PhaseGroup)
    (spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup)
    (hSpinMinusOne : spinC.spinMinusOne = spinCover.minusOne)
    (hPhaseMinusOne : spinC.phaseMinusOne = phaseData.minusOne)
    (hCancel : DiagonalDefectsCancel spinCover base spinLift phaseData phase)
    (i j k : Index) :
    spinC.quotient (pairedDefect spinCover base spinLift phase i j k) = 1 := by
  rcases hCancel i j k with hTrivial | hDiagonal
  · rw [pairedDefect, hTrivial.1, hTrivial.2]
    exact spinC.quotient.map_one
  · rw [pairedDefect, hDiagonal.1, hDiagonal.2,
      ← hSpinMinusOne, ← hPhaseMinusOne]
    exact spinC.diagonalMinusOne_killed

/-- Algebraic relation between the quotient of the paired defect and the failure
of the projected SpinC transitions to satisfy the cocycle law. -/
theorem spinCTransition_defect_formula
    {SpinGroup : Type u} {PhaseGroup : Type v} {SpinCGroup : Type w}
    [Group SpinGroup] [Group PhaseGroup] [Group SpinCGroup]
    {BaseGroup : Type y} [Group BaseGroup]
    {Index : Type x}
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (spinLift : ChosenTransitionLift spinCover.toCentralCoverData base)
    (phase : Index → Index → PhaseGroup)
    (spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup)
    (i j k : Index) :
    (spinCTransition spinCover base spinLift phase spinC j k *
        spinCTransition spinCover base spinLift phase spinC i j) *
      (spinCTransition spinCover base spinLift phase spinC i k)⁻¹ =
      spinC.quotient (pairedDefect spinCover base spinLift phase i j k) := by
  simp only [spinCTransition, pairedDefect, liftDefect, phaseDefect]
  rw [← spinC.quotient.map_mul, ← spinC.quotient.map_mul,
    ← spinC.quotient.map_inv]
  rfl

/-- Main abstract SpinC cancellation theorem: matching central Spin and phase
defects produce a genuine SpinC transition cocycle. -/
theorem diagonalDefectCancellation_implies_spinCCocycle
    {SpinGroup : Type u} {PhaseGroup : Type v} {SpinCGroup : Type w}
    [Group SpinGroup] [Group PhaseGroup] [Group SpinCGroup]
    {BaseGroup : Type y} [Group BaseGroup]
    {Index : Type x}
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (spinLift : ChosenTransitionLift spinCover.toCentralCoverData base)
    (phaseData : CentralPhaseInvolution PhaseGroup)
    (phase : Index → Index → PhaseGroup)
    (spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup)
    (hSpinMinusOne : spinC.spinMinusOne = spinCover.minusOne)
    (hPhaseMinusOne : spinC.phaseMinusOne = phaseData.minusOne)
    (hCancel : DiagonalDefectsCancel spinCover base spinLift phaseData phase) :
    ∀ i j k,
      spinCTransition spinCover base spinLift phase spinC j k *
        spinCTransition spinCover base spinLift phase spinC i j =
      spinCTransition spinCover base spinLift phase spinC i k := by
  intro i j k
  have hDefect := spinCTransition_defect_formula
    spinCover base spinLift phase spinC i j k
  have hQuotient := quotient_pairedDefect_eq_one
    spinCover base spinLift phaseData phase spinC
    hSpinMinusOne hPhaseMinusOne hCancel i j k
  rw [hQuotient] at hDefect
  have hMultiply := congrArg
    (fun element : SpinCGroup =>
      element * spinCTransition spinCover base spinLift phase spinC i k)
    hDefect
  simpa [mul_assoc] using hMultiply

/-- If the Spin lifts already satisfy their cocycle and the phase transitions do
too, diagonal cancellation holds trivially. -/
theorem trivialDefectsCancel
    {SpinGroup : Type u} {PhaseGroup : Type v}
    [Group SpinGroup] [Group PhaseGroup]
    {BaseGroup : Type y} [Group BaseGroup]
    {Index : Type x}
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (spinLift : ChosenTransitionLift spinCover.toCentralCoverData base)
    (phaseData : CentralPhaseInvolution PhaseGroup)
    (phase : Index → Index → PhaseGroup)
    (hSpin : IsLiftedCocycle spinCover.toCentralCoverData base spinLift)
    (hPhase : ∀ i j k,
      phase j k * phase i j = phase i k) :
    DiagonalDefectsCancel spinCover base spinLift phaseData phase := by
  intro i j k
  left
  constructor
  · exact (liftDefect_eq_one_iff
      spinCover.toCentralCoverData base spinLift i j k).2
      (hSpin i j k)
  · unfold phaseDefect
    rw [hPhase i j k]
    exact mul_inv_cancel _

/-- Exact boundary after abstract diagonal defect cancellation. -/
structure SpinCDiagonalCancellationStatus where
  spinDoubleCoverDataConstructed : Prop
  determinantPhaseInvolutionConstructed : Prop
  diagonalSpinCQuotientConstructed : Prop
  localSpinLiftsChosen : Prop
  localPhaseTransitionsChosen : Prop
  pairedDefectsComputed : Prop
  diagonalCancellationConditionProved : Prop
  spinCCocycleLawProved : Prop
  cliffordSpinCoverInstantiated : Prop
  phaseTransitionsDerivedFromDeterminantLine : Prop
  smoothSpinCPrincipalBundleConstructed : Prop
  spinCConnectionGluingProved : Prop

/-- Closure of the concrete SpinC transition stage. -/
def spinCDiagonalCancellationClosed
    (s : SpinCDiagonalCancellationStatus) : Prop :=
  s.spinDoubleCoverDataConstructed /\
  s.determinantPhaseInvolutionConstructed /\
  s.diagonalSpinCQuotientConstructed /\
  s.localSpinLiftsChosen /\
  s.localPhaseTransitionsChosen /\
  s.pairedDefectsComputed /\
  s.diagonalCancellationConditionProved /\
  s.spinCCocycleLawProved /\
  s.cliffordSpinCoverInstantiated /\
  s.phaseTransitionsDerivedFromDeterminantLine /\
  s.smoothSpinCPrincipalBundleConstructed /\
  s.spinCConnectionGluingProved

/-- The abstract cancellation theorem does not produce determinant-line phases
or prove that their defect matches the Spin defect. -/
theorem missing_determinant_phase_blocks_concrete_spinC
    (s : SpinCDiagonalCancellationStatus)
    (hMissing : Not s.phaseTransitionsDerivedFromDeterminantLine) :
    Not (spinCDiagonalCancellationClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusSpinCDiagonalDefectCancellation
end JanusFormal
