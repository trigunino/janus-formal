import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanGlobalSpinCJetRealization
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSpinCDiagonalDefectCancellation

namespace JanusFormal
namespace P0EFTJanusGlobalSpinCCechDescent

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusCentralLiftCocycleObstruction
open P0EFTJanusSpinCDiagonalDefectCancellation
open P0EFTJanusEuclideanGlobalSpinCJetRealization

universe u v w x y z

/-- Chart indices whose domains contain a specified base point. -/
abbrev ActiveChart
    {Base : Type u} {Index : Type v}
    (domain : Index -> Set Base) (base : Base) :=
  {index : Index // base ∈ domain index}

/-- Conditional input for multi-chart SpinC descent.  At every base point it
supplies an oriented transition cocycle on the active charts, chosen Spin
lifts, phase transitions, and the matching diagonal-defect proof.  No claim is
made here that these data come from a particular Janus characteristic class. -/
structure BasewiseSpinCDescentData
    {Base : Type u} {Index : Type v}
    {SpinGroup : Type w} {BaseGroup : Type x}
    {PhaseGroup : Type y} {SpinCGroup : Type z}
    [Group SpinGroup] [Group BaseGroup] [Group PhaseGroup] [Group SpinCGroup]
    (domain : Index -> Set Base)
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (phaseData : CentralPhaseInvolution PhaseGroup)
    (spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup) where
  orientedCocycle :
    ∀ base, TransitionCocycle (ActiveChart domain base) BaseGroup
  spinLift :
    ∀ base, ChosenTransitionLift spinCover.toCentralCoverData
      (orientedCocycle base)
  phase :
    ∀ base,
      ActiveChart domain base -> ActiveChart domain base -> PhaseGroup
  spinMinusOne_matches : spinC.spinMinusOne = spinCover.minusOne
  phaseMinusOne_matches : spinC.phaseMinusOne = phaseData.minusOne
  defects_cancel :
    ∀ base, DiagonalDefectsCancel spinCover (orientedCocycle base)
      (spinLift base) phaseData (phase base)

/-- SpinC transition between active charts.  The indices are reversed because
`TransitionCocycle` uses `g_jk * g_ij = g_ik`, whereas
`CechPrincipalBundleData` uses `g_ij * g_jk = g_ik`. -/
def activeSpinCTransition
    {Base : Type u} {Index : Type v}
    {SpinGroup : Type w} {BaseGroup : Type x}
    {PhaseGroup : Type y} {SpinCGroup : Type z}
    [Group SpinGroup] [Group BaseGroup] [Group PhaseGroup] [Group SpinCGroup]
    {domain : Index -> Set Base}
    {spinCover : CentralDoubleCoverData SpinGroup BaseGroup}
    {phaseData : CentralPhaseInvolution PhaseGroup}
    {spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup}
    (data : BasewiseSpinCDescentData domain spinCover phaseData spinC)
    (base : Base) (first second : ActiveChart domain base) : SpinCGroup :=
  spinCTransition spinCover (data.orientedCocycle base) (data.spinLift base)
    (data.phase base) spinC second first

/-- Matching Spin and phase defects give the overlap law in the convention
required by the principal-bundle presentation. -/
theorem activeSpinCTransition_cocycle
    {Base : Type u} {Index : Type v}
    {SpinGroup : Type w} {BaseGroup : Type x}
    {PhaseGroup : Type y} {SpinCGroup : Type z}
    [Group SpinGroup] [Group BaseGroup] [Group PhaseGroup] [Group SpinCGroup]
    {domain : Index -> Set Base}
    {spinCover : CentralDoubleCoverData SpinGroup BaseGroup}
    {phaseData : CentralPhaseInvolution PhaseGroup}
    {spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup}
    (data : BasewiseSpinCDescentData domain spinCover phaseData spinC)
    (base : Base) (first second third : ActiveChart domain base) :
    activeSpinCTransition data base first second *
        activeSpinCTransition data base second third =
      activeSpinCTransition data base first third := by
  exact diagonalDefectCancellation_implies_spinCCocycle
    spinCover (data.orientedCocycle base) (data.spinLift base)
    phaseData (data.phase base) spinC data.spinMinusOne_matches
    data.phaseMinusOne_matches (data.defects_cancel base) third second first

/-- The active-chart transition from a chart to itself is the identity. -/
@[simp]
theorem activeSpinCTransition_self
    {Base : Type u} {Index : Type v}
    {SpinGroup : Type w} {BaseGroup : Type x}
    {PhaseGroup : Type y} {SpinCGroup : Type z}
    [Group SpinGroup] [Group BaseGroup] [Group PhaseGroup] [Group SpinCGroup]
    {domain : Index -> Set Base}
    {spinCover : CentralDoubleCoverData SpinGroup BaseGroup}
    {phaseData : CentralPhaseInvolution PhaseGroup}
    {spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup}
    (data : BasewiseSpinCDescentData domain spinCover phaseData spinC)
    (base : Base) (index : ActiveChart domain base) :
    activeSpinCTransition data base index index = 1 := by
  have hCocycle := activeSpinCTransition_cocycle data base index index index
  have hCancel := congrArg
    (fun element : SpinCGroup =>
      element * (activeSpinCTransition data base index index)⁻¹)
    hCocycle
  simpa [mul_assoc] using hCancel

/-- Opposite active-chart transitions are mutual inverses. -/
theorem activeSpinCTransition_inverse
    {Base : Type u} {Index : Type v}
    {SpinGroup : Type w} {BaseGroup : Type x}
    {PhaseGroup : Type y} {SpinCGroup : Type z}
    [Group SpinGroup] [Group BaseGroup] [Group PhaseGroup] [Group SpinCGroup]
    {domain : Index -> Set Base}
    {spinCover : CentralDoubleCoverData SpinGroup BaseGroup}
    {phaseData : CentralPhaseInvolution PhaseGroup}
    {spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup}
    (data : BasewiseSpinCDescentData domain spinCover phaseData spinC)
    (base : Base) (first second : ActiveChart domain base) :
    activeSpinCTransition data base first second *
        activeSpinCTransition data base second first = 1 := by
  rw [activeSpinCTransition_cocycle data base first second first]
  exact activeSpinCTransition_self data base first

/-- Total transition function.  Its value away from a double overlap is
irrelevant to the Cech laws and is fixed to the identity. -/
def globalSpinCTransition
    {Base : Type u} {Index : Type v}
    {SpinGroup : Type w} {BaseGroup : Type x}
    {PhaseGroup : Type y} {SpinCGroup : Type z}
    [Group SpinGroup] [Group BaseGroup] [Group PhaseGroup] [Group SpinCGroup]
    {domain : Index -> Set Base}
    {spinCover : CentralDoubleCoverData SpinGroup BaseGroup}
    {phaseData : CentralPhaseInvolution PhaseGroup}
    {spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup}
    (data : BasewiseSpinCDescentData domain spinCover phaseData spinC)
    (first second : Index) (base : Base) : SpinCGroup := by
  classical
  exact if hFirst : base ∈ domain first then
    if hSecond : base ∈ domain second then
      activeSpinCTransition data base ⟨first, hFirst⟩ ⟨second, hSecond⟩
    else 1
  else 1

/-- On a genuine double overlap, the total transition is the reversed-index
SpinC transition obtained by diagonal defect cancellation. -/
theorem globalSpinCTransition_of_mem
    {Base : Type u} {Index : Type v}
    {SpinGroup : Type w} {BaseGroup : Type x}
    {PhaseGroup : Type y} {SpinCGroup : Type z}
    [Group SpinGroup] [Group BaseGroup] [Group PhaseGroup] [Group SpinCGroup]
    {domain : Index -> Set Base}
    {spinCover : CentralDoubleCoverData SpinGroup BaseGroup}
    {phaseData : CentralPhaseInvolution PhaseGroup}
    {spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup}
    (data : BasewiseSpinCDescentData domain spinCover phaseData spinC)
    (first second : Index) (base : Base)
    (hFirst : base ∈ domain first) (hSecond : base ∈ domain second) :
    globalSpinCTransition data first second base =
      activeSpinCTransition data base ⟨first, hFirst⟩ ⟨second, hSecond⟩ := by
  simp only [globalSpinCTransition, dif_pos hFirst, dif_pos hSecond]

/-- Conditional pointwise multi-chart SpinC Cech presentation. Supplied
matching defects give identity, inverse, and cocycle laws. This does not assert
continuity or smoothness in the base, nor construct a geometric total space. -/
def globalSpinCCechPresentation
    {Base : Type u} {Index : Type v}
    {SpinGroup : Type w} {BaseGroup : Type x}
    {PhaseGroup : Type y} {SpinCGroup : Type z}
    [TopologicalSpace Base]
    [Group SpinGroup] [Group BaseGroup] [Group PhaseGroup] [Group SpinCGroup]
    (domain : Index -> Set Base)
    (domain_isOpen : ∀ index, IsOpen (domain index))
    (cover : ∀ base, ∃ index, base ∈ domain index)
    (spinCover : CentralDoubleCoverData SpinGroup BaseGroup)
    (phaseData : CentralPhaseInvolution PhaseGroup)
    (spinC : SpinCDiagonalQuotientData SpinGroup PhaseGroup SpinCGroup)
    (data : BasewiseSpinCDescentData domain spinCover phaseData spinC) :
    CechPrincipalBundleData Base Index SpinCGroup where
  domain := domain
  domain_isOpen := domain_isOpen
  cover := cover
  transition := globalSpinCTransition data
  transition_self := by
    intro index base hIndex
    rw [globalSpinCTransition_of_mem data index index base hIndex hIndex]
    exact activeSpinCTransition_self data base ⟨index, hIndex⟩
  transition_inverse := by
    intro first second base hFirst hSecond
    rw [globalSpinCTransition_of_mem data first second base hFirst hSecond]
    rw [globalSpinCTransition_of_mem data second first base hSecond hFirst]
    exact activeSpinCTransition_inverse data base
      ⟨first, hFirst⟩ ⟨second, hSecond⟩
  transition_cocycle := by
    intro first second third base hFirst hSecond hThird
    rw [globalSpinCTransition_of_mem data first second base hFirst hSecond]
    rw [globalSpinCTransition_of_mem data second third base hSecond hThird]
    rw [globalSpinCTransition_of_mem data first third base hFirst hThird]
    exact activeSpinCTransition_cocycle data base
      ⟨first, hFirst⟩ ⟨second, hSecond⟩ ⟨third, hThird⟩

end

end P0EFTJanusGlobalSpinCCechDescent
end JanusFormal
