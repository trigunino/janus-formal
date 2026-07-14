import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAdaptedFrameOverlapCocycle

namespace JanusFormal
namespace P0EFTJanusNormalFramePointwiseTransition

set_option autoImplicit false

noncomputable section

universe u v

variable {Normal : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]

/-- Ambient image subspace of one linear isometric normal frame. -/
def normalFrameRange (frame : Normal →ₗᵢ[ℝ] Ambient) :
    Submodule ℝ Ambient :=
  LinearMap.range frame.toLinearMap

/-- Canonical change of normal coordinates between two linear isometric frames
with the same ambient image.

The convention is

`first (g normal) = second normal`,

so `g = first⁻¹ second` on the common image. -/
def normalFrameTransition
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange first = normalFrameRange second) :
    Normal ≃ₗᵢ[ℝ] Normal :=
  second.equivRange |>.trans
    ((LinearIsometryEquiv.ofEq
        (normalFrameRange second)
        (normalFrameRange first)
        hRange.symm).trans
      first.equivRange.symm)

/-- The canonical transition has the required frame-intertwining property. -/
theorem normalFrameTransition_spec
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange first = normalFrameRange second)
    (normal : Normal) :
    first (normalFrameTransition first second hRange normal) =
      second normal := by
  let pointInFirst : normalFrameRange first :=
    LinearIsometryEquiv.ofEq
      (normalFrameRange second)
      (normalFrameRange first)
      hRange.symm
      (second.equivRange normal)
  have hInverse :
      first.equivRange (first.equivRange.symm pointInFirst) =
        pointInFirst :=
    first.equivRange.apply_symm_apply pointInFirst
  change first (first.equivRange.symm pointInFirst) = second normal
  calc
    first (first.equivRange.symm pointInFirst) =
        (pointInFirst : Ambient) := by
      exact congrArg Subtype.val hInverse
    _ = second normal := by
      rfl

/-- Any orthogonal coordinate transformation intertwining the two frames is the
canonical transition. -/
theorem normalFrameTransition_unique
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange first = normalFrameRange second)
    (candidate : Normal ≃ₗᵢ[ℝ] Normal)
    (hCandidate : ∀ normal, first (candidate normal) = second normal) :
    candidate = normalFrameTransition first second hRange := by
  apply LinearIsometryEquiv.ext
  intro normal
  apply first.injective
  rw [hCandidate normal,
    normalFrameTransition_spec first second hRange normal]

/-- The canonical transition is independent of the proof witnessing equality of
ambient image subspaces. -/
theorem normalFrameTransition_proof_irrel
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (firstProof secondProof :
      normalFrameRange first = normalFrameRange second) :
    normalFrameTransition first second firstProof =
      normalFrameTransition first second secondProof := by
  exact normalFrameTransition_unique first second secondProof
    (normalFrameTransition first second firstProof)
    (normalFrameTransition_spec first second firstProof)

/-- A frame has the identity canonical transition to itself. -/
@[simp]
theorem normalFrameTransition_self
    (frame : Normal →ₗᵢ[ℝ] Ambient) :
    normalFrameTransition frame frame rfl = 1 := by
  symm
  apply normalFrameTransition_unique frame frame rfl
  intro normal
  rfl

/-- Reversing the overlap inverts the canonical transition. -/
theorem normalFrameTransition_reverse
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange first = normalFrameRange second) :
    normalFrameTransition second first hRange.symm =
      (normalFrameTransition first second hRange).symm := by
  symm
  apply normalFrameTransition_unique second first hRange.symm
  intro normal
  have hAt := normalFrameTransition_spec first second hRange
    ((normalFrameTransition first second hRange).symm normal)
  simpa using hAt.symm

/-- Čech composition law for three pointwise normal frames with the same image.
With the convention `first ∘ g₁₂ = second`, the transition satisfies
`g₁₂ * g₂₃ = g₁₃`. -/
theorem normalFrameTransition_cocycle
    (first second third : Normal →ₗᵢ[ℝ] Ambient)
    (hFirstSecond : normalFrameRange first = normalFrameRange second)
    (hSecondThird : normalFrameRange second = normalFrameRange third) :
    normalFrameTransition first second hFirstSecond *
        normalFrameTransition second third hSecondThird =
      normalFrameTransition first third
        (hFirstSecond.trans hSecondThird) := by
  apply normalFrameTransition_unique first third
    (hFirstSecond.trans hSecondThird)
  intro normal
  change
    first
        (normalFrameTransition first second hFirstSecond
          (normalFrameTransition second third hSecondThird normal)) =
      third normal
  rw [normalFrameTransition_spec first second hFirstSecond,
    normalFrameTransition_spec second third hSecondThird]

/-- A frame-intertwining orthogonal transformation forces equality of the two
ambient image subspaces. -/
theorem normalFrameRange_eq_of_transition
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (transition : Normal ≃ₗᵢ[ℝ] Normal)
    (hTransition : ∀ normal, first (transition normal) = second normal) :
    normalFrameRange first = normalFrameRange second := by
  change LinearMap.range first.toLinearMap =
    LinearMap.range second.toLinearMap
  apply le_antisymm
  · rintro value ⟨normal, rfl⟩
    refine ⟨transition.symm normal, ?_⟩
    have hAt := hTransition (transition.symm normal)
    simpa using hAt.symm
  · rintro value ⟨normal, rfl⟩
    exact ⟨transition normal, hTransition normal⟩

/-- Exact pointwise classification: two linear isometric normal frames have the
same image if and only if there is a unique orthogonal coordinate transition
intertwining them. -/
theorem same_normalFrameRange_iff_existsUnique_transition
    (first second : Normal →ₗᵢ[ℝ] Ambient) :
    normalFrameRange first = normalFrameRange second ↔
      ∃! transition : Normal ≃ₗᵢ[ℝ] Normal,
        ∀ normal, first (transition normal) = second normal := by
  constructor
  · intro hRange
    refine ⟨normalFrameTransition first second hRange,
      normalFrameTransition_spec first second hRange, ?_⟩
    intro candidate hCandidate
    exact normalFrameTransition_unique first second hRange
      candidate hCandidate
  · rintro ⟨transition, hTransition, hUnique⟩
    exact normalFrameRange_eq_of_transition first second
      transition hTransition

/-- Exact boundary between pointwise canonical overlap transitions and their
smooth two-jet realization on a normal-frame bundle. -/
structure NormalFramePointwiseTransitionStatus where
  commonImageSubspaceDefined : Prop
  canonicalTransitionConstructed : Prop
  frameIntertwiningProved : Prop
  uniquenessProved : Prop
  reverseLawProved : Prop
  cechCocycleLawProved : Prop
  sameRangeCharacterizationProved : Prop
  smoothTransitionFieldConstructed : Prop
  firstAndSecondTransitionJetsExtracted : Prop
  transitionIdentifiedWithBundleOverlapGauge : Prop

/-- Closure of the smooth normal-frame overlap stage. -/
def normalFramePointwiseTransitionClosed
    (s : NormalFramePointwiseTransitionStatus) : Prop :=
  s.commonImageSubspaceDefined ∧
  s.canonicalTransitionConstructed ∧
  s.frameIntertwiningProved ∧
  s.uniquenessProved ∧
  s.reverseLawProved ∧
  s.cechCocycleLawProved ∧
  s.sameRangeCharacterizationProved ∧
  s.smoothTransitionFieldConstructed ∧
  s.firstAndSecondTransitionJetsExtracted ∧
  s.transitionIdentifiedWithBundleOverlapGauge

/-- Pointwise canonical transitions do not yet prove smooth dependence on the
base point. -/
theorem missing_smooth_transition_blocks_overlap_gauge_realization
    (s : NormalFramePointwiseTransitionStatus)
    (hMissing : Not s.smoothTransitionFieldConstructed) :
    Not (normalFramePointwiseTransitionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusNormalFramePointwiseTransition
end JanusFormal
