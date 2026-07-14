import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFramePointwiseTransition
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorMovingFrame

namespace JanusFormal
namespace P0EFTJanusNormalFrameSmoothTransition

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusRieszShapeOperatorMovingFrame

universe u v w

variable {Normal : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]

/-- The adjoint formula for the coordinate transition between two isometric
normal frames. It is defined without a common-range hypothesis; that hypothesis
is only needed to identify it with an orthogonal equivalence. -/
def normalFrameAdjointTransition
    (first second : Normal →ₗᵢ[ℝ] Ambient) :
    Normal →L[ℝ] Normal :=
  (ContinuousLinearMap.adjoint first.toContinuousLinearMap).comp
    second.toContinuousLinearMap

/-- Inner-product characterization of the adjoint transition. -/
theorem normalFrameAdjointTransition_inner
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (normal test : Normal) :
    ⟪normalFrameAdjointTransition first second normal, test⟫_ℝ =
      ⟪second normal, first test⟫_ℝ := by
  change
    ⟪ContinuousLinearMap.adjoint first.toContinuousLinearMap
        (second normal), test⟫_ℝ =
      ⟪second normal, first test⟫_ℝ
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- On a common image, the adjoint formula is exactly the canonical pointwise
orthogonal transition constructed from the range equivalences. -/
theorem normalFrameAdjointTransition_eq_canonical
    (first second : Normal →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange first = normalFrameRange second) :
    normalFrameAdjointTransition first second =
      (normalFrameTransition first second hRange).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro normal
  apply ext_inner_right ℝ
  intro test
  rw [normalFrameAdjointTransition_inner,
    ← normalFrameTransition_spec first second hRange normal]
  exact first.inner_map_map _ _

/-- Over the real field, taking the Hilbert adjoint is an ordinary continuous
linear map between operator spaces. -/
def realAdjointLinearMap :
    (Normal →L[ℝ] Ambient) →ₗ[ℝ] (Ambient →L[ℝ] Normal) where
  toFun := ContinuousLinearMap.adjoint
  map_add' := by
    intro first second
    exact map_add ContinuousLinearMap.adjoint first second
  map_smul' := by
    intro scalar operator
    simpa using
      map_smulₛₗ ContinuousLinearMap.adjoint scalar operator

/-- Continuous-linear packaging of the real adjoint operation. -/
def realAdjointContinuousLinearMap :
    (Normal →L[ℝ] Ambient) →L[ℝ] (Ambient →L[ℝ] Normal) :=
  realAdjointLinearMap.mkContinuous 1 (by
    intro operator
    change ‖ContinuousLinearMap.adjoint operator‖ ≤ 1 * ‖operator‖
    rw [ContinuousLinearMap.adjoint.norm_map, one_mul])

@[simp]
theorem realAdjointContinuousLinearMap_apply
    (operator : Normal →L[ℝ] Ambient) :
    realAdjointContinuousLinearMap operator =
      ContinuousLinearMap.adjoint operator := by
  rfl

/-- A smooth family of linear isometric embeddings into a fixed ambient Hilbert
model. -/
structure SmoothIsometricNormalFrameFamily
    (Base : Type w) (Normal : Type u) (Ambient : Type v)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient] where
  frame : Base → Normal →ₗᵢ[ℝ] Ambient
  forward_contDiff : ContDiff ℝ ∞
    (fun base => (frame base).toContinuousLinearMap)

/-- Adjoint-composition transition for a pair of smooth isometric frame
families. -/
def smoothAdjointTransitionCLM
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (first second : SmoothIsometricNormalFrameFamily
      Base Normal Ambient) :
    Base → Normal →L[ℝ] Normal :=
  fun base => normalFrameAdjointTransition
    (first.frame base) (second.frame base)

/-- The adjoint-composition transition depends smoothly on the base point. -/
theorem smoothAdjointTransitionCLM_contDiff
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (first second : SmoothIsometricNormalFrameFamily
      Base Normal Ambient) :
    ContDiff ℝ ∞ (smoothAdjointTransitionCLM first second) := by
  change ContDiff ℝ ∞
    (fun base =>
      (realAdjointContinuousLinearMap
        (first.frame base).toContinuousLinearMap).comp
          (second.frame base).toContinuousLinearMap)
  have hAdjoint : ContDiff ℝ ∞
      (fun base => realAdjointContinuousLinearMap
        (first.frame base).toContinuousLinearMap) := by
    simpa [Function.comp_def] using
      realAdjointContinuousLinearMap.contDiff.comp
        first.forward_contDiff
  exact hAdjoint.clm_comp second.forward_contDiff

/-- Canonical smooth orthogonal transition between two smooth isometric normal
frame families with the same image at every base point. -/
def smoothCanonicalNormalFrameTransition
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (first second : SmoothIsometricNormalFrameFamily
      Base Normal Ambient)
    (hRange : ∀ base,
      normalFrameRange (first.frame base) =
        normalFrameRange (second.frame base)) :
    SmoothOrthogonalFrameFamily Base Normal where
  frame := fun base =>
    normalFrameTransition (first.frame base) (second.frame base)
      (hRange base)
  forward_contDiff := by
    change ContDiff ℝ ∞
      (fun base =>
        (normalFrameTransition (first.frame base) (second.frame base)
          (hRange base)).toContinuousLinearEquiv.toContinuousLinearMap)
    have hFunction :
        (fun base =>
          (normalFrameTransition (first.frame base) (second.frame base)
            (hRange base)).toContinuousLinearEquiv.toContinuousLinearMap) =
          smoothAdjointTransitionCLM first second := by
      funext base
      exact (normalFrameAdjointTransition_eq_canonical
        (first.frame base) (second.frame base) (hRange base)).symm
    rw [hFunction]
    exact smoothAdjointTransitionCLM_contDiff first second
  inverse_contDiff := by
    change ContDiff ℝ ∞
      (fun base =>
        ((normalFrameTransition (first.frame base) (second.frame base)
          (hRange base)).symm).toContinuousLinearEquiv.toContinuousLinearMap)
    have hFunction :
        (fun base =>
          ((normalFrameTransition (first.frame base) (second.frame base)
            (hRange base)).symm).toContinuousLinearEquiv.toContinuousLinearMap) =
          smoothAdjointTransitionCLM second first := by
      funext base
      calc
        ((normalFrameTransition (first.frame base) (second.frame base)
            (hRange base)).symm).toContinuousLinearEquiv.toContinuousLinearMap =
          (normalFrameTransition (second.frame base) (first.frame base)
            (hRange base).symm).toContinuousLinearEquiv.toContinuousLinearMap := by
              exact congrArg
                (fun transition : Normal ≃ₗᵢ[ℝ] Normal =>
                  transition.toContinuousLinearEquiv.toContinuousLinearMap)
                (normalFrameTransition_reverse
                  (first.frame base) (second.frame base) (hRange base)).symm
        _ = normalFrameAdjointTransition
            (second.frame base) (first.frame base) :=
          (normalFrameAdjointTransition_eq_canonical
            (second.frame base) (first.frame base)
            (hRange base).symm).symm
    rw [hFunction]
    exact smoothAdjointTransitionCLM_contDiff second first

@[simp]
theorem smoothCanonicalNormalFrameTransition_spec
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (first second : SmoothIsometricNormalFrameFamily
      Base Normal Ambient)
    (hRange : ∀ base,
      normalFrameRange (first.frame base) =
        normalFrameRange (second.frame base))
    (base : Base) (normal : Normal) :
    first.frame base
        ((smoothCanonicalNormalFrameTransition first second hRange).frame
          base normal) =
      second.frame base normal :=
  normalFrameTransition_spec (first.frame base) (second.frame base)
    (hRange base) normal

/-- Pointwise Čech law for the smooth canonical transitions. -/
theorem smoothCanonicalNormalFrameTransition_cocycle_at
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (first second third : SmoothIsometricNormalFrameFamily
      Base Normal Ambient)
    (hFirstSecond : ∀ base,
      normalFrameRange (first.frame base) =
        normalFrameRange (second.frame base))
    (hSecondThird : ∀ base,
      normalFrameRange (second.frame base) =
        normalFrameRange (third.frame base))
    (base : Base) :
    (smoothCanonicalNormalFrameTransition first second hFirstSecond).frame base *
        (smoothCanonicalNormalFrameTransition second third hSecondThird).frame base =
      (smoothCanonicalNormalFrameTransition first third
        (fun point => (hFirstSecond point).trans (hSecondThird point))).frame
        base :=
  normalFrameTransition_cocycle
    (first.frame base) (second.frame base) (third.frame base)
    (hFirstSecond base) (hSecondThird base)

/-- Exact boundary after constructing smooth canonical overlap transitions in a
fixed ambient Hilbert model. -/
structure NormalFrameSmoothTransitionStatus where
  adjointFormulaConstructed : Prop
  adjointFormulaIdentifiedWithCanonicalTransition : Prop
  realAdjointPackagedAsContinuousLinearMap : Prop
  smoothIsometricFrameFamilyDefined : Prop
  transitionSmoothnessProved : Prop
  inverseTransitionSmoothnessProved : Prop
  smoothCechLawProved : Prop
  smoothFrameFamiliesExtractedFromAdaptedGeometry : Prop
  firstAndSecondTransitionJetsMatchedToFrameJets : Prop
  varyingAmbientSubspaceModelHandled : Prop

/-- Closure of the geometric smooth-overlap transition stage. -/
def normalFrameSmoothTransitionClosed
    (s : NormalFrameSmoothTransitionStatus) : Prop :=
  s.adjointFormulaConstructed ∧
  s.adjointFormulaIdentifiedWithCanonicalTransition ∧
  s.realAdjointPackagedAsContinuousLinearMap ∧
  s.smoothIsometricFrameFamilyDefined ∧
  s.transitionSmoothnessProved ∧
  s.inverseTransitionSmoothnessProved ∧
  s.smoothCechLawProved ∧
  s.smoothFrameFamiliesExtractedFromAdaptedGeometry ∧
  s.firstAndSecondTransitionJetsMatchedToFrameJets ∧
  s.varyingAmbientSubspaceModelHandled

/-- Fixed-model smoothness still has to be connected to the adapted geometric
frame fields already extracted from the immersion data. -/
theorem missing_geometric_frame_extraction_blocks_transition_jet_matching
    (s : NormalFrameSmoothTransitionStatus)
    (hMissing : Not s.smoothFrameFamiliesExtractedFromAdaptedGeometry) :
    Not (normalFrameSmoothTransitionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusNormalFrameSmoothTransition
end JanusFormal
