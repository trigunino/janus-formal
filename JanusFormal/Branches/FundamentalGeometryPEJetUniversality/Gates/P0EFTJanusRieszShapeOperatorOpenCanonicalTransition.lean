import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameSmoothTransition
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorOpenMovingFrame

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorOpenCanonicalTransition

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusNormalFrameSmoothTransition
open P0EFTJanusRieszShapeOperatorOpenMovingFrame

universe u v w

/-- Isometric frame family whose underlying operator is smooth on one open chart
domain. -/
structure SmoothIsometricFrameFamilyOn
    (Base : Type w) (Model : Type u) (Ambient : Type v)
    (domain : Set Base)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Model] [InnerProductSpace ℝ Model]
    [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient] where
  frame : Base → Model →ₗᵢ[ℝ] Ambient
  forward_contDiffOn : ContDiffOn ℝ ∞
    (fun base => (frame base).toContinuousLinearMap) domain

variable {Base : Type w} {Model : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Model] [InnerProductSpace ℝ Model]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Model]
variable [FiniteDimensional ℝ Ambient]

/-- Adjoint-composition transition for open-domain isometric frame families. -/
def openAdjointTransitionCLM
    {domain : Set Base}
    (first second : SmoothIsometricFrameFamilyOn
      Base Model Ambient domain) :
    Base → Model →L[ℝ] Model :=
  fun base => normalFrameAdjointTransition
    (first.frame base) (second.frame base)

/-- The adjoint transition is smooth on the common open chart domain. -/
theorem openAdjointTransitionCLM_contDiffOn
    {domain : Set Base}
    (first second : SmoothIsometricFrameFamilyOn
      Base Model Ambient domain) :
    ContDiffOn ℝ ∞ (openAdjointTransitionCLM first second) domain := by
  change ContDiffOn ℝ ∞
    (fun base =>
      (realAdjointContinuousLinearMap
        (first.frame base).toContinuousLinearMap).comp
          (second.frame base).toContinuousLinearMap)
    domain
  have hAdjoint : ContDiffOn ℝ ∞
      (fun base => realAdjointContinuousLinearMap
        (first.frame base).toContinuousLinearMap) domain := by
    exact realAdjointContinuousLinearMap.contDiff.comp_contDiffOn
      first.forward_contDiffOn
  exact hAdjoint.clm_comp second.forward_contDiffOn

/-- Canonical orthogonal transition on an open domain. Outside the domain we use
the identity; no regularity is claimed there. -/
def openCanonicalFrameTransitionValue
    {domain : Set Base}
    (first second : SmoothIsometricFrameFamilyOn
      Base Model Ambient domain)
    (hRange : ∀ base, base ∈ domain →
      normalFrameRange (first.frame base) =
        normalFrameRange (second.frame base))
    (base : Base) : Model ≃ₗᵢ[ℝ] Model := by
  classical
  exact if hValid : base ∈ domain then
    normalFrameTransition (first.frame base) (second.frame base)
      (hRange base hValid)
  else
    LinearIsometryEquiv.refl ℝ Model

/-- Smooth canonical orthogonal transition on an open chart domain. -/
def openCanonicalFrameTransition
    {domain : Set Base}
    (first second : SmoothIsometricFrameFamilyOn
      Base Model Ambient domain)
    (hRange : ∀ base, base ∈ domain →
      normalFrameRange (first.frame base) =
        normalFrameRange (second.frame base)) :
    SmoothOrthogonalFrameFamilyOn Base Model domain where
  frame := openCanonicalFrameTransitionValue first second hRange
  forward_contDiffOn := by
    apply (openAdjointTransitionCLM_contDiffOn first second).congr
    intro base hValid
    change
      ((openCanonicalFrameTransitionValue first second hRange base).toContinuousLinearEquiv.toContinuousLinearMap) =
        openAdjointTransitionCLM first second base
    rw [openCanonicalFrameTransitionValue]
    simp only [hValid, ↓reduceIte, openAdjointTransitionCLM]
    exact (normalFrameAdjointTransition_eq_canonical
      (first.frame base) (second.frame base) (hRange base hValid)).symm
  inverse_contDiffOn := by
    apply (openAdjointTransitionCLM_contDiffOn second first).congr
    intro base hValid
    change
      (((openCanonicalFrameTransitionValue first second hRange base).symm).toContinuousLinearEquiv.toContinuousLinearMap) =
        openAdjointTransitionCLM second first base
    rw [openCanonicalFrameTransitionValue]
    simp only [hValid, ↓reduceIte, openAdjointTransitionCLM]
    calc
      ((normalFrameTransition (first.frame base) (second.frame base)
          (hRange base hValid)).symm).toContinuousLinearEquiv.toContinuousLinearMap =
        (normalFrameTransition (second.frame base) (first.frame base)
          (hRange base hValid).symm).toContinuousLinearEquiv.toContinuousLinearMap := by
            exact congrArg
              (fun transition : Model ≃ₗᵢ[ℝ] Model =>
                transition.toContinuousLinearEquiv.toContinuousLinearMap)
              (normalFrameTransition_reverse
                (first.frame base) (second.frame base)
                (hRange base hValid)).symm
      _ = normalFrameAdjointTransition
          (second.frame base) (first.frame base) :=
        (normalFrameAdjointTransition_eq_canonical
          (second.frame base) (first.frame base)
          (hRange base hValid).symm).symm

/-- On the valid domain, the canonical transition carries the first physical
frame to the second. -/
theorem openCanonicalFrameTransition_spec
    {domain : Set Base}
    (first second : SmoothIsometricFrameFamilyOn
      Base Model Ambient domain)
    (hRange : ∀ base, base ∈ domain →
      normalFrameRange (first.frame base) =
        normalFrameRange (second.frame base))
    (base : Base) (hValid : base ∈ domain) (vector : Model) :
    first.frame base
        ((openCanonicalFrameTransition first second hRange).frame base vector) =
      second.frame base vector := by
  change first.frame base
      (openCanonicalFrameTransitionValue first second hRange base vector) =
    second.frame base vector
  rw [openCanonicalFrameTransitionValue]
  simp only [hValid]
  exact normalFrameTransition_spec
    (first.frame base) (second.frame base) (hRange base hValid) vector

/-- Open-domain adapted tangent/normal frame pair. -/
structure OpenAdaptedFramePair
    (Base : Type w) (Tangent : Type u) (Normal : Type v)
    (AmbientTangent AmbientNormal : Type*)
    (domain : Set Base)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [NormedAddCommGroup AmbientTangent]
    [InnerProductSpace ℝ AmbientTangent]
    [NormedAddCommGroup AmbientNormal]
    [InnerProductSpace ℝ AmbientNormal] where
  referenceTangent : SmoothIsometricFrameFamilyOn
    Base Tangent AmbientTangent domain
  localTangent : SmoothIsometricFrameFamilyOn
    Base Tangent AmbientTangent domain
  tangentRange : ∀ base, base ∈ domain →
    normalFrameRange (referenceTangent.frame base) =
      normalFrameRange (localTangent.frame base)
  referenceNormal : SmoothIsometricFrameFamilyOn
    Base Normal AmbientNormal domain
  localNormal : SmoothIsometricFrameFamilyOn
    Base Normal AmbientNormal domain
  normalRange : ∀ base, base ∈ domain →
    normalFrameRange (referenceNormal.frame base) =
      normalFrameRange (localNormal.frame base)

/-- Canonical residual transition produced by an open adapted-frame pair. -/
def OpenAdaptedFramePair.residualTransition
    {Tangent : Type*} {Normal : Type*}
    {AmbientTangent AmbientNormal : Type*}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [NormedAddCommGroup AmbientTangent]
    [InnerProductSpace ℝ AmbientTangent]
    [NormedAddCommGroup AmbientNormal]
    [InnerProductSpace ℝ AmbientNormal]
    [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]
    [FiniteDimensional ℝ AmbientTangent]
    [FiniteDimensional ℝ AmbientNormal]
    {domain : Set Base}
    (frames : OpenAdaptedFramePair
      Base Tangent Normal AmbientTangent AmbientNormal domain) :
    SmoothResidualOrthogonalFrameFamilyOn
      Base Tangent Normal domain where
  tangent := openCanonicalFrameTransition
    frames.referenceTangent frames.localTangent frames.tangentRange
  normal := openCanonicalFrameTransition
    frames.referenceNormal frames.localNormal frames.normalRange

/-- Exact boundary after open canonical transitions. -/
structure OpenCanonicalTransitionStatus where
  openIsometricFramesPackaged : Prop
  adjointTransitionContDiffOnProved : Prop
  canonicalTransitionConstructed : Prop
  inverseTransitionContDiffOnProved : Prop
  frameTransitionSpecificationProved : Prop
  residualTangentNormalTransitionConstructed : Prop
  projectedSeedFramesInstantiated : Prop

/-- Closure of the open canonical transition stage. -/
def openCanonicalTransitionClosed
    (s : OpenCanonicalTransitionStatus) : Prop :=
  s.openIsometricFramesPackaged ∧
  s.adjointTransitionContDiffOnProved ∧
  s.canonicalTransitionConstructed ∧
  s.inverseTransitionContDiffOnProved ∧
  s.frameTransitionSpecificationProved ∧
  s.residualTangentNormalTransitionConstructed ∧
  s.projectedSeedFramesInstantiated

/-- The remaining step is packaging projected-seed Gram--Schmidt frames as
open-domain isometric frame families. -/
theorem missing_projected_seed_frames_blocks_open_transition_closure
    (s : OpenCanonicalTransitionStatus)
    (hMissing : Not s.projectedSeedFramesInstantiated) :
    Not (openCanonicalTransitionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorOpenCanonicalTransition
end JanusFormal
