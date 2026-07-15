import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameSmoothTransition
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorVariableOverlapInstantiation

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorCanonicalFrameBridge

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusNormalFrameSmoothTransition
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorMovingFrame
open P0EFTJanusRieszShapeOperatorVariableOverlap
open P0EFTJanusRieszShapeOperatorVariableOverlapInstantiation

universe u v w x

variable {Base : Type w} {Tangent : Type u} {Normal : Type v}
variable {AmbientTangent AmbientNormal : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup AmbientTangent] [InnerProductSpace ℝ AmbientTangent]
variable [NormedAddCommGroup AmbientNormal] [InnerProductSpace ℝ AmbientNormal]
variable [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ AmbientTangent]
variable [FiniteDimensional ℝ AmbientNormal]

structure AdaptedFramePair where
  referenceTangent : SmoothIsometricNormalFrameFamily Base Tangent AmbientTangent
  localTangent : SmoothIsometricNormalFrameFamily Base Tangent AmbientTangent
  tangentRange : ∀ base,
    normalFrameRange (referenceTangent.frame base) =
      normalFrameRange (localTangent.frame base)
  referenceNormal : SmoothIsometricNormalFrameFamily Base Normal AmbientNormal
  localNormal : SmoothIsometricNormalFrameFamily Base Normal AmbientNormal
  normalRange : ∀ base,
    normalFrameRange (referenceNormal.frame base) =
      normalFrameRange (localNormal.frame base)

def AdaptedFramePair.tangentTransition
    (frames : AdaptedFramePair
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (AmbientTangent := AmbientTangent) (AmbientNormal := AmbientNormal)) :
    SmoothOrthogonalFrameFamily Base Tangent :=
  smoothCanonicalNormalFrameTransition
    frames.referenceTangent frames.localTangent frames.tangentRange

def AdaptedFramePair.normalTransition
    (frames : AdaptedFramePair
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (AmbientTangent := AmbientTangent) (AmbientNormal := AmbientNormal)) :
    SmoothOrthogonalFrameFamily Base Normal :=
  smoothCanonicalNormalFrameTransition
    frames.referenceNormal frames.localNormal frames.normalRange

def AdaptedFramePair.residualTransition
    (frames : AdaptedFramePair
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (AmbientTangent := AmbientTangent) (AmbientNormal := AmbientNormal)) :
    SmoothResidualOrthogonalFrameFamily Base Tangent Normal where
  tangent := frames.tangentTransition
  normal := frames.normalTransition

theorem AdaptedFramePair.tangentTransition_spec
    (frames : AdaptedFramePair
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (AmbientTangent := AmbientTangent) (AmbientNormal := AmbientNormal))
    (base : Base) (vector : Tangent) :
    frames.referenceTangent.frame base
      ((frames.tangentTransition).frame base vector) =
      frames.localTangent.frame base vector := by
  exact smoothCanonicalNormalFrameTransition_spec
    frames.referenceTangent frames.localTangent frames.tangentRange base vector

theorem AdaptedFramePair.normalTransition_spec
    (frames : AdaptedFramePair
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (AmbientTangent := AmbientTangent) (AmbientNormal := AmbientNormal))
    (base : Base) (vector : Normal) :
    frames.referenceNormal.frame base
      ((frames.normalTransition).frame base vector) =
      frames.localNormal.frame base vector := by
  exact smoothCanonicalNormalFrameTransition_spec
    frames.referenceNormal frames.localNormal frames.normalRange base vector

structure AdaptedFrameAtlas (Chart : Type*) where
  frames : Chart → AdaptedFramePair
    (Base := Base) (Tangent := Tangent) (Normal := Normal)
    (AmbientTangent := AmbientTangent) (AmbientNormal := AmbientNormal)

def AdaptedFrameAtlas.transition
    {Chart : Type*}
    (atlas : AdaptedFrameAtlas
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (AmbientTangent := AmbientTangent) (AmbientNormal := AmbientNormal) Chart)
    (chart : Chart) :
    SmoothResidualOrthogonalFrameFamily Base Tangent Normal :=
  (atlas.frames chart).residualTransition

def variableOverlapChartsOfAdaptedFrameAtlas
    {Chart : Type*}
    (atlas : AdaptedFrameAtlas
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (AmbientTangent := AmbientTangent) (AmbientNormal := AmbientNormal) Chart)
    (referenceTangentFrame : SmoothOrthogonalFrameFamily Base Tangent)
    (referenceNormalFrame : SmoothOrthogonalFrameFamily Base Normal)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (physicalNormal : Base → Normal)
    (hForm : ContDiff ℝ ∞ form)
    (hPhysicalNormal : ContDiff ℝ ∞ physicalNormal) :
    VariableOverlapRieszCharts
      (JetBase := Base) (Tangent := Tangent) (Normal := Normal) Chart where
  referenceTangentFrame := referenceTangentFrame
  referenceNormalFrame := referenceNormalFrame
  transition := atlas.transition
  form := form
  physicalNormal := physicalNormal
  form_contDiff := hForm
  physicalNormal_contDiff := hPhysicalNormal

theorem adaptedFrameAtlas_closes_riesz_obligations
    {Chart : Type*}
    (atlas : AdaptedFrameAtlas
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (AmbientTangent := AmbientTangent) (AmbientNormal := AmbientNormal) Chart)
    (referenceTangentFrame : SmoothOrthogonalFrameFamily Base Tangent)
    (referenceNormalFrame : SmoothOrthogonalFrameFamily Base Normal)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (physicalNormal : Base → Normal)
    (hForm : ContDiff ℝ ∞ form)
    (hPhysicalNormal : ContDiff ℝ ∞ physicalNormal) :
    let charts : VariableOverlapRieszCharts
        (JetBase := Base) (Tangent := Tangent) (Normal := Normal) Chart :=
      variableOverlapChartsOfAdaptedFrameAtlas atlas
        referenceTangentFrame referenceNormalFrame form physicalNormal
        hForm hPhysicalNormal
    (∀ chart, charts.localRiesz chart = charts.physicalRiesz) ∧
      (∀ chart, ContDiff ℝ ∞ (charts.localRiesz chart)) := by
  exact variableOverlap_closes_final_obligations
    (variableOverlapChartsOfAdaptedFrameAtlas atlas
      referenceTangentFrame referenceNormalFrame form physicalNormal
      hForm hPhysicalNormal)

structure CanonicalFrameBridgeStatus where
  smoothReferenceFramesSupplied : Prop
  smoothLocalFramesSupplied : Prop
  commonTangentRangesProved : Prop
  commonNormalRangesProved : Prop
  canonicalTangentTransitionsConstructed : Prop
  canonicalNormalTransitionsConstructed : Prop
  residualTransitionFamiliesConstructed : Prop
  localRieszObligationsDerived : Prop
  connectedToProjectedSeedGramSchmidtFrames : Prop

def canonicalFrameBridgeClosed (s : CanonicalFrameBridgeStatus) : Prop :=
  s.smoothReferenceFramesSupplied ∧
  s.smoothLocalFramesSupplied ∧
  s.commonTangentRangesProved ∧
  s.commonNormalRangesProved ∧
  s.canonicalTangentTransitionsConstructed ∧
  s.canonicalNormalTransitionsConstructed ∧
  s.residualTransitionFamiliesConstructed ∧
  s.localRieszObligationsDerived ∧
  s.connectedToProjectedSeedGramSchmidtFrames

theorem missing_gramSchmidt_frame_connection_blocks_closure
    (s : CanonicalFrameBridgeStatus)
    (hMissing : Not s.connectedToProjectedSeedGramSchmidtFrames) :
    Not (canonicalFrameBridgeClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorCanonicalFrameBridge
end JanusFormal
