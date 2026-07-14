import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorVariableOverlap

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorOpenMovingFrame

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorEquivariance
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorMovingFrame

universe u v w

/-- Orthogonal frame family whose forward and inverse operator maps are smooth
only on one chart domain. -/
structure SmoothOrthogonalFrameFamilyOn
    (Base : Type w) (Fiber : Type u) (domain : Set Base)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber] where
  frame : Base → Fiber ≃ₗᵢ[ℝ] Fiber
  forward_contDiffOn : ContDiffOn ℝ ∞
    (fun base => (frame base).toContinuousLinearEquiv.toContinuousLinearMap)
    domain
  inverse_contDiffOn : ContDiffOn ℝ ∞
    (fun base => (frame base).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    domain

variable {Base : Type w} {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]

/-- Coordinates of a vector field in an orthogonal frame, restricted to one open
chart domain. -/
def movingFrameCoordinatesOn
    {domain : Set Base}
    (family : SmoothOrthogonalFrameFamilyOn Base Normal domain)
    (vector : Base → Normal) : Base → Normal :=
  fun base => (family.frame base).symm (vector base)

/-- Chartwise smooth vectors have chartwise smooth moving-frame coordinates. -/
theorem movingFrameCoordinatesOn_contDiffOn
    {domain : Set Base}
    (family : SmoothOrthogonalFrameFamilyOn Base Normal domain)
    (vector : Base → Normal)
    (hVector : ContDiffOn ℝ ∞ vector domain) :
    ContDiffOn ℝ ∞ (movingFrameCoordinatesOn family vector) domain := by
  exact family.inverse_contDiffOn.clm_apply hVector

/-- Conjugation of a chartwise operator family by an open-domain tangent frame. -/
def conjugatedOperatorFamilyOn
    {domain : Set Base}
    (family : SmoothOrthogonalFrameFamilyOn Base Tangent domain)
    (operator : Base → Tangent →L[ℝ] Tangent) :
    Base → Tangent →L[ℝ] Tangent :=
  fun base => conjugateShapeOperator (family.frame base) (operator base)

/-- Open-domain smoothness is preserved by tangent-frame conjugation. -/
theorem conjugatedOperatorFamilyOn_contDiffOn
    {domain : Set Base}
    (family : SmoothOrthogonalFrameFamilyOn Base Tangent domain)
    (operator : Base → Tangent →L[ℝ] Tangent)
    (hOperator : ContDiffOn ℝ ∞ operator domain) :
    ContDiffOn ℝ ∞ (conjugatedOperatorFamilyOn family operator) domain := by
  change ContDiffOn ℝ ∞
    (fun base =>
      (family.frame base).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((operator base).comp
          (family.frame base).symm.toContinuousLinearEquiv.toContinuousLinearMap))
    domain
  exact family.forward_contDiffOn.clm_comp
    (hOperator.clm_comp family.inverse_contDiffOn)

/-- Fixed-model Riesz depends smoothly on `(II,xi)` on any chart domain. -/
theorem continuousIIRieszShape_family_contDiffOn
    [FiniteDimensional ℝ Normal]
    {domain : Set Base}
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Base → Normal)
    (hForm : ContDiffOn ℝ ∞ form domain)
    (hNormal : ContDiffOn ℝ ∞ normal domain) :
    ContDiffOn ℝ ∞
      (fun base => continuousIIRieszShapeOperator (form base) (normal base))
      domain := by
  change ContDiffOn ℝ ∞
    (fun base =>
      continuousIIRieszShapeContinuousBilinear
        (Tangent := Tangent) (Normal := Normal) (form base) (normal base))
    domain
  have hFirst : ContDiffOn ℝ ∞
      (fun base =>
        continuousIIRieszShapeContinuousBilinear
          (Tangent := Tangent) (Normal := Normal) (form base))
      domain := by
    exact contDiffOn_const.clm_apply hForm
  exact hFirst.clm_apply hNormal

/-- Riesz shape family written in one open moving tangent frame. -/
def framedRieszShapeFamilyOn
    {domain : Set Base}
    (tangentFrame : SmoothOrthogonalFrameFamilyOn Base Tangent domain)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normalCoordinates : Base → Normal) :
    Base → Tangent →L[ℝ] Tangent :=
  conjugatedOperatorFamilyOn tangentFrame
    (fun base => continuousIIRieszShapeOperator
      (form base) (normalCoordinates base))

/-- The local Riesz family is smooth on its open chart domain. -/
theorem framedRieszShapeFamilyOn_contDiffOn
    [FiniteDimensional ℝ Normal]
    {domain : Set Base}
    (tangentFrame : SmoothOrthogonalFrameFamilyOn Base Tangent domain)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normalCoordinates : Base → Normal)
    (hForm : ContDiffOn ℝ ∞ form domain)
    (hNormal : ContDiffOn ℝ ∞ normalCoordinates domain) :
    ContDiffOn ℝ ∞
      (framedRieszShapeFamilyOn tangentFrame form normalCoordinates) domain := by
  apply conjugatedOperatorFamilyOn_contDiffOn
  exact continuousIIRieszShape_family_contDiffOn form normalCoordinates
    hForm hNormal

/-- Physical Riesz family on one open chart. -/
def geometricRieszShapeFamilyOn
    [FiniteDimensional ℝ Normal]
    {domain : Set Base}
    (tangentFrame : SmoothOrthogonalFrameFamilyOn Base Tangent domain)
    (normalFrame : SmoothOrthogonalFrameFamilyOn Base Normal domain)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (physicalNormal : Base → Normal) :
    Base → Tangent →L[ℝ] Tangent :=
  framedRieszShapeFamilyOn tangentFrame form
    (movingFrameCoordinatesOn normalFrame physicalNormal)

/-- Smooth chart data gives a smooth physical Riesz expression on the chart. -/
theorem geometricRieszShapeFamilyOn_contDiffOn
    [FiniteDimensional ℝ Normal]
    {domain : Set Base}
    (tangentFrame : SmoothOrthogonalFrameFamilyOn Base Tangent domain)
    (normalFrame : SmoothOrthogonalFrameFamilyOn Base Normal domain)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (physicalNormal : Base → Normal)
    (hForm : ContDiffOn ℝ ∞ form domain)
    (hPhysicalNormal : ContDiffOn ℝ ∞ physicalNormal domain) :
    ContDiffOn ℝ ∞
      (geometricRieszShapeFamilyOn tangentFrame normalFrame form physicalNormal)
      domain := by
  apply framedRieszShapeFamilyOn_contDiffOn
  · exact hForm
  · exact movingFrameCoordinatesOn_contDiffOn normalFrame physicalNormal
      hPhysicalNormal

/-- Smooth residual tangent/normal coordinate change on one open chart. -/
structure SmoothResidualOrthogonalFrameFamilyOn
    (Base : Type w) (Tangent : Type u) (Normal : Type v)
    (domain : Set Base)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal] where
  tangent : SmoothOrthogonalFrameFamilyOn Base Tangent domain
  normal : SmoothOrthogonalFrameFamilyOn Base Normal domain

/-- Variable orthogonal reparametrization of an open-domain frame. -/
def reparametrizeSmoothOrthogonalFrameFamilyOn
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    {domain : Set Base}
    (family transition : SmoothOrthogonalFrameFamilyOn Base Fiber domain) :
    SmoothOrthogonalFrameFamilyOn Base Fiber domain where
  frame := fun base =>
    (transition.frame base).symm.trans (family.frame base)
  forward_contDiffOn := by
    change ContDiffOn ℝ ∞
      (fun base =>
        (family.frame base).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (transition.frame base).symm.toContinuousLinearEquiv.toContinuousLinearMap)
      domain
    exact family.forward_contDiffOn.clm_comp transition.inverse_contDiffOn
  inverse_contDiffOn := by
    change ContDiffOn ℝ ∞
      (fun base =>
        (transition.frame base).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (family.frame base).symm.toContinuousLinearEquiv.toContinuousLinearMap)
      domain
    exact transition.forward_contDiffOn.clm_comp family.inverse_contDiffOn

@[simp]
theorem reparametrizeSmoothOrthogonalFrameFamilyOn_apply
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    {domain : Set Base}
    (family transition : SmoothOrthogonalFrameFamilyOn Base Fiber domain)
    (base : Base) (vector : Fiber) :
    (reparametrizeSmoothOrthogonalFrameFamilyOn family transition).frame
        base vector =
      family.frame base ((transition.frame base).symm vector) := by
  rfl

@[simp]
theorem reparametrizeSmoothOrthogonalFrameFamilyOn_symm_apply
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    {domain : Set Base}
    (family transition : SmoothOrthogonalFrameFamilyOn Base Fiber domain)
    (base : Base) (vector : Fiber) :
    ((reparametrizeSmoothOrthogonalFrameFamilyOn family transition).frame
        base).symm vector =
      transition.frame base ((family.frame base).symm vector) := by
  rfl

/-- Moving coordinates transform pointwise by the open overlap gauge. -/
theorem movingFrameCoordinatesOn_variable_reparametrize
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    {domain : Set Base}
    (family transition : SmoothOrthogonalFrameFamilyOn Base Fiber domain)
    (vector : Base → Fiber) :
    movingFrameCoordinatesOn
        (reparametrizeSmoothOrthogonalFrameFamilyOn family transition)
        vector =
      fun base => transition.frame base
        (movingFrameCoordinatesOn family vector base) := by
  funext base
  rfl

/-- Pointwise residual transformation of `II` on an open overlap. -/
def transformContinuousIIOnOpenOverlap
    {domain : Set Base}
    (transition : SmoothResidualOrthogonalFrameFamilyOn
      Base Tangent Normal domain)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal)) :
    Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal) :=
  fun base => actOnContinuousSecondFundamentalForm
    (transition.tangent.frame base, transition.normal.frame base) (form base)

/-- The framed Riesz family is invariant under a simultaneous variable
orthogonal coordinate change on an open chart. -/
theorem framedRieszShapeFamilyOn_variable_coordinate_invariant
    [FiniteDimensional ℝ Normal]
    {domain : Set Base}
    (tangentFrame : SmoothOrthogonalFrameFamilyOn Base Tangent domain)
    (transition : SmoothResidualOrthogonalFrameFamilyOn
      Base Tangent Normal domain)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normalCoordinates : Base → Normal) :
    framedRieszShapeFamilyOn
        (reparametrizeSmoothOrthogonalFrameFamilyOn
          tangentFrame transition.tangent)
        (transformContinuousIIOnOpenOverlap transition form)
        (fun base => transition.normal.frame base (normalCoordinates base)) =
      framedRieszShapeFamilyOn tangentFrame form normalCoordinates := by
  funext base
  change
    conjugateShapeOperator
        ((transition.tangent.frame base).symm.trans
          (tangentFrame.frame base))
        (continuousIIRieszShapeOperator
          (actOnContinuousSecondFundamentalForm
            (transition.tangent.frame base, transition.normal.frame base)
            (form base))
          (transition.normal.frame base (normalCoordinates base))) =
      conjugateShapeOperator (tangentFrame.frame base)
        (continuousIIRieszShapeOperator (form base) (normalCoordinates base))
  rw [continuousIIRieszShapeOperator_residual_equivariant]
  apply ContinuousLinearMap.ext
  intro x
  simp [conjugateShapeOperator]

/-- The open-chart physical Riesz expression is invariant under a simultaneous
variable orthogonal coordinate change. -/
theorem geometricRieszShapeFamilyOn_variable_coordinate_invariant
    [FiniteDimensional ℝ Normal]
    {domain : Set Base}
    (tangentFrame : SmoothOrthogonalFrameFamilyOn Base Tangent domain)
    (normalFrame : SmoothOrthogonalFrameFamilyOn Base Normal domain)
    (transition : SmoothResidualOrthogonalFrameFamilyOn
      Base Tangent Normal domain)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (physicalNormal : Base → Normal) :
    geometricRieszShapeFamilyOn
        (reparametrizeSmoothOrthogonalFrameFamilyOn
          tangentFrame transition.tangent)
        (reparametrizeSmoothOrthogonalFrameFamilyOn
          normalFrame transition.normal)
        (transformContinuousIIOnOpenOverlap transition form)
        physicalNormal =
      geometricRieszShapeFamilyOn tangentFrame normalFrame form physicalNormal := by
  change
    framedRieszShapeFamilyOn
        (reparametrizeSmoothOrthogonalFrameFamilyOn
          tangentFrame transition.tangent)
        (transformContinuousIIOnOpenOverlap transition form)
        (movingFrameCoordinatesOn
          (reparametrizeSmoothOrthogonalFrameFamilyOn
            normalFrame transition.normal)
          physicalNormal) =
      framedRieszShapeFamilyOn tangentFrame form
        (movingFrameCoordinatesOn normalFrame physicalNormal)
  rw [movingFrameCoordinatesOn_variable_reparametrize]
  exact framedRieszShapeFamilyOn_variable_coordinate_invariant
    tangentFrame transition form
      (movingFrameCoordinatesOn normalFrame physicalNormal)

/-- The reparametrized local expression is smooth on the open chart. -/
theorem geometricRieszShapeFamilyOn_variable_overlap_contDiffOn
    [FiniteDimensional ℝ Normal]
    {domain : Set Base}
    (tangentFrame : SmoothOrthogonalFrameFamilyOn Base Tangent domain)
    (normalFrame : SmoothOrthogonalFrameFamilyOn Base Normal domain)
    (transition : SmoothResidualOrthogonalFrameFamilyOn
      Base Tangent Normal domain)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (physicalNormal : Base → Normal)
    (hForm : ContDiffOn ℝ ∞ form domain)
    (hPhysicalNormal : ContDiffOn ℝ ∞ physicalNormal domain) :
    ContDiffOn ℝ ∞
      (geometricRieszShapeFamilyOn
        (reparametrizeSmoothOrthogonalFrameFamilyOn
          tangentFrame transition.tangent)
        (reparametrizeSmoothOrthogonalFrameFamilyOn
          normalFrame transition.normal)
        (transformContinuousIIOnOpenOverlap transition form)
        physicalNormal)
      domain := by
  rw [geometricRieszShapeFamilyOn_variable_coordinate_invariant]
  exact geometricRieszShapeFamilyOn_contDiffOn tangentFrame normalFrame form
    physicalNormal hForm hPhysicalNormal

/-- Exact boundary after open-domain moving-frame Riesz theory. -/
structure OpenMovingFrameStatus where
  openFrameFamiliesDefined : Prop
  movingCoordinatesContDiffOnProved : Prop
  conjugationContDiffOnProved : Prop
  fixedModelRieszContDiffOnProved : Prop
  geometricRieszContDiffOnProved : Prop
  variableOverlapInvarianceProved : Prop
  projectedSeedFramesPackaged : Prop

/-- Closure of the open moving-frame stage. -/
def openMovingFrameClosed (s : OpenMovingFrameStatus) : Prop :=
  s.openFrameFamiliesDefined ∧
  s.movingCoordinatesContDiffOnProved ∧
  s.conjugationContDiffOnProved ∧
  s.fixedModelRieszContDiffOnProved ∧
  s.geometricRieszContDiffOnProved ∧
  s.variableOverlapInvarianceProved ∧
  s.projectedSeedFramesPackaged

/-- The remaining step is packaging the projected-seed orthonormal families as
open-domain orthogonal frame maps. -/
theorem missing_projected_seed_packaging_blocks_open_moving_frame_closure
    (s : OpenMovingFrameStatus)
    (hMissing : Not s.projectedSeedFramesPackaged) :
    Not (openMovingFrameClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorOpenMovingFrame
end JanusFormal
