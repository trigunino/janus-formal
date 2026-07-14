import Mathlib.Analysis.Calculus.ContDiff.Comp
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorSmoothDependence

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorMovingFrame

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperator
open P0EFTJanusRieszShapeOperatorEquivariance
open P0EFTJanusRieszShapeOperatorSmoothDependence

universe u v w

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]

/-- Residual tangent/normal orthogonal action on the continuous coefficient model
of the second fundamental form. -/
def actOnContinuousSecondFundamentalForm
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal)) :
    ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal) :=
  LinearMap.toContinuousBilinearMap
    { toFun := fun x =>
        { toFun := fun y =>
            frame.2 (form (frame.1.symm x) (frame.1.symm y))
          map_add' := by
            intro first second
            simp
          map_smul' := by
            intro scalar y
            simp }
      map_add' := by
        intro first second
        ext y
        simp
      map_smul' := by
        intro scalar x
        ext y
        simp }

@[simp]
theorem actOnContinuousSecondFundamentalForm_apply
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (x y : Tangent) :
    actOnContinuousSecondFundamentalForm frame form x y =
      frame.2 (form (frame.1.symm x) (frame.1.symm y)) := by
  rfl

@[simp]
theorem actOnContinuousSecondFundamentalForm_one
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal)) :
    actOnContinuousSecondFundamentalForm
        (1 : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
        form = form := by
  ext x y
  change form x y = form x y
  rfl

@[simp]
theorem actOnContinuousSecondFundamentalForm_mul
    (first second :
      ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal)) :
    actOnContinuousSecondFundamentalForm (first * second) form =
      actOnContinuousSecondFundamentalForm first
        (actOnContinuousSecondFundamentalForm second form) := by
  ext x y
  simp [actOnContinuousSecondFundamentalForm,
    LinearIsometryEquiv.mul_def]

/-- Residual equivariance of the Riesz construction on the continuous
second-fundamental-form coefficient model. -/
theorem continuousIIRieszShapeOperator_residual_equivariant
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (normal : Normal) :
    continuousIIRieszShapeOperator
        (actOnContinuousSecondFundamentalForm frame form)
        (frame.2 normal) =
      conjugateShapeOperator frame.1
        (continuousIIRieszShapeOperator form normal) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [continuousIIRieszShapeOperator_inner]
  change
    ⟪frame.2 (form (frame.1.symm x) (frame.1.symm y)),
        frame.2 normal⟫_ℝ =
      ⟪frame.1
          (continuousIIRieszShapeOperator form normal
            (frame.1.symm x)), y⟫_ℝ
  rw [frame.2.inner_map_map, frame.1.inner_map_eq_flip,
    continuousIIRieszShapeOperator_inner]

/-- A smooth family of orthogonal frames is represented by the frame itself,
together with smoothness of its forward and inverse continuous-linear maps.
This avoids requiring a manifold structure on the bundled orthogonal group. -/
structure SmoothOrthogonalFrameFamily
    (Base : Type w) (Fiber : Type u)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber] where
  frame : Base → Fiber ≃ₗᵢ[ℝ] Fiber
  forward_contDiff : ContDiff ℝ ∞
    (fun base => (frame base).toContinuousLinearEquiv.toContinuousLinearMap)
  inverse_contDiff : ContDiff ℝ ∞
    (fun base => (frame base).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Coordinates of a smooth physical vector field in a moving orthogonal frame. -/
def movingFrameCoordinates
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    (family : SmoothOrthogonalFrameFamily Base Fiber)
    (vector : Base → Fiber) : Base → Fiber :=
  fun base => (family.frame base).symm (vector base)

/-- Smooth vectors have smooth moving-frame coordinates when the inverse frame
map is smooth. -/
theorem movingFrameCoordinates_contDiff
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    (family : SmoothOrthogonalFrameFamily Base Fiber)
    (vector : Base → Fiber)
    (hVector : ContDiff ℝ ∞ vector) :
    ContDiff ℝ ∞ (movingFrameCoordinates family vector) := by
  exact family.inverse_contDiff.clm_apply hVector

/-- Conjugate a smooth family of tangent endomorphisms by a smooth orthogonal
frame family. -/
def conjugatedOperatorFamily
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (family : SmoothOrthogonalFrameFamily Base Tangent)
    (operator : Base → Tangent →L[ℝ] Tangent) :
    Base → Tangent →L[ℝ] Tangent :=
  fun base => conjugateShapeOperator (family.frame base) (operator base)

/-- Smoothness is preserved by moving-frame conjugation. -/
theorem conjugatedOperatorFamily_contDiff
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (family : SmoothOrthogonalFrameFamily Base Tangent)
    (operator : Base → Tangent →L[ℝ] Tangent)
    (hOperator : ContDiff ℝ ∞ operator) :
    ContDiff ℝ ∞ (conjugatedOperatorFamily family operator) := by
  change ContDiff ℝ ∞
    (fun base =>
      (family.frame base).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((operator base).comp
          (family.frame base).symm.toContinuousLinearEquiv.toContinuousLinearMap))
  exact family.forward_contDiff.clm_comp
    (hOperator.clm_comp family.inverse_contDiff)

/-- Shape-operator family written in a moving tangent frame while `II` and the
normal parameter are expressed in the corresponding local coordinates. -/
def framedRieszShapeFamily
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (tangentFrame : SmoothOrthogonalFrameFamily Base Tangent)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normalCoordinates : Base → Normal) :
    Base → Tangent →L[ℝ] Tangent :=
  conjugatedOperatorFamily tangentFrame
    (fun base => continuousIIRieszShapeOperator
      (form base) (normalCoordinates base))

/-- The Riesz family is smooth after conjugation by a smooth moving tangent
frame. -/
theorem framedRieszShapeFamily_contDiff
    [FiniteDimensional ℝ Normal]
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (tangentFrame : SmoothOrthogonalFrameFamily Base Tangent)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normalCoordinates : Base → Normal)
    (hForm : ContDiff ℝ ∞ form)
    (hNormal : ContDiff ℝ ∞ normalCoordinates) :
    ContDiff ℝ ∞
      (framedRieszShapeFamily tangentFrame form normalCoordinates) := by
  apply conjugatedOperatorFamily_contDiff
  exact continuousIIRieszShape_family_contDiff form normalCoordinates
    hForm hNormal

/-- Shape-operator family for a physical normal vector field. The normal frame
first converts that vector to local coordinates, and the tangent frame then
conjugates the local Riesz operator back to physical tangent coordinates. -/
def geometricRieszShapeFamily
    [FiniteDimensional ℝ Normal]
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (tangentFrame : SmoothOrthogonalFrameFamily Base Tangent)
    (normalFrame : SmoothOrthogonalFrameFamily Base Normal)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (physicalNormal : Base → Normal) :
    Base → Tangent →L[ℝ] Tangent :=
  framedRieszShapeFamily tangentFrame form
    (movingFrameCoordinates normalFrame physicalNormal)

/-- Local trivializations turn smooth geometric data into a smooth physical
shape-operator family. This is the precise fixed-rank bundle chart needed before
gluing over a structured-jet base. -/
theorem geometricRieszShapeFamily_contDiff
    [FiniteDimensional ℝ Normal]
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (tangentFrame : SmoothOrthogonalFrameFamily Base Tangent)
    (normalFrame : SmoothOrthogonalFrameFamily Base Normal)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (physicalNormal : Base → Normal)
    (hForm : ContDiff ℝ ∞ form)
    (hPhysicalNormal : ContDiff ℝ ∞ physicalNormal) :
    ContDiff ℝ ∞
      (geometricRieszShapeFamily tangentFrame normalFrame form physicalNormal) := by
  apply framedRieszShapeFamily_contDiff
  · exact hForm
  · exact movingFrameCoordinates_contDiff normalFrame physicalNormal
      hPhysicalNormal

/-- Reparametrize local fiber coordinates by a constant orthogonal map. The
physical frame is unchanged, so its coordinate map is precomposed by the inverse
change of coordinates. -/
def reparametrizeSmoothOrthogonalFrameFamily
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    (family : SmoothOrthogonalFrameFamily Base Fiber)
    (change : Fiber ≃ₗᵢ[ℝ] Fiber) :
    SmoothOrthogonalFrameFamily Base Fiber where
  frame := fun base => change.symm.trans (family.frame base)
  forward_contDiff := by
    change ContDiff ℝ ∞
      (fun base =>
        (family.frame base).toContinuousLinearEquiv.toContinuousLinearMap.comp
          change.symm.toContinuousLinearEquiv.toContinuousLinearMap)
    exact family.forward_contDiff.clm_comp contDiff_const
  inverse_contDiff := by
    change ContDiff ℝ ∞
      (fun base =>
        change.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (family.frame base).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    exact contDiff_const.clm_comp family.inverse_contDiff

/-- The physical Riesz family is independent of a constant simultaneous change
of tangent and normal orthogonal coordinates. -/
theorem framedRieszShapeFamily_constant_coordinate_invariant
    [FiniteDimensional ℝ Normal]
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (tangentFrame : SmoothOrthogonalFrameFamily Base Tangent)
    (change : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Base → Normal) :
    framedRieszShapeFamily
        (reparametrizeSmoothOrthogonalFrameFamily tangentFrame change.1)
        (fun base => actOnContinuousSecondFundamentalForm change (form base))
        (fun base => change.2 (normal base)) =
      framedRieszShapeFamily tangentFrame form normal := by
  funext base
  change
    conjugateShapeOperator
        ((change.1.symm).trans (tangentFrame.frame base))
        (continuousIIRieszShapeOperator
          (actOnContinuousSecondFundamentalForm change (form base))
          (change.2 (normal base))) =
      conjugateShapeOperator (tangentFrame.frame base)
        (continuousIIRieszShapeOperator (form base) (normal base))
  rw [continuousIIRieszShapeOperator_residual_equivariant]
  apply ContinuousLinearMap.ext
  intro x
  simp [conjugateShapeOperator]

/-- Exact boundary of the moving-frame smoothness stage. -/
structure RieszMovingFrameStatus where
  continuousIIResidualActionConstructed : Prop
  continuousIIResidualActionLawsProved : Prop
  continuousRieszEquivarianceProved : Prop
  smoothOrthogonalFrameFamilyDefined : Prop
  movingCoordinateSmoothnessProved : Prop
  conjugatedOperatorSmoothnessProved : Prop
  framedRieszSmoothnessProved : Prop
  physicalNormalFieldSmoothnessProved : Prop
  constantOverlapCoordinateIndependenceProved : Prop
  variableOverlapCoordinateIndependenceProved : Prop
  varyingMetricTrivializationConstructed : Prop
  structuredJetBundleMapConstructed : Prop

/-- Closure of the local-to-bundle Riesz stage. -/
def rieszMovingFrameClosed (s : RieszMovingFrameStatus) : Prop :=
  s.continuousIIResidualActionConstructed /\
  s.continuousIIResidualActionLawsProved /\
  s.continuousRieszEquivarianceProved /\
  s.smoothOrthogonalFrameFamilyDefined /\
  s.movingCoordinateSmoothnessProved /\
  s.conjugatedOperatorSmoothnessProved /\
  s.framedRieszSmoothnessProved /\
  s.physicalNormalFieldSmoothnessProved /\
  s.constantOverlapCoordinateIndependenceProved /\
  s.variableOverlapCoordinateIndependenceProved /\
  s.varyingMetricTrivializationConstructed /\
  s.structuredJetBundleMapConstructed

/-- Constant overlap invariance is not yet the full cocycle theorem for a varying
smooth transition function. -/
theorem missing_variable_overlap_blocks_riesz_bundle_map
    (s : RieszMovingFrameStatus)
    (hMissing : Not s.variableOverlapCoordinateIndependenceProved) :
    Not (rieszMovingFrameClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorMovingFrame
end JanusFormal
