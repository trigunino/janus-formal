import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorMovingFrame

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorVariableOverlap

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorEquivariance
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorMovingFrame

universe u v w

/-- A smooth residual tangent/normal change of orthogonal coordinates on an
overlap. Each component stores smooth forward and inverse operator families. -/
structure SmoothResidualOrthogonalFrameFamily
    (Base : Type w) (Tangent : Type u) (Normal : Type v)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal] where
  tangent : SmoothOrthogonalFrameFamily Base Tangent
  normal : SmoothOrthogonalFrameFamily Base Normal

/-- Pointwise residual orthogonal frame represented by a smooth overlap family. -/
def residualFrameAt
    {Base : Type w} {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (transition : SmoothResidualOrthogonalFrameFamily Base Tangent Normal)
    (base : Base) :
    ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal) :=
  (transition.tangent.frame base, transition.normal.frame base)

/-- Reparametrize a smooth physical frame by a smooth variable orthogonal change
of local fiber coordinates. Pointwise the new physical frame is

`e' = e ∘ g⁻¹`.
-/
def reparametrizeSmoothOrthogonalFrameFamilyVariable
    {Base : Type w} {Fiber : Type u}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    (family transition : SmoothOrthogonalFrameFamily Base Fiber) :
    SmoothOrthogonalFrameFamily Base Fiber where
  frame := fun base =>
    (transition.frame base).symm.trans (family.frame base)
  forward_contDiff := by
    change ContDiff ℝ ∞
      (fun base =>
        (family.frame base).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (transition.frame base).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    exact family.forward_contDiff.clm_comp transition.inverse_contDiff
  inverse_contDiff := by
    change ContDiff ℝ ∞
      (fun base =>
        (transition.frame base).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (family.frame base).symm.toContinuousLinearEquiv.toContinuousLinearMap)
    exact transition.forward_contDiff.clm_comp family.inverse_contDiff

@[simp]
theorem reparametrizeSmoothOrthogonalFrameFamilyVariable_apply
    {Base : Type w} {Fiber : Type u}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    (family transition : SmoothOrthogonalFrameFamily Base Fiber)
    (base : Base) (vector : Fiber) :
    (reparametrizeSmoothOrthogonalFrameFamilyVariable family transition).frame
        base vector =
      family.frame base ((transition.frame base).symm vector) := by
  rfl

@[simp]
theorem reparametrizeSmoothOrthogonalFrameFamilyVariable_symm_apply
    {Base : Type w} {Fiber : Type u}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    (family transition : SmoothOrthogonalFrameFamily Base Fiber)
    (base : Base) (vector : Fiber) :
    ((reparametrizeSmoothOrthogonalFrameFamilyVariable family transition).frame
        base).symm vector =
      transition.frame base ((family.frame base).symm vector) := by
  rfl

/-- Moving coordinates transform pointwise by the variable overlap gauge. -/
theorem movingFrameCoordinates_variable_reparametrize
    {Base : Type w} {Fiber : Type u}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    (family transition : SmoothOrthogonalFrameFamily Base Fiber)
    (vector : Base → Fiber) :
    movingFrameCoordinates
        (reparametrizeSmoothOrthogonalFrameFamilyVariable family transition)
        vector =
      fun base => transition.frame base
        (movingFrameCoordinates family vector base) := by
  funext base
  rfl

/-- Pointwise variable-overlap transformation of the continuous second
fundamental form. -/
def transformContinuousIIOnOverlap
    {Base : Type w} {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (transition : SmoothResidualOrthogonalFrameFamily Base Tangent Normal)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal)) :
    Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal) :=
  fun base => actOnContinuousSecondFundamentalForm
    (residualFrameAt transition base) (form base)

/-- The physical Riesz shape-operator family is independent of a smooth variable
simultaneous change of tangent and normal orthogonal coordinates.

This closes the overlap issue left open by the constant-coordinate theorem: no
derivatives of the transition enter because the shape operator is a tensorial
pointwise construction from `II` and a normal vector. -/
theorem framedRieszShapeFamily_variable_coordinate_invariant
    {Base : Type w} {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]
    (tangentFrame : SmoothOrthogonalFrameFamily Base Tangent)
    (transition : SmoothResidualOrthogonalFrameFamily Base Tangent Normal)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normalCoordinates : Base → Normal) :
    framedRieszShapeFamily
        (reparametrizeSmoothOrthogonalFrameFamilyVariable
          tangentFrame transition.tangent)
        (transformContinuousIIOnOverlap transition form)
        (fun base => transition.normal.frame base (normalCoordinates base)) =
      framedRieszShapeFamily tangentFrame form normalCoordinates := by
  funext base
  change
    conjugateShapeOperator
        (((transition.tangent.frame base).symm).trans
          (tangentFrame.frame base))
        (continuousIIRieszShapeOperator
          (actOnContinuousSecondFundamentalForm
            (residualFrameAt transition base) (form base))
          (transition.normal.frame base (normalCoordinates base))) =
      conjugateShapeOperator (tangentFrame.frame base)
        (continuousIIRieszShapeOperator (form base) (normalCoordinates base))
  rw [continuousIIRieszShapeOperator_residual_equivariant]
  apply ContinuousLinearMap.ext
  intro x
  simp [residualFrameAt, conjugateShapeOperator]

/-- The chart-independent geometric family is unchanged when both tangent and
normal local frames are reparametrized by a smooth variable overlap gauge. -/
theorem geometricRieszShapeFamily_variable_coordinate_invariant
    {Base : Type w} {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]
    (tangentFrame : SmoothOrthogonalFrameFamily Base Tangent)
    (normalFrame : SmoothOrthogonalFrameFamily Base Normal)
    (transition : SmoothResidualOrthogonalFrameFamily Base Tangent Normal)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (physicalNormal : Base → Normal) :
    geometricRieszShapeFamily
        (reparametrizeSmoothOrthogonalFrameFamilyVariable
          tangentFrame transition.tangent)
        (reparametrizeSmoothOrthogonalFrameFamilyVariable
          normalFrame transition.normal)
        (transformContinuousIIOnOverlap transition form)
        physicalNormal =
      geometricRieszShapeFamily tangentFrame normalFrame form physicalNormal := by
  change
    framedRieszShapeFamily
        (reparametrizeSmoothOrthogonalFrameFamilyVariable
          tangentFrame transition.tangent)
        (transformContinuousIIOnOverlap transition form)
        (movingFrameCoordinates
          (reparametrizeSmoothOrthogonalFrameFamilyVariable
            normalFrame transition.normal)
          physicalNormal) =
      framedRieszShapeFamily tangentFrame form
        (movingFrameCoordinates normalFrame physicalNormal)
  rw [movingFrameCoordinates_variable_reparametrize]
  exact framedRieszShapeFamily_variable_coordinate_invariant
    tangentFrame transition form
      (movingFrameCoordinates normalFrame physicalNormal)

/-- Smoothness of the geometric Riesz family descends across a smooth variable
overlap: the reparametrized expression is equal to the original smooth physical
operator family. -/
theorem geometricRieszShapeFamily_variable_overlap_contDiff
    {Base : Type w} {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]
    (tangentFrame : SmoothOrthogonalFrameFamily Base Tangent)
    (normalFrame : SmoothOrthogonalFrameFamily Base Normal)
    (transition : SmoothResidualOrthogonalFrameFamily Base Tangent Normal)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (physicalNormal : Base → Normal)
    (hForm : ContDiff ℝ ∞ form)
    (hPhysicalNormal : ContDiff ℝ ∞ physicalNormal) :
    ContDiff ℝ ∞
      (geometricRieszShapeFamily
        (reparametrizeSmoothOrthogonalFrameFamilyVariable
          tangentFrame transition.tangent)
        (reparametrizeSmoothOrthogonalFrameFamilyVariable
          normalFrame transition.normal)
        (transformContinuousIIOnOverlap transition form)
        physicalNormal) := by
  rw [geometricRieszShapeFamily_variable_coordinate_invariant]
  exact geometricRieszShapeFamily_contDiff tangentFrame normalFrame form
    physicalNormal hForm hPhysicalNormal

/-- Exact boundary after variable-overlap descent of the Riesz construction. -/
structure RieszVariableOverlapStatus where
  smoothResidualOverlapFamilyDefined : Prop
  variableFrameReparametrizationConstructed : Prop
  movingCoordinatesGaugeLawProved : Prop
  variablePointwiseRieszInvarianceProved : Prop
  geometricFamilyOverlapIndependenceProved : Prop
  smoothnessDescendsAcrossOverlap : Prop
  varyingMetricTrivializationConstructed : Prop
  structuredJetBundleMapConstructed : Prop

/-- Closure of the local-to-bundle Riesz overlap stage. -/
def rieszVariableOverlapClosed (s : RieszVariableOverlapStatus) : Prop :=
  s.smoothResidualOverlapFamilyDefined ∧
  s.variableFrameReparametrizationConstructed ∧
  s.movingCoordinatesGaugeLawProved ∧
  s.variablePointwiseRieszInvarianceProved ∧
  s.geometricFamilyOverlapIndependenceProved ∧
  s.smoothnessDescendsAcrossOverlap ∧
  s.varyingMetricTrivializationConstructed ∧
  s.structuredJetBundleMapConstructed

/-- Variable overlap descent still does not identify a single fixed model for a
family of varying tangent/normal inner products and subspaces. -/
theorem missing_varying_metric_trivialization_blocks_bundle_map
    (s : RieszVariableOverlapStatus)
    (hMissing : Not s.varyingMetricTrivializationConstructed) :
    Not (rieszVariableOverlapClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorVariableOverlap
end JanusFormal
