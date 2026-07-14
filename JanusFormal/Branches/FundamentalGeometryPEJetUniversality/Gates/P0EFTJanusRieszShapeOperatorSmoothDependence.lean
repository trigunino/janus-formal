import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorEquivariance

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorSmoothDependence

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperator
open P0EFTJanusRieszShapeOperatorEquivariance

universe u v w

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]

/-- Fixed-model coefficient space for a continuous normal-valued bilinear form. -/
abbrev ContinuousSecondFundamentalForm :=
  Tangent →L[ℝ] Tangent →L[ℝ] Normal

/-- Pair a continuous normal-valued bilinear form with one normal vector. The
finite-dimensional tangent hypothesis supplies the required bilinear
continuity. -/
def continuousIIPairedBilinear
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Normal) :
    Tangent →L[ℝ] Tangent →L[ℝ] ℝ :=
  LinearMap.toContinuousBilinearMap
    { toFun := fun x =>
        (InnerProductSpace.toDualMap ℝ Normal normal).toLinearMap.comp
          (form x).toLinearMap
      map_add' := by
        intro first second
        ext y
        change
          ⟪normal, form (first + second) y⟫_ℝ =
            ⟪normal, form first y⟫_ℝ + ⟪normal, form second y⟫_ℝ
        rw [map_add, ContinuousLinearMap.add_apply, inner_add_right]
      map_smul' := by
        intro scalar x
        ext y
        simp }

@[simp]
theorem continuousIIPairedBilinear_apply
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Normal) (x y : Tangent) :
    continuousIIPairedBilinear form normal x y =
      ⟪normal, form x y⟫_ℝ := by
  rfl

/-- Riesz shape operator constructed directly from a continuous bilinear `II`. -/
def continuousIIRieszShapeOperator
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Normal) :
    Tangent →L[ℝ] Tangent :=
  InnerProductSpace.continuousLinearMapOfBilin
    (continuousIIPairedBilinear form normal)

/-- Weingarten relation for the continuous coefficient model. -/
theorem continuousIIRieszShapeOperator_inner
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Normal) (x y : Tangent) :
    ⟪continuousIIRieszShapeOperator form normal x, y⟫_ℝ =
      ⟪form x y, normal⟫_ℝ := by
  change
    ⟪InnerProductSpace.continuousLinearMapOfBilin
        (continuousIIPairedBilinear form normal) x, y⟫_ℝ =
      ⟪form x y, normal⟫_ℝ
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
  exact real_inner_comm _ _

/-- Additivity in the normal parameter. -/
theorem continuousIIRieszShapeOperator_add_normal
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (first second : Normal) :
    continuousIIRieszShapeOperator form (first + second) =
      continuousIIRieszShapeOperator form first +
        continuousIIRieszShapeOperator form second := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  change
    ⟪continuousIIRieszShapeOperator form (first + second) x, y⟫_ℝ =
      ⟪continuousIIRieszShapeOperator form first x +
          continuousIIRieszShapeOperator form second x, y⟫_ℝ
  rw [continuousIIRieszShapeOperator_inner, inner_add_left,
    continuousIIRieszShapeOperator_inner,
    continuousIIRieszShapeOperator_inner, inner_add_right]

/-- Homogeneity in the normal parameter. -/
theorem continuousIIRieszShapeOperator_smul_normal
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (scalar : ℝ) (normal : Normal) :
    continuousIIRieszShapeOperator form (scalar • normal) =
      scalar • continuousIIRieszShapeOperator form normal := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  change
    ⟪continuousIIRieszShapeOperator form (scalar • normal) x, y⟫_ℝ =
      ⟪scalar • continuousIIRieszShapeOperator form normal x, y⟫_ℝ
  rw [continuousIIRieszShapeOperator_inner, inner_smul_left,
    continuousIIRieszShapeOperator_inner, inner_smul_right]
  rfl

/-- Additivity in the second-fundamental-form coefficient. -/
theorem continuousIIRieszShapeOperator_add_form
    (first second : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Normal) :
    continuousIIRieszShapeOperator (first + second) normal =
      continuousIIRieszShapeOperator first normal +
        continuousIIRieszShapeOperator second normal := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  change
    ⟪continuousIIRieszShapeOperator (first + second) normal x, y⟫_ℝ =
      ⟪continuousIIRieszShapeOperator first normal x +
          continuousIIRieszShapeOperator second normal x, y⟫_ℝ
  rw [continuousIIRieszShapeOperator_inner, inner_add_left,
    continuousIIRieszShapeOperator_inner,
    continuousIIRieszShapeOperator_inner]
  change
    ⟪first x y + second x y, normal⟫_ℝ =
      ⟪first x y, normal⟫_ℝ + ⟪second x y, normal⟫_ℝ
  exact inner_add_left _ _ _

/-- Homogeneity in the second-fundamental-form coefficient. -/
theorem continuousIIRieszShapeOperator_smul_form
    (scalar : ℝ)
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Normal) :
    continuousIIRieszShapeOperator (scalar • form) normal =
      scalar • continuousIIRieszShapeOperator form normal := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  change
    ⟪continuousIIRieszShapeOperator (scalar • form) normal x, y⟫_ℝ =
      ⟪scalar • continuousIIRieszShapeOperator form normal x, y⟫_ℝ
  rw [continuousIIRieszShapeOperator_inner, inner_smul_left,
    continuousIIRieszShapeOperator_inner]
  change
    ⟪scalar • form x y, normal⟫_ℝ = scalar * ⟪form x y, normal⟫_ℝ
  exact inner_smul_left _ _ _

/-- The Riesz construction is bilinear in `(II,xi)` before adding joint
continuity. -/
def continuousIIRieszShapeBilinearLinear :
    ContinuousSecondFundamentalForm
        (Tangent := Tangent) (Normal := Normal) →ₗ[ℝ]
      Normal →ₗ[ℝ] Tangent →L[ℝ] Tangent where
  toFun := fun form =>
    { toFun := continuousIIRieszShapeOperator form
      map_add' := continuousIIRieszShapeOperator_add_normal form
      map_smul' := continuousIIRieszShapeOperator_smul_normal form }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro normal
    exact continuousIIRieszShapeOperator_add_form first second normal
  map_smul' := by
    intro scalar form
    apply LinearMap.ext
    intro normal
    exact continuousIIRieszShapeOperator_smul_form scalar form normal

/-- Jointly continuous bilinear Riesz construction on the fixed finite-dimensional
coefficient model. -/
def continuousIIRieszShapeContinuousBilinear
    [FiniteDimensional ℝ Normal] :
    ContinuousSecondFundamentalForm
        (Tangent := Tangent) (Normal := Normal) →L[ℝ]
      Normal →L[ℝ] Tangent →L[ℝ] Tangent :=
  LinearMap.toContinuousBilinearMap
    (continuousIIRieszShapeBilinearLinear
      (Tangent := Tangent) (Normal := Normal))

@[simp]
theorem continuousIIRieszShapeContinuousBilinear_apply
    [FiniteDimensional ℝ Normal]
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Normal) :
    continuousIIRieszShapeContinuousBilinear
        (Tangent := Tangent) (Normal := Normal) form normal =
      continuousIIRieszShapeOperator form normal := by
  rfl

/-- Joint smoothness of `(II,xi) ↦ A_xi` in a fixed finite-dimensional tangent
and normal model. -/
theorem continuousIIRieszShape_joint_contDiff
    [FiniteDimensional ℝ Normal] :
    ContDiff ℝ ∞
      (fun point :
          ContinuousSecondFundamentalForm
              (Tangent := Tangent) (Normal := Normal) × Normal =>
        continuousIIRieszShapeOperator point.1 point.2) := by
  change
    ContDiff ℝ ∞
      (fun point :
          ContinuousSecondFundamentalForm
              (Tangent := Tangent) (Normal := Normal) × Normal =>
        continuousIIRieszShapeContinuousBilinear
          (Tangent := Tangent) (Normal := Normal) point.1 point.2)
  fun_prop

/-- Smooth background families of coefficients and normal parameters produce a
smooth family of shape operators, as long as the tangent and normal models are
fixed. -/
theorem continuousIIRieszShape_family_contDiff
    [FiniteDimensional ℝ Normal]
    {Base : Type w}
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Base → Normal)
    (hForm : ContDiff ℝ ∞ form)
    (hNormal : ContDiff ℝ ∞ normal) :
    ContDiff ℝ ∞
      (fun base => continuousIIRieszShapeOperator (form base) (normal base)) := by
  change
    ContDiff ℝ ∞
      (fun base =>
        continuousIIRieszShapeContinuousBilinear
          (Tangent := Tangent) (Normal := Normal) (form base) (normal base))
  fun_prop

/-- Convert the earlier finite bilinear model to the continuous coefficient
space. -/
def continuousSecondFundamentalFormOfFinite
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal) :=
  LinearMap.toContinuousBilinearMap form.toLinear

@[simp]
theorem continuousSecondFundamentalFormOfFinite_apply
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (x y : Tangent) :
    continuousSecondFundamentalFormOfFinite form x y = form x y := by
  rfl

/-- Compatibility with the previous pointwise Riesz construction. -/
theorem continuousIIRieszShapeOperator_ofFinite
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (normal : Normal) :
    continuousIIRieszShapeOperator
        (continuousSecondFundamentalFormOfFinite form) normal =
      rieszShapeOperator form normal := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [continuousIIRieszShapeOperator_inner,
    rieszShapeOperator_inner]
  rfl

/-- Exact boundary of the fixed-model smooth-dependence result. -/
structure RieszSmoothDependenceStatus where
  continuousIICoefficientSpaceConstructed : Prop
  bilinearityInIIAndNormalProved : Prop
  jointContinuityProved : Prop
  jointSmoothnessProved : Prop
  smoothFixedModelFamiliesProved : Prop
  compatibilityWithFiniteIIModelProved : Prop
  varyingMetricDependenceProved : Prop
  varyingTangentNormalSubspacesHandled : Prop
  smoothStructuredJetBundleMapConstructed : Prop
  manifoldNormalConnectionInserted : Prop

/-- Closure of the genuine varying-background Riesz stage. -/
def rieszSmoothDependenceClosed (s : RieszSmoothDependenceStatus) : Prop :=
  s.continuousIICoefficientSpaceConstructed /\
  s.bilinearityInIIAndNormalProved /\
  s.jointContinuityProved /\
  s.jointSmoothnessProved /\
  s.smoothFixedModelFamiliesProved /\
  s.compatibilityWithFiniteIIModelProved /\
  s.varyingMetricDependenceProved /\
  s.varyingTangentNormalSubspacesHandled /\
  s.smoothStructuredJetBundleMapConstructed /\
  s.manifoldNormalConnectionInserted

/-- Fixed-model smoothness does not solve varying metric and subspace dependence
on the structured-jet base. -/
theorem missing_varying_subspaces_blocks_full_riesz_smoothness
    (s : RieszSmoothDependenceStatus)
    (hMissing : Not s.varyingTangentNormalSubspacesHandled) :
    Not (rieszSmoothDependenceClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorSmoothDependence
end JanusFormal
