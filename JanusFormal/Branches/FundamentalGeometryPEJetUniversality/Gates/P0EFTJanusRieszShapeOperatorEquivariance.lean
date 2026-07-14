import Mathlib.Topology.Algebra.Module.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperator

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorEquivariance

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusRieszShapeOperator

universe u v

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]

/-- Two finite-dimensional second fundamental forms are equal when all of their
values agree. -/
@[ext]
theorem FiniteSecondFundamentalForm.ext
    (first second : FiniteSecondFundamentalForm Tangent Normal)
    (hValue : ∀ x y, first x y = second x y) :
    first = second := by
  cases first with
  | mk firstLinear firstSymmetric =>
      cases second with
      | mk secondLinear secondSymmetric =>
          congr
          ext x y
          exact hValue x y

/-- The Riesz shape operator is additive in its normal parameter. -/
theorem rieszShapeOperator_add
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (first second : Normal) :
    rieszShapeOperator form (first + second) =
      rieszShapeOperator form first + rieszShapeOperator form second := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  change
    ⟪rieszShapeOperator form (first + second) x, y⟫_ℝ =
      ⟪rieszShapeOperator form first x +
          rieszShapeOperator form second x, y⟫_ℝ
  rw [rieszShapeOperator_inner, inner_add_left,
    rieszShapeOperator_inner, rieszShapeOperator_inner,
    inner_add_right]

/-- The Riesz shape operator is homogeneous in its normal parameter. -/
theorem rieszShapeOperator_smul
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (scalar : ℝ) (normal : Normal) :
    rieszShapeOperator form (scalar • normal) =
      scalar • rieszShapeOperator form normal := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  change
    ⟪rieszShapeOperator form (scalar • normal) x, y⟫_ℝ =
      ⟪scalar • rieszShapeOperator form normal x, y⟫_ℝ
  rw [rieszShapeOperator_inner, inner_smul_left,
    rieszShapeOperator_inner, inner_smul_right]
  rfl

/-- The family `xi ↦ A_xi` bundled as a linear map into continuous tangent
endomorphisms. -/
def rieszShapeOperatorLinear
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    Normal →ₗ[ℝ] Tangent →L[ℝ] Tangent where
  toFun := rieszShapeOperator form
  map_add' := rieszShapeOperator_add form
  map_smul' := rieszShapeOperator_smul form

@[simp]
theorem rieszShapeOperatorLinear_apply
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (normal : Normal) :
    rieszShapeOperatorLinear form normal =
      rieszShapeOperator form normal := by
  rfl

/-- In finite normal dimension, the whole normal-parameter family is a
continuous linear map. -/
def rieszShapeOperatorContinuous
    [FiniteDimensional ℝ Normal]
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    Normal →L[ℝ] Tangent →L[ℝ] Tangent :=
  LinearMap.toContinuousLinearMap (rieszShapeOperatorLinear form)

@[simp]
theorem rieszShapeOperatorContinuous_apply
    [FiniteDimensional ℝ Normal]
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (normal : Normal) :
    rieszShapeOperatorContinuous form normal =
      rieszShapeOperator form normal := by
  rfl

/-- Residual tangent/normal orthogonal frame group. -/
abbrev ResidualOrthogonalFrame :=
  (Tangent ≃ₗᵢ[ℝ] Tangent) × (Normal ≃ₗᵢ[ℝ] Normal)

/-- Standard residual action on a bundled finite-dimensional second fundamental
form,

`((a,b) · II)(x,y) = b (II(a⁻¹x,a⁻¹y))`.
-/
def actOnFiniteSecondFundamentalForm
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    FiniteSecondFundamentalForm Tangent Normal where
  toLinear :=
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
  symmetric := by
    intro x y
    change
      frame.2 (form (frame.1.symm x) (frame.1.symm y)) =
        frame.2 (form (frame.1.symm y) (frame.1.symm x))
    exact congrArg frame.2 (form.symmetric _ _)

@[simp]
theorem actOnFiniteSecondFundamentalForm_apply
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (x y : Tangent) :
    actOnFiniteSecondFundamentalForm frame form x y =
      frame.2 (form (frame.1.symm x) (frame.1.symm y)) := by
  rfl

@[simp]
theorem actOnFiniteSecondFundamentalForm_one
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    actOnFiniteSecondFundamentalForm
        (1 : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
        form = form := by
  ext x y
  change form x y = form x y
  rfl

@[simp]
theorem actOnFiniteSecondFundamentalForm_mul
    (first second :
      ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    actOnFiniteSecondFundamentalForm (first * second) form =
      actOnFiniteSecondFundamentalForm first
        (actOnFiniteSecondFundamentalForm second form) := by
  ext x y
  simp [actOnFiniteSecondFundamentalForm,
    LinearIsometryEquiv.mul_def]

/-- Conjugation action of a tangent orthogonal frame on a continuous tangent
endomorphism. -/
def conjugateShapeOperator
    (frame : Tangent ≃ₗᵢ[ℝ] Tangent)
    (operator : Tangent →L[ℝ] Tangent) :
    Tangent →L[ℝ] Tangent :=
  frame.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (operator.comp
      frame.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem conjugateShapeOperator_apply
    (frame : Tangent ≃ₗᵢ[ℝ] Tangent)
    (operator : Tangent →L[ℝ] Tangent)
    (x : Tangent) :
    conjugateShapeOperator frame operator x =
      frame (operator (frame.symm x)) := by
  rfl

/-- Conjugation bundled as a linear map on continuous tangent endomorphisms. -/
def conjugateShapeOperatorLinear
    (frame : Tangent ≃ₗᵢ[ℝ] Tangent) :
    (Tangent →L[ℝ] Tangent) →ₗ[ℝ] (Tangent →L[ℝ] Tangent) where
  toFun := conjugateShapeOperator frame
  map_add' := by
    intro first second
    ext x
    simp [conjugateShapeOperator]
  map_smul' := by
    intro scalar operator
    ext x
    simp [conjugateShapeOperator]

/-- Since the tangent endomorphism space is finite-dimensional, conjugation is a
continuous linear operator on it. -/
def conjugateShapeOperatorContinuous
    (frame : Tangent ≃ₗᵢ[ℝ] Tangent) :
    (Tangent →L[ℝ] Tangent) →L[ℝ] (Tangent →L[ℝ] Tangent) :=
  LinearMap.toContinuousLinearMap (conjugateShapeOperatorLinear frame)

/-- Residual orthogonal equivariance of the Riesz construction:

`A^((a,b)·II)_(b xi) = a ∘ A^II_xi ∘ a⁻¹`.
-/
theorem rieszShapeOperator_residual_equivariant
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (normal : Normal) :
    rieszShapeOperator
        (actOnFiniteSecondFundamentalForm frame form)
        (frame.2 normal) =
      conjugateShapeOperator frame.1
        (rieszShapeOperator form normal) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [rieszShapeOperator_inner]
  change
    ⟪frame.2 (form (frame.1.symm x) (frame.1.symm y)),
        frame.2 normal⟫_ℝ =
      ⟪frame.1
          (rieszShapeOperator form normal (frame.1.symm x)), y⟫_ℝ
  rw [frame.2.inner_map_map, frame.1.inner_map_eq_flip,
    rieszShapeOperator_inner]

/-- Equivariance bundled at the linear-map level. -/
theorem rieszShapeOperatorLinear_residual_equivariant
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal)) :
    (rieszShapeOperatorLinear
        (actOnFiniteSecondFundamentalForm frame form)).comp
        frame.2.toLinearEquiv.toLinearMap =
      (conjugateShapeOperatorLinear frame.1).comp
        (rieszShapeOperatorLinear form) := by
  apply LinearMap.ext
  intro normal
  exact rieszShapeOperator_residual_equivariant form frame normal

/-- Equivariance of the continuous normal-parameter family. -/
theorem rieszShapeOperatorContinuous_residual_equivariant
    [FiniteDimensional ℝ Normal]
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal)) :
    (rieszShapeOperatorContinuous
        (actOnFiniteSecondFundamentalForm frame form)).comp
        frame.2.toContinuousLinearEquiv.toContinuousLinearMap =
      (conjugateShapeOperatorContinuous frame.1).comp
        (rieszShapeOperatorContinuous form) := by
  apply ContinuousLinearMap.ext
  intro normal
  exact rieszShapeOperator_residual_equivariant form frame normal

/-- Progress boundary after bundling and equivariance of the Riesz family. -/
structure RieszEquivarianceStatus where
  normalParameterLinearityBundled : Prop
  normalParameterContinuityProved : Prop
  residualActionOnBundledIIConstructed : Prop
  residualActionLawsProved : Prop
  tangentConjugationActionConstructed : Prop
  pointwiseRieszEquivarianceProved : Prop
  bundledLinearEquivarianceProved : Prop
  bundledContinuousEquivarianceProved : Prop
  smoothDependenceOnBackgroundJetsProved : Prop
  actualNormalConnectionCurvatureInserted : Prop

/-- Closure of the Riesz equivariance stage. -/
def rieszEquivarianceClosed (s : RieszEquivarianceStatus) : Prop :=
  s.normalParameterLinearityBundled /\
  s.normalParameterContinuityProved /\
  s.residualActionOnBundledIIConstructed /\
  s.residualActionLawsProved /\
  s.tangentConjugationActionConstructed /\
  s.pointwiseRieszEquivarianceProved /\
  s.bundledLinearEquivarianceProved /\
  s.bundledContinuousEquivarianceProved /\
  s.smoothDependenceOnBackgroundJetsProved /\
  s.actualNormalConnectionCurvatureInserted

/-- Linear/continuous equivariance does not itself prove smooth dependence on a
varying structured background jet. -/
theorem missing_smooth_background_dependence_blocks_riesz_equivariance
    (s : RieszEquivarianceStatus)
    (hMissing : Not s.smoothDependenceOnBackgroundJetsProved) :
    Not (rieszEquivarianceClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorEquivariance
end JanusFormal
