import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorVariableOverlap

namespace JanusFormal
namespace P0EFTJanusRicciNormalResidualEquivariance

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusRicciNormalEquation
open P0EFTJanusRieszShapeOperator
open P0EFTJanusRieszShapeOperatorEquivariance

universe u v

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]

/-- Residual tangent/normal orthogonal action on a scalar normal-curvature
tensor. All four covariant inputs are pulled back by the inverse frames. -/
def actOnRealNormalCurvatureTensor
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (tensor : RealNormalCurvatureTensor Tangent Normal) :
    RealNormalCurvatureTensor Tangent Normal :=
  fun x y firstNormal secondNormal =>
    tensor (frame.1.symm x) (frame.1.symm y)
      (frame.2.symm firstNormal) (frame.2.symm secondNormal)

@[simp]
theorem actOnRealNormalCurvatureTensor_one
    (tensor : RealNormalCurvatureTensor Tangent Normal) :
    actOnRealNormalCurvatureTensor
        (1 : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
        tensor = tensor := by
  funext x y firstNormal secondNormal
  change tensor x y firstNormal secondNormal =
    tensor x y firstNormal secondNormal
  rfl

@[simp]
theorem actOnRealNormalCurvatureTensor_mul
    (first second :
      ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (tensor : RealNormalCurvatureTensor Tangent Normal) :
    actOnRealNormalCurvatureTensor (first * second) tensor =
      actOnRealNormalCurvatureTensor first
        (actOnRealNormalCurvatureTensor second tensor) := by
  funext x y firstNormal secondNormal
  simp [actOnRealNormalCurvatureTensor, LinearIsometryEquiv.mul_def]

/-- Residual orthogonal changes preserve the algebraic skew symmetries of normal
curvature. -/
def actOnAlgebraicNormalCurvatureTensor
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (tensor : AlgebraicNormalCurvatureTensor Tangent Normal) :
    AlgebraicNormalCurvatureTensor Tangent Normal where
  toFun := actOnRealNormalCurvatureTensor frame tensor.toFun
  skewTangent := by
    intro x y firstNormal secondNormal
    exact tensor.skewTangent
      (frame.1.symm x) (frame.1.symm y)
      (frame.2.symm firstNormal) (frame.2.symm secondNormal)
  skewNormal := by
    intro x y firstNormal secondNormal
    exact tensor.skewNormal
      (frame.1.symm x) (frame.1.symm y)
      (frame.2.symm firstNormal) (frame.2.symm secondNormal)

/-- Equivariance of the shape operator written for an arbitrary transformed
normal input rather than an input already displayed as `b xi`. -/
theorem rieszShapeOperator_residual_equivariant_symm_normal
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (normal : Normal) :
    rieszShapeOperator
        (actOnFiniteSecondFundamentalForm frame form) normal =
      conjugateShapeOperator frame.1
        (rieszShapeOperator form (frame.2.symm normal)) := by
  simpa using
    rieszShapeOperator_residual_equivariant form frame
      (frame.2.symm normal)

/-- The scalar shape-commutator term is a genuine residual covariant tensor. -/
theorem rieszRicciShapeCommutator_residual_equivariant
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    rieszRicciShapeCommutator
        (actOnFiniteSecondFundamentalForm frame form)
        x y firstNormal secondNormal =
      rieszRicciShapeCommutator form
        (frame.1.symm x) (frame.1.symm y)
        (frame.2.symm firstNormal) (frame.2.symm secondNormal) := by
  change
    ⟪rieszShapeOperator
          (actOnFiniteSecondFundamentalForm frame form) firstNormal
          (rieszShapeOperator
            (actOnFiniteSecondFundamentalForm frame form) secondNormal x),
        y⟫_ℝ -
      ⟪rieszShapeOperator
          (actOnFiniteSecondFundamentalForm frame form) secondNormal
          (rieszShapeOperator
            (actOnFiniteSecondFundamentalForm frame form) firstNormal x),
        y⟫_ℝ =
    ⟪rieszShapeOperator form (frame.2.symm firstNormal)
          (rieszShapeOperator form (frame.2.symm secondNormal)
            (frame.1.symm x)),
        frame.1.symm y⟫_ℝ -
      ⟪rieszShapeOperator form (frame.2.symm secondNormal)
          (rieszShapeOperator form (frame.2.symm firstNormal)
            (frame.1.symm x)),
        frame.1.symm y⟫_ℝ
  rw [rieszShapeOperator_residual_equivariant_symm_normal form frame firstNormal,
    rieszShapeOperator_residual_equivariant_symm_normal form frame secondNormal]
  simp only [conjugateShapeOperator_apply,
    frame.1.symm_apply_apply]
  rw [frame.1.inner_map_eq_flip, frame.1.inner_map_eq_flip]

/-- Riesz reconstruction of normal curvature commutes with residual orthogonal
changes of tangent and normal frames. -/
theorem rieszReconstructedNormalCurvature_residual_equivariant
    (ambientMixed : RealNormalCurvatureTensor Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal)) :
    rieszReconstructedNormalCurvature
        (actOnRealNormalCurvatureTensor frame ambientMixed)
        (actOnFiniteSecondFundamentalForm frame form) =
      actOnRealNormalCurvatureTensor frame
        (rieszReconstructedNormalCurvature ambientMixed form) := by
  funext x y firstNormal secondNormal
  change
    ambientMixed (frame.1.symm x) (frame.1.symm y)
        (frame.2.symm firstNormal) (frame.2.symm secondNormal) +
      rieszRicciShapeCommutator
        (actOnFiniteSecondFundamentalForm frame form)
        x y firstNormal secondNormal =
    ambientMixed (frame.1.symm x) (frame.1.symm y)
        (frame.2.symm firstNormal) (frame.2.symm secondNormal) +
      rieszRicciShapeCommutator form
        (frame.1.symm x) (frame.1.symm y)
        (frame.2.symm firstNormal) (frame.2.symm secondNormal)
  rw [rieszRicciShapeCommutator_residual_equivariant]

/-- The pointwise Ricci normal equation is invariant under residual orthogonal
frame changes. -/
theorem satisfiesRicciNormalEquation_residual_equivariant
    (normalCurvature ambientMixed :
      RealNormalCurvatureTensor Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (frame : ResidualOrthogonalFrame (Tangent := Tangent) (Normal := Normal))
    (hRicci : SatisfiesRicciNormalEquation normalCurvature ambientMixed
      (rieszShapeOperatorData form)) :
    SatisfiesRicciNormalEquation
      (actOnRealNormalCurvatureTensor frame normalCurvature)
      (actOnRealNormalCurvatureTensor frame ambientMixed)
      (rieszShapeOperatorData
        (actOnFiniteSecondFundamentalForm frame form)) := by
  intro x y firstNormal secondNormal
  change
    normalCurvature (frame.1.symm x) (frame.1.symm y)
        (frame.2.symm firstNormal) (frame.2.symm secondNormal) =
      ambientMixed (frame.1.symm x) (frame.1.symm y)
          (frame.2.symm firstNormal) (frame.2.symm secondNormal) +
        rieszRicciShapeCommutator
          (actOnFiniteSecondFundamentalForm frame form)
          x y firstNormal secondNormal
  rw [rieszRicciShapeCommutator_residual_equivariant]
  exact hRicci (frame.1.symm x) (frame.1.symm y)
    (frame.2.symm firstNormal) (frame.2.symm secondNormal)

/-- Exact boundary after proving residual covariance of the complete pointwise
Ricci-normal identity. -/
structure RicciResidualEquivarianceStatus where
  residualActionOnNormalCurvatureDefined : Prop
  residualActionLawsProved : Prop
  algebraicCurvatureSymmetriesPreserved : Prop
  rieszShapeCommutatorEquivarianceProved : Prop
  reconstructedCurvatureEquivarianceProved : Prop
  ricciEquationEquivarianceProved : Prop
  smoothVariableOverlapVersionProved : Prop
  geometricAmbientAndNormalCurvaturesInserted : Prop

/-- Closure of the residual-equivariant Ricci stage. -/
def ricciResidualEquivarianceClosed
    (s : RicciResidualEquivarianceStatus) : Prop :=
  s.residualActionOnNormalCurvatureDefined ∧
  s.residualActionLawsProved ∧
  s.algebraicCurvatureSymmetriesPreserved ∧
  s.rieszShapeCommutatorEquivarianceProved ∧
  s.reconstructedCurvatureEquivarianceProved ∧
  s.ricciEquationEquivarianceProved ∧
  s.smoothVariableOverlapVersionProved ∧
  s.geometricAmbientAndNormalCurvaturesInserted

/-- Pointwise residual covariance is not yet the smooth overlap theorem for the
actual ambient and normal curvature bundle sections. -/
theorem missing_smooth_overlap_blocks_geometric_ricci_descent
    (s : RicciResidualEquivarianceStatus)
    (hMissing : Not s.smoothVariableOverlapVersionProved) :
    Not (ricciResidualEquivarianceClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.1

end

end P0EFTJanusRicciNormalResidualEquivariance
end JanusFormal
