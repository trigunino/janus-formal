import Mathlib.Analysis.InnerProductSpace.LinearMap
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusGaussCodazziBianchiIdentities

namespace JanusFormal
namespace P0EFTJanusRicciNormalEquation

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusSecondFundamentalFormJet
open P0EFTJanusGaussCodazziBianchiIdentities

universe u v

/-- A second fundamental form together with its family of shape operators. The
adjoint relation is the pointwise Weingarten identity

`<A_ξ x, y> = <II(x,y), ξ>`.
-/
structure ShapeOperatorData
    (Tangent : Type u) (Normal : Type v)
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal] where
  secondFundamental : Tangent → Tangent → Normal
  secondFundamental_symmetric : IsSymmetricTensor secondFundamental
  shape : Normal → Tangent → Tangent
  adjoint_relation : ∀ normal x y,
    ⟪shape normal x, y⟫_ℝ =
      ⟪secondFundamental x y, normal⟫_ℝ

/-- Every shape operator is self-adjoint. -/
theorem shape_self_adjoint
    {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (data : ShapeOperatorData Tangent Normal)
    (normal : Normal) (x y : Tangent) :
    ⟪data.shape normal x, y⟫_ℝ =
      ⟪x, data.shape normal y⟫_ℝ := by
  calc
    ⟪data.shape normal x, y⟫_ℝ =
        ⟪data.secondFundamental x y, normal⟫_ℝ :=
      data.adjoint_relation normal x y
    _ = ⟪data.secondFundamental y x, normal⟫_ℝ := by
      rw [data.secondFundamental_symmetric x y]
    _ = ⟪data.shape normal y, x⟫_ℝ :=
      (data.adjoint_relation normal y x).symm
    _ = ⟪x, data.shape normal y⟫_ℝ :=
      real_inner_comm _ _

/-- Scalar commutator term in the Ricci equation,

`<[A_ξ,A_η]x,y>`

in the convention `A_ξ A_η - A_η A_ξ`. -/
def ricciShapeCommutator
    {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (data : ShapeOperatorData Tangent Normal) :
    Tangent → Tangent → Normal → Normal → ℝ :=
  fun x y firstNormal secondNormal =>
    ⟪data.shape firstNormal (data.shape secondNormal x), y⟫_ℝ -
      ⟪data.shape secondNormal (data.shape firstNormal x), y⟫_ℝ

/-- The shape-commutator contribution is skew in the two normal directions. -/
theorem ricciShapeCommutator_swap_normal
    {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (data : ShapeOperatorData Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    ricciShapeCommutator data x y secondNormal firstNormal =
      -ricciShapeCommutator data x y firstNormal secondNormal := by
  simp only [ricciShapeCommutator]
  ring

/-- A commutator of self-adjoint shape operators is skew-adjoint, hence the
Ricci contribution is skew in the tangent directions. -/
theorem ricciShapeCommutator_swap_tangent
    {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (data : ShapeOperatorData Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    ricciShapeCommutator data y x firstNormal secondNormal =
      -ricciShapeCommutator data x y firstNormal secondNormal := by
  simp only [ricciShapeCommutator]
  rw [shape_self_adjoint data firstNormal
      (data.shape secondNormal y) x,
    shape_self_adjoint data secondNormal
      (data.shape firstNormal y) x,
    shape_self_adjoint data firstNormal
      (data.shape secondNormal x) y,
    shape_self_adjoint data secondNormal
      (data.shape firstNormal x) y]
  rw [real_inner_comm (data.shape secondNormal y)
      (data.shape firstNormal x),
    real_inner_comm (data.shape firstNormal y)
      (data.shape secondNormal x)]
  ring

/-- Pointwise scalar normal-curvature tensor. -/
abbrev RealNormalCurvatureTensor (Tangent : Type u) (Normal : Type v) :=
  Tangent → Tangent → Normal → Normal → ℝ

/-- Algebraic symmetries required of the scalar normal-curvature tensor. -/
structure AlgebraicNormalCurvatureTensor
    (Tangent : Type u) (Normal : Type v) where
  toFun : RealNormalCurvatureTensor Tangent Normal
  skewTangent : ∀ x y firstNormal secondNormal,
    toFun y x firstNormal secondNormal =
      -toFun x y firstNormal secondNormal
  skewNormal : ∀ x y firstNormal secondNormal,
    toFun x y secondNormal firstNormal =
      -toFun x y firstNormal secondNormal

/-- The shape-commutator term itself is an algebraic normal-curvature tensor. -/
def ricciShapeAlgebraicCurvature
    {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (data : ShapeOperatorData Tangent Normal) :
    AlgebraicNormalCurvatureTensor Tangent Normal where
  toFun := ricciShapeCommutator data
  skewTangent := ricciShapeCommutator_swap_tangent data
  skewNormal := ricciShapeCommutator_swap_normal data

/-- Normal curvature reconstructed from the ambient mixed curvature and the
shape-operator commutator. -/
def ricciReconstructedNormalCurvature
    {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (ambientMixed : RealNormalCurvatureTensor Tangent Normal)
    (data : ShapeOperatorData Tangent Normal) :
    RealNormalCurvatureTensor Tangent Normal :=
  fun x y firstNormal secondNormal =>
    ambientMixed x y firstNormal secondNormal +
      ricciShapeCommutator data x y firstNormal secondNormal

/-- Pointwise Ricci equation. -/
def SatisfiesRicciNormalEquation
    {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (normalCurvature ambientMixed :
      RealNormalCurvatureTensor Tangent Normal)
    (data : ShapeOperatorData Tangent Normal) : Prop :=
  ∀ x y firstNormal secondNormal,
    normalCurvature x y firstNormal secondNormal =
      ambientMixed x y firstNormal secondNormal +
        ricciShapeCommutator data x y firstNormal secondNormal

/-- The reconstructed normal curvature satisfies the Ricci equation by
construction. -/
theorem ricciReconstructedNormalCurvature_satisfies
    {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (ambientMixed : RealNormalCurvatureTensor Tangent Normal)
    (data : ShapeOperatorData Tangent Normal) :
    SatisfiesRicciNormalEquation
      (ricciReconstructedNormalCurvature ambientMixed data)
      ambientMixed data := by
  intro x y firstNormal secondNormal
  rfl

/-- If the ambient mixed-curvature tensor has the two skew symmetries, then the
Ricci-reconstructed normal curvature has them as well. -/
def ricciReconstructedAlgebraicNormalCurvature
    {Tangent : Type u} {Normal : Type v}
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
    (ambientMixed : AlgebraicNormalCurvatureTensor Tangent Normal)
    (data : ShapeOperatorData Tangent Normal) :
    AlgebraicNormalCurvatureTensor Tangent Normal where
  toFun := ricciReconstructedNormalCurvature ambientMixed.toFun data
  skewTangent := by
    intro x y firstNormal secondNormal
    simp only [ricciReconstructedNormalCurvature]
    rw [ambientMixed.skewTangent,
      ricciShapeCommutator_swap_tangent]
    ring
  skewNormal := by
    intro x y firstNormal secondNormal
    simp only [ricciReconstructedNormalCurvature]
    rw [ambientMixed.skewNormal,
      ricciShapeCommutator_swap_normal]
    ring

/-- Exact boundary after the algebraic Ricci-normal equation. -/
structure RicciNormalEquationStatus where
  shapeOperatorDataDefined : Prop
  shapeSelfAdjointnessProved : Prop
  commutatorSkewTangentProved : Prop
  commutatorSkewNormalProved : Prop
  algebraicNormalCurvatureConstructed : Prop
  pointwiseRicciEquationDefined : Prop
  reconstructedRicciEquationProved : Prop
  finiteDimensionalRieszShapeOperatorsConstructed : Prop
  actualNormalConnectionCurvatureInserted : Prop
  actualAmbientMixedCurvatureInserted : Prop
  residualOrthogonalEquivarianceProved : Prop
  smoothJetBundleCompatibilityProved : Prop

/-- Closure of the geometric normal-Ricci stage. -/
def ricciNormalEquationClosed (s : RicciNormalEquationStatus) : Prop :=
  s.shapeOperatorDataDefined /\
  s.shapeSelfAdjointnessProved /\
  s.commutatorSkewTangentProved /\
  s.commutatorSkewNormalProved /\
  s.algebraicNormalCurvatureConstructed /\
  s.pointwiseRicciEquationDefined /\
  s.reconstructedRicciEquationProved /\
  s.finiteDimensionalRieszShapeOperatorsConstructed /\
  s.actualNormalConnectionCurvatureInserted /\
  s.actualAmbientMixedCurvatureInserted /\
  s.residualOrthogonalEquivarianceProved /\
  s.smoothJetBundleCompatibilityProved

/-- The algebraic Ricci identity does not insert the curvature of the genuine
normal connection of the Janus immersion. -/
theorem missing_normal_connection_blocks_geometric_ricci
    (s : RicciNormalEquationStatus)
    (hMissing : Not s.actualNormalConnectionCurvatureInserted) :
    Not (ricciNormalEquationClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusRicciNormalEquation
end JanusFormal
