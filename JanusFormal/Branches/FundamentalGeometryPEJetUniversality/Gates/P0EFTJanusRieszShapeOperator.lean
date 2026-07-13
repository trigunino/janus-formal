import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRicciNormalEquation

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperator

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusConcreteSecondJetChainRule
open P0EFTJanusRicciNormalEquation

universe u v

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]

/-- A finite-dimensional bilinear second fundamental form. Its linearity in both
arguments is bundled; symmetry is the geometric torsion-free condition. -/
structure FiniteSecondFundamentalForm
    (Tangent : Type u) (Normal : Type v)
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal] where
  toLinear : Tangent →ₗ[ℝ] Tangent →ₗ[ℝ] Normal
  symmetric : ∀ x y, toLinear x y = toLinear y x

instance : CoeFun (FiniteSecondFundamentalForm Tangent Normal)
    (fun _ => Tangent → Tangent → Normal) where
  coe form := fun x y => form.toLinear x y

/-- Pair a normal-valued bilinear form with one normal vector. The result is a
real bilinear form before adding continuity. -/
def pairedBilinearLinear
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (normal : Normal) :
    Tangent →ₗ[ℝ] Tangent →ₗ[ℝ] ℝ where
  toFun x :=
    (InnerProductSpace.toDualMap ℝ Normal normal).toLinearMap.comp
      (form.toLinear x)
  map_add' x y := by
    ext z
    simp
  map_smul' scalar x := by
    ext z
    simp

@[simp]
theorem pairedBilinearLinear_apply
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (normal : Normal) (x y : Tangent) :
    pairedBilinearLinear form normal x y =
      ⟪normal, form x y⟫_ℝ := by
  rfl

/-- In finite dimension every bilinear form is continuous. -/
def pairedContinuousBilinear
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (normal : Normal) :
    Tangent →L[ℝ] Tangent →L[ℝ] ℝ :=
  (pairedBilinearLinear form normal).toContinuousBilinearMap

@[simp]
theorem pairedContinuousBilinear_apply
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (normal : Normal) (x y : Tangent) :
    pairedContinuousBilinear form normal x y =
      ⟪normal, form x y⟫_ℝ := by
  rfl

/-- Shape operator obtained from `II` by Fréchet--Riesz representation. -/
def rieszShapeOperator
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (normal : Normal) :
    Tangent →L[ℝ] Tangent :=
  InnerProductSpace.continuousLinearMapOfBilin
    (pairedContinuousBilinear form normal)

/-- The Riesz-constructed shape operator satisfies the Weingarten adjoint
relation with the original second fundamental form. -/
theorem rieszShapeOperator_inner
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (normal : Normal) (x y : Tangent) :
    ⟪rieszShapeOperator form normal x, y⟫_ℝ =
      ⟪form x y, normal⟫_ℝ := by
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
  change ⟪normal, form x y⟫_ℝ = ⟪form x y, normal⟫_ℝ
  exact real_inner_comm _ _

/-- The Riesz construction instantiates all shape-operator data required by the
algebraic normal Ricci theorem. -/
def rieszShapeOperatorData
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    ShapeOperatorData Tangent Normal where
  secondFundamental := form
  secondFundamental_symmetric := form.symmetric
  shape normal x := rieszShapeOperator form normal x
  adjoint_relation := rieszShapeOperator_inner form

/-- Self-adjointness now follows from `II` and finite-dimensional Riesz rather
than being supplied as independent data. -/
theorem rieszShapeOperator_self_adjoint
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (normal : Normal) (x y : Tangent) :
    ⟪rieszShapeOperator form normal x, y⟫_ℝ =
      ⟪x, rieszShapeOperator form normal y⟫_ℝ :=
  shape_self_adjoint (rieszShapeOperatorData form) normal x y

/-- Concrete shape-commutator term constructed solely from `II`. -/
def rieszRicciShapeCommutator
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    Tangent → Tangent → Normal → Normal → ℝ :=
  ricciShapeCommutator (rieszShapeOperatorData form)

/-- The Riesz-constructed Ricci term is skew in tangent directions. -/
theorem rieszRicciShapeCommutator_swap_tangent
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    rieszRicciShapeCommutator form y x firstNormal secondNormal =
      -rieszRicciShapeCommutator form x y firstNormal secondNormal :=
  ricciShapeCommutator_swap_tangent
    (rieszShapeOperatorData form) x y firstNormal secondNormal

/-- The Riesz-constructed Ricci term is skew in normal directions. -/
theorem rieszRicciShapeCommutator_swap_normal
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    rieszRicciShapeCommutator form x y secondNormal firstNormal =
      -rieszRicciShapeCommutator form x y firstNormal secondNormal :=
  ricciShapeCommutator_swap_normal
    (rieszShapeOperatorData form) x y firstNormal secondNormal

/-- Reconstruct algebraic normal curvature directly from ambient mixed curvature
and a finite-dimensional `II`. -/
def rieszReconstructedNormalCurvature
    (ambientMixed : RealNormalCurvatureTensor Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    RealNormalCurvatureTensor Tangent Normal :=
  ricciReconstructedNormalCurvature ambientMixed
    (rieszShapeOperatorData form)

/-- The Riesz reconstruction satisfies the pointwise normal Ricci equation. -/
theorem rieszReconstructedNormalCurvature_satisfies
    (ambientMixed : RealNormalCurvatureTensor Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    SatisfiesRicciNormalEquation
      (rieszReconstructedNormalCurvature ambientMixed form)
      ambientMixed (rieszShapeOperatorData form) :=
  ricciReconstructedNormalCurvature_satisfies
    ambientMixed (rieszShapeOperatorData form)

/-- Exact boundary after constructing shape operators by Riesz. -/
structure RieszShapeOperatorStatus where
  finiteBilinearIIModelConstructed : Prop
  automaticFiniteDimensionalContinuityUsed : Prop
  rieszShapeOperatorsConstructed : Prop
  weingartenRelationProved : Prop
  selfAdjointnessDerived : Prop
  ricciCommutatorSymmetriesDerived : Prop
  actualGeometricIIInserted : Prop
  normalParameterLinearityBundled : Prop
  residualOrthogonalEquivarianceProved : Prop
  smoothDependenceOnBackgroundJetsProved : Prop
  actualNormalConnectionCurvatureInserted : Prop

/-- Closure of the geometric Riesz/shape-operator stage. -/
def rieszShapeOperatorClosed (s : RieszShapeOperatorStatus) : Prop :=
  s.finiteBilinearIIModelConstructed /\
  s.automaticFiniteDimensionalContinuityUsed /\
  s.rieszShapeOperatorsConstructed /\
  s.weingartenRelationProved /\
  s.selfAdjointnessDerived /\
  s.ricciCommutatorSymmetriesDerived /\
  s.actualGeometricIIInserted /\
  s.normalParameterLinearityBundled /\
  s.residualOrthogonalEquivarianceProved /\
  s.smoothDependenceOnBackgroundJetsProved /\
  s.actualNormalConnectionCurvatureInserted

/-- Pointwise Riesz representation does not itself prove smooth dependence on
the structured background jet. -/
theorem missing_smooth_background_dependence_blocks_riesz_stage
    (s : RieszShapeOperatorStatus)
    (hMissing : Not s.smoothDependenceOnBackgroundJetsProved) :
    Not (rieszShapeOperatorClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperator
end JanusFormal
