import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorSmoothDependence

namespace JanusFormal
namespace P0EFTJanusMetricNormalConnectionCurvature

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusRicciNormalEquation
open P0EFTJanusRieszShapeOperator

universe u v

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]

/-- Skew-adjointness of a continuous normal endomorphism, the infinitesimal
metric-compatibility condition for an orthogonal connection. -/
def IsSkewAdjointOperator (operator : Normal →L[ℝ] Normal) : Prop :=
  ∀ first second,
    ⟪operator first, second⟫_ℝ = -⟪first, operator second⟫_ℝ

/-- A difference of skew-adjoint operators is skew-adjoint. -/
theorem skewAdjoint_sub
    {first second : Normal →L[ℝ] Normal}
    (hFirst : IsSkewAdjointOperator first)
    (hSecond : IsSkewAdjointOperator second) :
    IsSkewAdjointOperator (first - second) := by
  intro x y
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  rw [hFirst x y, hSecond x y]
  ring

/-- A sum of skew-adjoint operators is skew-adjoint. -/
theorem skewAdjoint_add
    {first second : Normal →L[ℝ] Normal}
    (hFirst : IsSkewAdjointOperator first)
    (hSecond : IsSkewAdjointOperator second) :
    IsSkewAdjointOperator (first + second) := by
  intro x y
  simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  rw [hFirst x y, hSecond x y]
  ring

/-- Commutator convention `[A,B] = A ∘ B - B ∘ A`. -/
def operatorCommutator
    (first second : Normal →L[ℝ] Normal) :
    Normal →L[ℝ] Normal :=
  first.comp second - second.comp first

/-- The commutator of two skew-adjoint operators is again skew-adjoint. -/
theorem skewAdjoint_operatorCommutator
    {first second : Normal →L[ℝ] Normal}
    (hFirst : IsSkewAdjointOperator first)
    (hSecond : IsSkewAdjointOperator second) :
    IsSkewAdjointOperator (operatorCommutator first second) := by
  intro x y
  simp only [operatorCommutator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, inner_sub_left, inner_sub_right]
  rw [hFirst (second x) y, hSecond x (first y),
    hSecond (first x) y, hFirst x (second y)]
  ring

/-- Pointwise first jet of a metric normal connection in a commuting tangent
coordinate frame.

`coefficient x` is the normal connection matrix `ω_x`, and
`derivative x y` is `∂_x ω_y` at the base point. Metric compatibility is encoded
by skew-adjointness of both coefficient and derivative matrices. -/
structure MetricNormalConnectionOneJet
    (Tangent : Type u) (Normal : Type v)
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal] where
  coefficient : Tangent →ₗ[ℝ] Normal →L[ℝ] Normal
  derivative : Tangent →ₗ[ℝ] Tangent →ₗ[ℝ] Normal →L[ℝ] Normal
  coefficient_skew : ∀ x, IsSkewAdjointOperator (coefficient x)
  derivative_skew : ∀ x y, IsSkewAdjointOperator (derivative x y)

/-- Curvature endomorphism

`R^⊥(x,y) = ∂_xω_y - ∂_yω_x + [ω_x,ω_y]`

in a commuting tangent coordinate frame. -/
def normalConnectionCurvatureEndomorphism
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) : Normal →L[ℝ] Normal :=
  jet.derivative x y - jet.derivative y x +
    operatorCommutator (jet.coefficient x) (jet.coefficient y)

/-- Normal curvature is skew in the tangent directions. -/
theorem normalConnectionCurvatureEndomorphism_swap_tangent
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) :
    normalConnectionCurvatureEndomorphism jet y x =
      -normalConnectionCurvatureEndomorphism jet x y := by
  apply ContinuousLinearMap.ext
  intro normal
  simp [normalConnectionCurvatureEndomorphism, operatorCommutator]
  abel

/-- Metric compatibility makes every normal-curvature endomorphism
skew-adjoint. -/
theorem normalConnectionCurvatureEndomorphism_skew
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) :
    IsSkewAdjointOperator
      (normalConnectionCurvatureEndomorphism jet x y) :=
  skewAdjoint_add
    (skewAdjoint_sub (jet.derivative_skew x y)
      (jet.derivative_skew y x))
    (skewAdjoint_operatorCommutator
      (jet.coefficient_skew x) (jet.coefficient_skew y))

/-- Scalar normal-curvature tensor obtained by pairing the curvature
endomorphism with a second normal vector. -/
def normalConnectionCurvatureScalar
    (jet : MetricNormalConnectionOneJet Tangent Normal) :
    RealNormalCurvatureTensor Tangent Normal :=
  fun x y firstNormal secondNormal =>
    ⟪normalConnectionCurvatureEndomorphism jet x y firstNormal,
      secondNormal⟫_ℝ

/-- Scalar normal curvature is skew in tangent directions. -/
theorem normalConnectionCurvatureScalar_swap_tangent
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    normalConnectionCurvatureScalar jet y x firstNormal secondNormal =
      -normalConnectionCurvatureScalar jet x y firstNormal secondNormal := by
  change
    ⟪normalConnectionCurvatureEndomorphism jet y x firstNormal,
      secondNormal⟫_ℝ =
      -⟪normalConnectionCurvatureEndomorphism jet x y firstNormal,
        secondNormal⟫_ℝ
  rw [normalConnectionCurvatureEndomorphism_swap_tangent]
  simp

/-- Scalar normal curvature is skew in normal directions. -/
theorem normalConnectionCurvatureScalar_swap_normal
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    normalConnectionCurvatureScalar jet x y secondNormal firstNormal =
      -normalConnectionCurvatureScalar jet x y firstNormal secondNormal := by
  change
    ⟪normalConnectionCurvatureEndomorphism jet x y secondNormal,
      firstNormal⟫_ℝ =
      -⟪normalConnectionCurvatureEndomorphism jet x y firstNormal,
        secondNormal⟫_ℝ
  calc
    ⟪normalConnectionCurvatureEndomorphism jet x y secondNormal,
        firstNormal⟫_ℝ =
      -⟪secondNormal,
        normalConnectionCurvatureEndomorphism jet x y firstNormal⟫_ℝ :=
      normalConnectionCurvatureEndomorphism_skew jet x y
        secondNormal firstNormal
    _ = -⟪normalConnectionCurvatureEndomorphism jet x y firstNormal,
        secondNormal⟫_ℝ := by rw [real_inner_comm]

/-- The local metric normal connection produces an algebraic normal-curvature
tensor with both required skew symmetries. -/
def normalConnectionAlgebraicCurvature
    (jet : MetricNormalConnectionOneJet Tangent Normal) :
    AlgebraicNormalCurvatureTensor Tangent Normal where
  toFun := normalConnectionCurvatureScalar jet
  skewTangent := normalConnectionCurvatureScalar_swap_tangent jet
  skewNormal := normalConnectionCurvatureScalar_swap_normal jet

/-- Off-diagonal plus normal block of the ambient connection in an adapted
splitting. The tangential diagonal connection is omitted because it does not
enter the normal-normal block of the Ricci equation.

For `(t,ξ) ∈ T ⊕ N`,

`Ω_x(t,ξ) = (-A_ξ x, II(x,t) + ω_x ξ)`. -/
def splitAmbientConnectionAction
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (x : Tangent) (state : Tangent × Normal) : Tangent × Normal :=
  (-rieszShapeOperator form state.2 x,
    form x state.1 + jet.coefficient x state.2)

/-- Normal action of the ambient curvature on a pure normal input, computed from
the first jet of the adapted block connection. -/
def splitAmbientMixedCurvatureAction
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (x y : Tangent) (normal : Normal) : Normal :=
  jet.derivative x y normal - jet.derivative y x normal +
    (splitAmbientConnectionAction form jet x
      (splitAmbientConnectionAction form jet y (0, normal))).2 -
    (splitAmbientConnectionAction form jet y
      (splitAmbientConnectionAction form jet x (0, normal))).2

/-- Expansion of the normal ambient-curvature block into intrinsic normal
curvature plus the off-diagonal extrinsic contribution. -/
theorem splitAmbientMixedCurvatureAction_expansion
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (x y : Tangent) (normal : Normal) :
    splitAmbientMixedCurvatureAction jet form x y normal =
      normalConnectionCurvatureEndomorphism jet x y normal +
        (-form x (rieszShapeOperator form normal y) +
          form y (rieszShapeOperator form normal x)) := by
  simp [splitAmbientMixedCurvatureAction, splitAmbientConnectionAction,
    normalConnectionCurvatureEndomorphism, operatorCommutator]
  abel

/-- The off-diagonal block contribution is the negative of the shape-operator
commutator in the convention used by the Ricci equation. -/
theorem splitExtrinsicTerm_eq_neg_rieszCommutator
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    ⟪-form x (rieszShapeOperator form firstNormal y) +
        form y (rieszShapeOperator form firstNormal x),
      secondNormal⟫_ℝ =
      -rieszRicciShapeCommutator form x y firstNormal secondNormal := by
  simp only [inner_add_left, inner_neg_left]
  rw [← rieszShapeOperator_inner form secondNormal x
      (rieszShapeOperator form firstNormal y),
    ← rieszShapeOperator_inner form secondNormal y
      (rieszShapeOperator form firstNormal x)]
  change
    -⟪rieszShapeOperator form secondNormal x,
        rieszShapeOperator form firstNormal y⟫_ℝ +
      ⟪rieszShapeOperator form secondNormal y,
        rieszShapeOperator form firstNormal x⟫_ℝ =
      -(⟪rieszShapeOperator form firstNormal
            (rieszShapeOperator form secondNormal x), y⟫_ℝ -
        ⟪rieszShapeOperator form secondNormal
            (rieszShapeOperator form firstNormal x), y⟫_ℝ)
  rw [rieszShapeOperator_self_adjoint form firstNormal
      (rieszShapeOperator form secondNormal x) y,
    rieszShapeOperator_self_adjoint form secondNormal
      (rieszShapeOperator form firstNormal x) y,
    real_inner_comm (rieszShapeOperator form secondNormal y)
      (rieszShapeOperator form firstNormal x)]
  ring

/-- Scalar mixed ambient curvature in the adapted block model. -/
def splitAmbientMixedCurvatureScalar
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    RealNormalCurvatureTensor Tangent Normal :=
  fun x y firstNormal secondNormal =>
    ⟪splitAmbientMixedCurvatureAction jet form x y firstNormal,
      secondNormal⟫_ℝ

/-- The ambient mixed curvature equals normal curvature minus the shape
commutator. -/
theorem splitAmbientMixedCurvatureScalar_eq
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    splitAmbientMixedCurvatureScalar jet form x y firstNormal secondNormal =
      normalConnectionCurvatureScalar jet x y firstNormal secondNormal -
        rieszRicciShapeCommutator form x y firstNormal secondNormal := by
  rw [splitAmbientMixedCurvatureScalar,
    splitAmbientMixedCurvatureAction_expansion, inner_add_left,
    splitExtrinsicTerm_eq_neg_rieszCommutator]
  rfl

/-- The local metric normal connection and the adapted ambient block connection
satisfy the Ricci normal equation as a derived identity. -/
theorem metricNormalConnection_satisfies_Ricci
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    SatisfiesRicciNormalEquation
      (normalConnectionCurvatureScalar jet)
      (splitAmbientMixedCurvatureScalar jet form)
      (rieszShapeOperatorData form) := by
  intro x y firstNormal secondNormal
  change
    normalConnectionCurvatureScalar jet x y firstNormal secondNormal =
      splitAmbientMixedCurvatureScalar jet form x y firstNormal secondNormal +
        rieszRicciShapeCommutator form x y firstNormal secondNormal
  rw [splitAmbientMixedCurvatureScalar_eq]
  ring

/-- The mixed ambient curvature derived from the block connection is skew in the
tangent directions. -/
theorem splitAmbientMixedCurvatureScalar_swap_tangent
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    splitAmbientMixedCurvatureScalar jet form y x firstNormal secondNormal =
      -splitAmbientMixedCurvatureScalar jet form x y firstNormal secondNormal := by
  rw [splitAmbientMixedCurvatureScalar_eq,
    splitAmbientMixedCurvatureScalar_eq,
    normalConnectionCurvatureScalar_swap_tangent,
    rieszRicciShapeCommutator_swap_tangent]
  ring

/-- The mixed ambient curvature derived from the block connection is skew in the
normal directions. -/
theorem splitAmbientMixedCurvatureScalar_swap_normal
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal)
    (x y : Tangent) (firstNormal secondNormal : Normal) :
    splitAmbientMixedCurvatureScalar jet form x y secondNormal firstNormal =
      -splitAmbientMixedCurvatureScalar jet form x y firstNormal secondNormal := by
  rw [splitAmbientMixedCurvatureScalar_eq,
    splitAmbientMixedCurvatureScalar_eq,
    normalConnectionCurvatureScalar_swap_normal,
    rieszRicciShapeCommutator_swap_normal]
  ring

/-- The split ambient block curvature is itself an algebraic mixed-curvature
tensor. -/
def splitAmbientMixedAlgebraicCurvature
    (jet : MetricNormalConnectionOneJet Tangent Normal)
    (form : FiniteSecondFundamentalForm Tangent Normal) :
    AlgebraicNormalCurvatureTensor Tangent Normal where
  toFun := splitAmbientMixedCurvatureScalar jet form
  skewTangent := splitAmbientMixedCurvatureScalar_swap_tangent jet form
  skewNormal := splitAmbientMixedCurvatureScalar_swap_normal jet form

/-- Exact progress boundary after inserting a local metric normal-connection jet
and deriving Ricci from the adapted block connection. -/
structure MetricNormalConnectionCurvatureStatus where
  metricNormalConnectionOneJetDefined : Prop
  normalCurvatureFormulaConstructed : Prop
  normalCurvatureSkewSymmetriesProved : Prop
  adaptedAmbientBlockConnectionConstructed : Prop
  ambientMixedCurvatureDerived : Prop
  ricciEquationDerivedFromBlockCurvature : Prop
  actualManifoldNormalConnectionInserted : Prop
  actualAmbientLeviCivitaConnectionInserted : Prop
  varyingFrameGaugeLawProved : Prop
  smoothStructuredJetBundleCompatibilityProved : Prop

/-- Closure of the manifold-level normal-curvature/Ricci stage. -/
def metricNormalConnectionCurvatureClosed
    (s : MetricNormalConnectionCurvatureStatus) : Prop :=
  s.metricNormalConnectionOneJetDefined /\
  s.normalCurvatureFormulaConstructed /\
  s.normalCurvatureSkewSymmetriesProved /\
  s.adaptedAmbientBlockConnectionConstructed /\
  s.ambientMixedCurvatureDerived /\
  s.ricciEquationDerivedFromBlockCurvature /\
  s.actualManifoldNormalConnectionInserted /\
  s.actualAmbientLeviCivitaConnectionInserted /\
  s.varyingFrameGaugeLawProved /\
  s.smoothStructuredJetBundleCompatibilityProved

/-- The coordinate-jet Ricci theorem is not yet the curvature theorem for the
actual Janus normal bundle until the manifold normal connection is inserted. -/
theorem missing_manifold_normal_connection_blocks_full_stage
    (s : MetricNormalConnectionCurvatureStatus)
    (hMissing : Not s.actualManifoldNormalConnectionInserted) :
    Not (metricNormalConnectionCurvatureClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.1

end

end P0EFTJanusMetricNormalConnectionCurvature
end JanusFormal
