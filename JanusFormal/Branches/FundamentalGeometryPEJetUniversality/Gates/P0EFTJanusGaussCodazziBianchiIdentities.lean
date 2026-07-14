import Mathlib.Analysis.InnerProductSpace.LinearMap
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondFundamentalFormJet

namespace JanusFormal
namespace P0EFTJanusGaussCodazziBianchiIdentities

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusSecondFundamentalFormJet

universe u v

/-- A real four-covariant curvature tensor at one point. No multilinearity is
bundled yet; this gate isolates the permutation identities needed by the jet
isomorphism program. -/
abbrev RealCurvatureTensor (Tangent : Type u) :=
  Tangent → Tangent → Tangent → Tangent → ℝ

/-- Algebraic Riemann-curvature symmetries in the sign convention used by the
Gauss tensor below. -/
structure AlgebraicCurvatureTensor (Tangent : Type u) where
  toFun : RealCurvatureTensor Tangent
  skewFirst : ∀ x y z w, toFun y x z w = -toFun x y z w
  skewSecond : ∀ x y z w, toFun x y w z = -toFun x y z w
  pairExchange : ∀ x y z w, toFun z w x y = toFun x y z w
  firstBianchi : ∀ x y z w,
    toFun x y z w + toFun y z x w + toFun z x y w = 0

section Gauss

variable {Tangent : Type u}
variable {Normal : Type v}
variable [NormedAddCommGroup Normal]
variable [InnerProductSpace ℝ Normal]

/-- The quadratic extrinsic term in the Gauss equation,

`<B(x,w),B(y,z)> - <B(x,z),B(y,w)>`.
-/
def gaussQuadraticTensor
    (secondFundamental : Tangent → Tangent → Normal) :
    RealCurvatureTensor Tangent :=
  fun x y z w =>
    ⟪secondFundamental x w, secondFundamental y z⟫_ℝ -
      ⟪secondFundamental x z, secondFundamental y w⟫_ℝ

/-- The Gauss quadratic term is skew in its first pair without any symmetry
hypothesis on `B`. -/
theorem gaussQuadraticTensor_swap_first
    (secondFundamental : Tangent → Tangent → Normal)
    (x y z w : Tangent) :
    gaussQuadraticTensor secondFundamental y x z w =
      -gaussQuadraticTensor secondFundamental x y z w := by
  simp only [gaussQuadraticTensor]
  rw [real_inner_comm (secondFundamental y w) (secondFundamental x z),
    real_inner_comm (secondFundamental y z) (secondFundamental x w)]
  ring

/-- The Gauss quadratic term is skew in its second pair. -/
theorem gaussQuadraticTensor_swap_second
    (secondFundamental : Tangent → Tangent → Normal)
    (x y z w : Tangent) :
    gaussQuadraticTensor secondFundamental x y w z =
      -gaussQuadraticTensor secondFundamental x y z w := by
  simp only [gaussQuadraticTensor]
  ring

/-- Symmetry of `B` supplies exchange symmetry between the two curvature pairs. -/
theorem gaussQuadraticTensor_pair_exchange
    (secondFundamental : Tangent → Tangent → Normal)
    (hSymmetric : IsSymmetricTensor secondFundamental)
    (x y z w : Tangent) :
    gaussQuadraticTensor secondFundamental z w x y =
      gaussQuadraticTensor secondFundamental x y z w := by
  simp only [gaussQuadraticTensor]
  rw [hSymmetric z y, hSymmetric w x,
    hSymmetric z x, hSymmetric w y,
    real_inner_comm (secondFundamental y z) (secondFundamental x w)]

/-- The first Bianchi identity for the Gauss quadratic term follows solely from
symmetry of the second fundamental form. -/
theorem gaussQuadraticTensor_first_bianchi
    (secondFundamental : Tangent → Tangent → Normal)
    (hSymmetric : IsSymmetricTensor secondFundamental)
    (x y z w : Tangent) :
    gaussQuadraticTensor secondFundamental x y z w +
        gaussQuadraticTensor secondFundamental y z x w +
        gaussQuadraticTensor secondFundamental z x y w = 0 := by
  simp only [gaussQuadraticTensor]
  rw [hSymmetric z x, hSymmetric y x, hSymmetric z y]
  rw [real_inner_comm (secondFundamental y w) (secondFundamental x z),
    real_inner_comm (secondFundamental z w) (secondFundamental x y),
    real_inner_comm (secondFundamental y z) (secondFundamental x w)]
  ring

/-- The Gauss quadratic term is an algebraic curvature tensor whenever `B` is
symmetric. -/
def gaussAlgebraicCurvatureTensor
    (secondFundamental : Tangent → Tangent → Normal)
    (hSymmetric : IsSymmetricTensor secondFundamental) :
    AlgebraicCurvatureTensor Tangent where
  toFun := gaussQuadraticTensor secondFundamental
  skewFirst := gaussQuadraticTensor_swap_first secondFundamental
  skewSecond := gaussQuadraticTensor_swap_second secondFundamental
  pairExchange := gaussQuadraticTensor_pair_exchange secondFundamental hSymmetric
  firstBianchi := gaussQuadraticTensor_first_bianchi secondFundamental hSymmetric

/-- Pointwise Gauss equation for an intrinsic curvature tensor, the tangential
ambient-curvature restriction and a second fundamental form. -/
def SatisfiesGaussEquation
    (intrinsic ambientTangential : RealCurvatureTensor Tangent)
    (secondFundamental : Tangent → Tangent → Normal) : Prop :=
  ∀ x y z w,
    intrinsic x y z w =
      ambientTangential x y z w +
        gaussQuadraticTensor secondFundamental x y z w

/-- Curvature reconstructed from ambient tangential curvature and `B`. -/
def gaussReconstructedCurvature
    (ambientTangential : RealCurvatureTensor Tangent)
    (secondFundamental : Tangent → Tangent → Normal) :
    RealCurvatureTensor Tangent :=
  fun x y z w =>
    ambientTangential x y z w +
      gaussQuadraticTensor secondFundamental x y z w

/-- The reconstructed curvature satisfies the Gauss equation by construction. -/
theorem gaussReconstructedCurvature_satisfies
    (ambientTangential : RealCurvatureTensor Tangent)
    (secondFundamental : Tangent → Tangent → Normal) :
    SatisfiesGaussEquation
      (gaussReconstructedCurvature ambientTangential secondFundamental)
      ambientTangential secondFundamental := by
  intro x y z w
  rfl

/-- Orthogonal change of tangent and normal frames for a normal-valued bilinear
tensor. -/
def transformSecondFundamental
    [NormedAddCommGroup Tangent]
    [InnerProductSpace ℝ Tangent]
    (tangentFrame : Tangent ≃ₗᵢ[ℝ] Tangent)
    (normalFrame : Normal ≃ₗᵢ[ℝ] Normal)
    (secondFundamental : Tangent → Tangent → Normal) :
    Tangent → Tangent → Normal :=
  fun x y =>
    normalFrame
      (secondFundamental (tangentFrame.symm x) (tangentFrame.symm y))

/-- The Gauss tensor is equivariant under the residual orthogonal frame group. -/
theorem gaussQuadraticTensor_transform
    [NormedAddCommGroup Tangent]
    [InnerProductSpace ℝ Tangent]
    (tangentFrame : Tangent ≃ₗᵢ[ℝ] Tangent)
    (normalFrame : Normal ≃ₗᵢ[ℝ] Normal)
    (secondFundamental : Tangent → Tangent → Normal)
    (x y z w : Tangent) :
    gaussQuadraticTensor
        (transformSecondFundamental tangentFrame normalFrame secondFundamental)
        x y z w =
      gaussQuadraticTensor secondFundamental
        (tangentFrame.symm x) (tangentFrame.symm y)
        (tangentFrame.symm z) (tangentFrame.symm w) := by
  simp [gaussQuadraticTensor, transformSecondFundamental]

/-- Residual orthogonal frame changes preserve symmetry of `B`. -/
theorem transformSecondFundamental_isSymmetric
    [NormedAddCommGroup Tangent]
    [InnerProductSpace ℝ Tangent]
    (tangentFrame : Tangent ≃ₗᵢ[ℝ] Tangent)
    (normalFrame : Normal ≃ₗᵢ[ℝ] Normal)
    (secondFundamental : Tangent → Tangent → Normal)
    (hSymmetric : IsSymmetricTensor secondFundamental) :
    IsSymmetricTensor
      (transformSecondFundamental tangentFrame normalFrame secondFundamental) := by
  intro x y
  simp only [transformSecondFundamental]
  rw [hSymmetric]

end Gauss

section Codazzi

variable {Tangent : Type u}
variable {Normal : Type v}
variable [AddCommGroup Normal]

/-- A pointwise candidate for `∇B`, with the derivative index first. -/
abbrev CovariantDerivativeSecondFundamental :=
  Tangent → Tangent → Tangent → Normal

/-- Symmetry in the two arguments inherited from symmetry of `B`. -/
def IsLastTwoSymmetric
    (covariantDerivative : CovariantDerivativeSecondFundamental
      (Tangent := Tangent) (Normal := Normal)) : Prop :=
  ∀ x y z, covariantDerivative x y z = covariantDerivative x z y

/-- Alternation in the first two arguments: the Codazzi defect. -/
def codazziDefect
    (covariantDerivative : CovariantDerivativeSecondFundamental
      (Tangent := Tangent) (Normal := Normal)) :
    Tangent → Tangent → Tangent → Normal :=
  fun x y z =>
    covariantDerivative x y z - covariantDerivative y x z

/-- The Codazzi defect is skew in its first two arguments. -/
theorem codazziDefect_swap_first
    (covariantDerivative : CovariantDerivativeSecondFundamental
      (Tangent := Tangent) (Normal := Normal))
    (x y z : Tangent) :
    codazziDefect covariantDerivative y x z =
      -codazziDefect covariantDerivative x y z := by
  simp only [codazziDefect]
  abel

/-- The cyclic Codazzi identity is forced by symmetry in the last two indices of
`∇B`. -/
theorem codazziDefect_cyclic_zero
    (covariantDerivative : CovariantDerivativeSecondFundamental
      (Tangent := Tangent) (Normal := Normal))
    (hSymmetric : IsLastTwoSymmetric covariantDerivative)
    (x y z : Tangent) :
    codazziDefect covariantDerivative x y z +
        codazziDefect covariantDerivative y z x +
        codazziDefect covariantDerivative z x y = 0 := by
  simp only [codazziDefect]
  rw [hSymmetric y z x, hSymmetric z y x, hSymmetric x z y]
  abel

/-- Pointwise Codazzi equation. The right-hand side is intended to be the normal
component of ambient curvature. -/
def SatisfiesCodazziEquation
    (ambientNormalCurvature : Tangent → Tangent → Tangent → Normal)
    (covariantDerivative : CovariantDerivativeSecondFundamental
      (Tangent := Tangent) (Normal := Normal)) : Prop :=
  ∀ x y z,
    ambientNormalCurvature x y z =
      codazziDefect covariantDerivative x y z

/-- A Codazzi right-hand side obtained from a symmetric `∇B` necessarily obeys
the cyclic identity. -/
theorem codazziEquation_forces_cyclic_identity
    (ambientNormalCurvature : Tangent → Tangent → Tangent → Normal)
    (covariantDerivative : CovariantDerivativeSecondFundamental
      (Tangent := Tangent) (Normal := Normal))
    (hSymmetric : IsLastTwoSymmetric covariantDerivative)
    (hCodazzi : SatisfiesCodazziEquation ambientNormalCurvature covariantDerivative)
    (x y z : Tangent) :
    ambientNormalCurvature x y z +
        ambientNormalCurvature y z x +
        ambientNormalCurvature z x y = 0 := by
  rw [hCodazzi x y z, hCodazzi y z x, hCodazzi z x y]
  exact codazziDefect_cyclic_zero covariantDerivative hSymmetric x y z

end Codazzi

section AbelianBianchi

variable {Tangent : Type u}

/-- Symmetry of a local abelian connection's second derivative in its first two
partial-derivative indices. -/
def IsFirstTwoSymmetric
    (secondDerivative : Tangent → Tangent → Tangent → ℝ) : Prop :=
  ∀ x y z, secondDerivative x y z = secondDerivative y x z

/-- First derivative of abelian curvature obtained from a second derivative of
the local connection one-form. -/
def abelianCurvatureDerivative
    (secondDerivative : Tangent → Tangent → Tangent → ℝ) :
    Tangent → Tangent → Tangent → ℝ :=
  fun x y z =>
    secondDerivative x y z - secondDerivative x z y

/-- `∇F` remains skew in the curvature slots. -/
theorem abelianCurvatureDerivative_swap_last
    (secondDerivative : Tangent → Tangent → Tangent → ℝ)
    (x y z : Tangent) :
    abelianCurvatureDerivative secondDerivative x z y =
      -abelianCurvatureDerivative secondDerivative x y z := by
  simp only [abelianCurvatureDerivative]
  ring

/-- Equality of mixed second derivatives implies the abelian Bianchi identity
`dF=0` at the next jet order. -/
theorem abelianCurvatureDerivative_cyclic_zero
    (secondDerivative : Tangent → Tangent → Tangent → ℝ)
    (hSymmetric : IsFirstTwoSymmetric secondDerivative)
    (x y z : Tangent) :
    abelianCurvatureDerivative secondDerivative x y z +
        abelianCurvatureDerivative secondDerivative y z x +
        abelianCurvatureDerivative secondDerivative z x y = 0 := by
  simp only [abelianCurvatureDerivative]
  rw [hSymmetric y x z, hSymmetric z y x, hSymmetric z x y]
  ring

end AbelianBianchi

/-- Exact boundary of the first integrability package. -/
structure GaussCodazziBianchiStatus where
  gaussQuadraticCurvatureSymmetriesProved : Prop
  gaussFirstBianchiProved : Prop
  gaussResidualOrthogonalEquivarianceProved : Prop
  pointwiseGaussEquationDefined : Prop
  codazziSkewSymmetryProved : Prop
  codazziCyclicIdentityProved : Prop
  pointwiseCodazziEquationDefined : Prop
  abelianCurvatureDerivativeBianchiProved : Prop
  actualAmbientCurvatureJetsInserted : Prop
  normalConnectionAndRicciEquationInserted : Prop
  higherOrderFormalIntegrabilityProved : Prop

/-- Closure of the first geometric integrability stage. -/
def gaussCodazziBianchiClosed
    (s : GaussCodazziBianchiStatus) : Prop :=
  s.gaussQuadraticCurvatureSymmetriesProved /\
  s.gaussFirstBianchiProved /\
  s.gaussResidualOrthogonalEquivarianceProved /\
  s.pointwiseGaussEquationDefined /\
  s.codazziSkewSymmetryProved /\
  s.codazziCyclicIdentityProved /\
  s.pointwiseCodazziEquationDefined /\
  s.abelianCurvatureDerivativeBianchiProved /\
  s.actualAmbientCurvatureJetsInserted /\
  s.normalConnectionAndRicciEquationInserted /\
  s.higherOrderFormalIntegrabilityProved

/-- The algebraic identities do not yet insert the actual ambient curvature jet
of the Janus immersion. -/
theorem missing_ambient_curvature_blocks_geometric_integrability
    (s : GaussCodazziBianchiStatus)
    (hMissing : Not s.actualAmbientCurvatureJetsInserted) :
    Not (gaussCodazziBianchiClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusGaussCodazziBianchiIdentities
end JanusFormal
