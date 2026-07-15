import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootFrechetSylvester

/-!
A local inverse-function-theorem gate for real `4 x 4` matrix square roots.

At a supplied root `X`, the derivative of `Y ↦ Y²` is the Sylvester map
`H ↦ XH + HX`.  When that map is supplied as a continuous linear
equivalence, the inverse function theorem produces a genuine local root
branch on a neighbourhood of `X²`, with derivative the inverse Sylvester
map.  The identity root gives a concrete co-diagonal positive base point.

This is only a local matrix statement.  It makes no global, principal,
Lorentz-causal-domain, or smooth-field-selection claim.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzLocalRootBranch4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4

local instance matrix4NormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

local instance matrix4AddCommGroup : AddCommGroup Matrix4 :=
  matrix4NormedAddCommGroup.toAddCommGroup

local instance matrix4TopologicalSpace : TopologicalSpace Matrix4 :=
  matrix4NormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance matrix4NormedSpace : NormedSpace ℝ Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance matrix4Module : Module ℝ Matrix4 :=
  matrix4NormedSpace.toModule

/-- Strict derivative predicate with the Frobenius topology used by matrix
multiplication in this gate. -/
abbrev MatrixHasStrictFDerivAt
    (f : Matrix4 → Matrix4) (f' : Matrix4 →L[ℝ] Matrix4)
    (point : Matrix4) : Prop :=
  HasStrictFDerivAt f f' point

/-- Ordinary derivative predicate with the same fixed matrix topology. -/
abbrev MatrixHasFDerivAt
    (f : Matrix4 → Matrix4) (f' : Matrix4 →L[ℝ] Matrix4)
    (point : Matrix4) : Prop :=
  HasFDerivAt f f' point

/-- Squaring on the full real `4 x 4` matrix space. -/
def matrixSquare (root : Matrix4) : Matrix4 := root * root

/-- The Sylvester linearization of matrix squaring at `root`. -/
def sylvesterMap (root : Matrix4) : Matrix4 →L[ℝ] Matrix4 :=
  P0EFTJanusMatrixSquareRootFrechetSylvester.sylvesterOperator root

@[simp]
theorem sylvesterMap_apply (root variation : Matrix4) :
    sylvesterMap root variation =
      root * variation + variation * root := by
  rfl

/-- Matrix squaring has the strict Fréchet derivative required by the
inverse function theorem. -/
theorem matrixSquare_hasStrictFDerivAt (root : Matrix4) :
    HasStrictFDerivAt matrixSquare (sylvesterMap root) root := by
  have hIdentity :
      HasStrictFDerivAt (fun point : Matrix4 => point)
        (ContinuousLinearMap.id ℝ Matrix4) root :=
    hasStrictFDerivAt_id root
  have hProduct := hIdentity.mul' hIdentity
  refine hProduct.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro variation
  rfl

/-- Exact nonsingularity data for the Sylvester derivative at one root. -/
structure SylvesterEquivWitness (root : Matrix4) where
  equiv : Matrix4 ≃L[ℝ] Matrix4
  forward_eq :
    (equiv : Matrix4 →L[ℝ] Matrix4) = sylvesterMap root

theorem inverseSylvester_left
    (root : Matrix4) (witness : SylvesterEquivWitness root)
    (variation : Matrix4) :
    witness.equiv.symm (sylvesterMap root variation) = variation := by
  rw [← witness.forward_eq]
  exact witness.equiv.symm_apply_apply variation

theorem inverseSylvester_right
    (root : Matrix4) (witness : SylvesterEquivWitness root)
    (variation : Matrix4) :
    sylvesterMap root (witness.equiv.symm variation) = variation := by
  rw [← witness.forward_eq]
  exact witness.equiv.apply_symm_apply variation

theorem matrixSquare_hasStrictFDerivAt_equiv
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    HasStrictFDerivAt matrixSquare
      (witness.equiv : Matrix4 →L[ℝ] Matrix4) root :=
  (matrixSquare_hasStrictFDerivAt root).congr_fderiv
    witness.forward_eq.symm

/-- The local chart supplied by the inverse function theorem. -/
def localSquareChart
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    OpenPartialHomeomorph Matrix4 Matrix4 :=
  HasStrictFDerivAt.toOpenPartialHomeomorph
    matrixSquare (matrixSquare_hasStrictFDerivAt_equiv root witness)

@[simp]
theorem localSquareChart_apply
    (root : Matrix4) (witness : SylvesterEquivWitness root)
    (point : Matrix4) :
    localSquareChart root witness point = matrixSquare point := by
  rfl

theorem root_mem_localSquareChart_source
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    root ∈ (localSquareChart root witness).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (matrixSquare_hasStrictFDerivAt_equiv root witness)

theorem square_mem_localSquareChart_target
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    matrixSquare root ∈ (localSquareChart root witness).target :=
  HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target
    (matrixSquare_hasStrictFDerivAt_equiv root witness)

/-- The actual local square-root branch furnished by the chart. -/
def localRootBranch
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    Matrix4 → Matrix4 :=
  HasStrictFDerivAt.localInverse matrixSquare witness.equiv root
    (matrixSquare_hasStrictFDerivAt_equiv root witness)

@[simp]
theorem localRootBranch_at_base
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    localRootBranch root witness (matrixSquare root) = root :=
  HasStrictFDerivAt.localInverse_apply_image
    (matrixSquare_hasStrictFDerivAt_equiv root witness)

/-- Every independently perturbed matrix in some neighbourhood of `X²`
is squared back exactly by the local branch. -/
theorem eventually_matrixSquare_localRootBranch
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    ∀ᶠ target in 𝓝 (matrixSquare root),
      matrixSquare (localRootBranch root witness target) = target :=
  HasStrictFDerivAt.eventually_right_inverse
    (matrixSquare_hasStrictFDerivAt_equiv root witness)

/-- The branch is a local left inverse on the corresponding root
neighbourhood. -/
theorem eventually_localRootBranch_matrixSquare
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    ∀ᶠ point in 𝓝 root,
      localRootBranch root witness (matrixSquare point) = point :=
  HasStrictFDerivAt.eventually_left_inverse
    (matrixSquare_hasStrictFDerivAt_equiv root witness)

/-- The IFT derivative is precisely the inverse Sylvester operator. -/
theorem localRootBranch_hasStrictFDerivAt
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    MatrixHasStrictFDerivAt (localRootBranch root witness)
      (witness.equiv.symm : Matrix4 →L[ℝ] Matrix4)
      (matrixSquare root) := by
  simpa only [localRootBranch] using
    HasStrictFDerivAt.to_localInverse
      (matrixSquare_hasStrictFDerivAt_equiv root witness)

theorem localRootBranch_hasFDerivAt
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    MatrixHasFDerivAt (localRootBranch root witness)
      (witness.equiv.symm : Matrix4 →L[ℝ] Matrix4)
      (matrixSquare root) :=
  (localRootBranch_hasStrictFDerivAt root witness).hasFDerivAt

/-- Scalar multiplication by two, the Sylvester equivalence at `X = I`. -/
def twiceEquiv : Matrix4 ≃L[ℝ] Matrix4 :=
  ContinuousLinearEquiv.smulLeft
    (R₁ := ℝ) (M₁ := Matrix4)
    (Units.mk0 (2 : ℝ) (by norm_num))

@[simp]
theorem twiceEquiv_apply (variation : Matrix4) :
    twiceEquiv variation = 2 • variation := by
  ext i j
  simp [twiceEquiv]

/-- At the positive co-diagonal identity root, the Sylvester map is an
explicit continuous linear equivalence. -/
def identitySylvesterWitness :
    SylvesterEquivWitness (1 : Matrix4) where
  equiv := twiceEquiv
  forward_eq := by
    apply ContinuousLinearMap.ext
    intro variation
    change twiceEquiv variation =
      P0EFTJanusMatrixSquareRootFrechetSylvester.sylvesterOperator
        (1 : Matrix4) variation
    rw [P0EFTJanusMatrixSquareRootFrechetSylvester.sylvesterOperator_apply]
    simp [twiceEquiv, two_smul]

@[simp]
theorem identity_matrixSquare :
    matrixSquare (1 : Matrix4) = 1 := by
  simp [matrixSquare]

/-- Concrete local branch around the identity relative matrix. -/
def identityLocalRootBranch : Matrix4 → Matrix4 :=
  localRootBranch (1 : Matrix4) identitySylvesterWitness

@[simp]
theorem identityLocalRootBranch_at_identity :
    identityLocalRootBranch 1 = (1 : Matrix4) := by
  simpa [identityLocalRootBranch, identity_matrixSquare] using
    localRootBranch_at_base (1 : Matrix4) identitySylvesterWitness

theorem eventually_identityLocalRootBranch_square :
    ∀ᶠ target in 𝓝 (1 : Matrix4),
      matrixSquare (identityLocalRootBranch target) = target := by
  simpa [identityLocalRootBranch] using
    eventually_matrixSquare_localRootBranch
      (1 : Matrix4) identitySylvesterWitness

theorem identityLocalRootBranch_hasFDerivAt :
    MatrixHasFDerivAt identityLocalRootBranch
      (twiceEquiv.symm : Matrix4 →L[ℝ] Matrix4) (1 : Matrix4) := by
  simpa only [identityLocalRootBranch, identitySylvesterWitness,
    identity_matrixSquare] using
    localRootBranch_hasFDerivAt
      (1 : Matrix4) identitySylvesterWitness

/-- Gate summary: a true local differentiable root branch in the complete
`4 x 4` matrix space, conditional only on exact Sylvester invertibility,
with a concrete identity-base instance. -/
theorem lorentzLocalRootBranch4D_gate
    (root : Matrix4) (witness : SylvesterEquivWitness root) :
    localRootBranch root witness (matrixSquare root) = root ∧
      MatrixHasFDerivAt (localRootBranch root witness)
        (witness.equiv.symm : Matrix4 →L[ℝ] Matrix4)
        (matrixSquare root) ∧
      (∀ᶠ target in 𝓝 (matrixSquare root),
        matrixSquare (localRootBranch root witness target) = target) := by
  exact ⟨localRootBranch_at_base root witness,
    localRootBranch_hasFDerivAt root witness,
    eventually_matrixSquare_localRootBranch root witness⟩

end

end P0EFTJanusLorentzLocalRootBranch4D
end JanusFormal
