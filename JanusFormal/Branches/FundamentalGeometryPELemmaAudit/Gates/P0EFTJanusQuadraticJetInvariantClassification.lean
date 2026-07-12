import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusVectorInvariantPairing

namespace JanusFormal
namespace P0EFTJanusQuadraticJetInvariantClassification

set_option autoImplicit false

open P0EFTJanusVectorInvariantPairing

/-- General real polynomial of total degree at most two on the local vector fiber. -/
@[ext] structure QuadraticPolynomial3 where
  constant : ℝ
  linearX : ℝ
  linearY : ℝ
  linearZ : ℝ
  xx : ℝ
  yy : ℝ
  zz : ℝ
  xy : ℝ
  xz : ℝ
  yz : ℝ

/-- Evaluation of the quadratic polynomial. -/
def evaluate
    (polynomial : QuadraticPolynomial3)
    (vector : Vector3) : ℝ :=
  polynomial.constant +
    polynomial.linearX * vector.x +
    polynomial.linearY * vector.y +
    polynomial.linearZ * vector.z +
    polynomial.xx * vector.x ^ 2 +
    polynomial.yy * vector.y ^ 2 +
    polynomial.zz * vector.z ^ 2 +
    polynomial.xy * vector.x * vector.y +
    polynomial.xz * vector.x * vector.z +
    polynomial.yz * vector.y * vector.z

/-- Reflection in the third coordinate. -/
def flipZ (vector : Vector3) : Vector3 :=
  { x := vector.x, y := vector.y, z := -vector.z }

/-- Test vectors. -/
def zeroVector : Vector3 := { x := 0, y := 0, z := 0 }

def xyVector : Vector3 := { x := 1, y := 1, z := 0 }

def xzVector : Vector3 := { x := 1, y := 0, z := 1 }

def yzVector : Vector3 := { x := 0, y := 1, z := 1 }

/-- Invariance under signed coordinate permutations. -/
structure SignedPermutationInvariant
    (polynomial : QuadraticPolynomial3) where
  flipXInvariant :
    ∀ vector,
      evaluate polynomial (flipX vector) = evaluate polynomial vector
  flipYInvariant :
    ∀ vector,
      evaluate polynomial (flipY vector) = evaluate polynomial vector
  flipZInvariant :
    ∀ vector,
      evaluate polynomial (flipZ vector) = evaluate polynomial vector
  swapXYInvariant :
    ∀ vector,
      evaluate polynomial (swapXY vector) = evaluate polynomial vector
  swapYZInvariant :
    ∀ vector,
      evaluate polynomial (swapYZ vector) = evaluate polynomial vector

/-- Reflection invariance removes the first linear coefficient. -/
theorem invariant_linear_x_zero
    (polynomial : QuadraticPolynomial3)
    (hInvariant : SignedPermutationInvariant polynomial) :
    polynomial.linearX = 0 := by
  have h := hInvariant.flipXInvariant basisX
  norm_num [evaluate, flipX, basisX] at h
  linarith

/-- Reflection invariance removes the second linear coefficient. -/
theorem invariant_linear_y_zero
    (polynomial : QuadraticPolynomial3)
    (hInvariant : SignedPermutationInvariant polynomial) :
    polynomial.linearY = 0 := by
  have h := hInvariant.flipYInvariant basisY
  norm_num [evaluate, flipY, basisY] at h
  linarith

/-- Reflection invariance removes the third linear coefficient. -/
theorem invariant_linear_z_zero
    (polynomial : QuadraticPolynomial3)
    (hInvariant : SignedPermutationInvariant polynomial) :
    polynomial.linearZ = 0 := by
  have h := hInvariant.flipZInvariant basisZ
  norm_num [evaluate, flipZ, basisZ] at h
  linarith

/-- Reflection invariance removes the `xy` monomial. -/
theorem invariant_xy_zero
    (polynomial : QuadraticPolynomial3)
    (hInvariant : SignedPermutationInvariant polynomial) :
    polynomial.xy = 0 := by
  have h := hInvariant.flipXInvariant xyVector
  have hLinear := invariant_linear_x_zero polynomial hInvariant
  norm_num [evaluate, flipX, xyVector] at h
  linarith

/-- Reflection invariance removes the `xz` monomial. -/
theorem invariant_xz_zero
    (polynomial : QuadraticPolynomial3)
    (hInvariant : SignedPermutationInvariant polynomial) :
    polynomial.xz = 0 := by
  have h := hInvariant.flipXInvariant xzVector
  have hLinear := invariant_linear_x_zero polynomial hInvariant
  norm_num [evaluate, flipX, xzVector] at h
  linarith

/-- Reflection invariance removes the `yz` monomial. -/
theorem invariant_yz_zero
    (polynomial : QuadraticPolynomial3)
    (hInvariant : SignedPermutationInvariant polynomial) :
    polynomial.yz = 0 := by
  have h := hInvariant.flipYInvariant yzVector
  have hLinear := invariant_linear_y_zero polynomial hInvariant
  norm_num [evaluate, flipY, yzVector] at h
  linarith

/-- Permutation invariance equates the first two quadratic coefficients. -/
theorem invariant_xx_eq_yy
    (polynomial : QuadraticPolynomial3)
    (hInvariant : SignedPermutationInvariant polynomial) :
    polynomial.xx = polynomial.yy := by
  have h := hInvariant.swapXYInvariant basisX
  have hLinearX := invariant_linear_x_zero polynomial hInvariant
  have hLinearY := invariant_linear_y_zero polynomial hInvariant
  norm_num [evaluate, swapXY, basisX, basisY] at h
  linarith

/-- Permutation invariance equates the final two quadratic coefficients. -/
theorem invariant_yy_eq_zz
    (polynomial : QuadraticPolynomial3)
    (hInvariant : SignedPermutationInvariant polynomial) :
    polynomial.yy = polynomial.zz := by
  have h := hInvariant.swapYZInvariant basisY
  have hLinearY := invariant_linear_y_zero polynomial hInvariant
  have hLinearZ := invariant_linear_z_zero polynomial hInvariant
  norm_num [evaluate, swapYZ, basisY, basisZ] at h
  linarith

/-- Canonical radial quadratic polynomial. -/
def radialQuadratic
    (constant coefficient : ℝ) : QuadraticPolynomial3 :=
  { constant := constant
    linearX := 0
    linearY := 0
    linearZ := 0
    xx := coefficient
    yy := coefficient
    zz := coefficient
    xy := 0
    xz := 0
    yz := 0 }

/-- Every signed-permutation-invariant quadratic polynomial is radial. -/
theorem invariant_quadratic_is_radial
    (polynomial : QuadraticPolynomial3)
    (hInvariant : SignedPermutationInvariant polynomial) :
    polynomial = radialQuadratic polynomial.constant polynomial.xx := by
  have hLinearX := invariant_linear_x_zero polynomial hInvariant
  have hLinearY := invariant_linear_y_zero polynomial hInvariant
  have hLinearZ := invariant_linear_z_zero polynomial hInvariant
  have hXY := invariant_xy_zero polynomial hInvariant
  have hXZ := invariant_xz_zero polynomial hInvariant
  have hYZ := invariant_yz_zero polynomial hInvariant
  have hYY : polynomial.yy = polynomial.xx :=
    (invariant_xx_eq_yy polynomial hInvariant).symm
  have hZZ : polynomial.zz = polynomial.xx := by
    calc
      polynomial.zz = polynomial.yy :=
        (invariant_yy_eq_zz polynomial hInvariant).symm
      _ = polynomial.xx := hYY
  apply QuadraticPolynomial3.ext
  · rfl
  · exact hLinearX
  · exact hLinearY
  · exact hLinearZ
  · rfl
  · exact hYY
  · exact hZZ
  · exact hXY
  · exact hXZ
  · exact hYZ

/-- The radial quadratic polynomial is invariant. -/
theorem radial_quadratic_invariant
    (constant coefficient : ℝ) :
    SignedPermutationInvariant (radialQuadratic constant coefficient) := by
  constructor <;>
    intro vector <;>
    simp [evaluate, radialQuadratic, flipX, flipY, flipZ,
      swapXY, swapYZ] <;>
    ring

/-- Squared Euclidean norm. -/
def normSquared (vector : Vector3) : ℝ :=
  vector.x ^ 2 + vector.y ^ 2 + vector.z ^ 2

/-- Functional form of the classification. -/
theorem invariant_quadratic_evaluation
    (polynomial : QuadraticPolynomial3)
    (hInvariant : SignedPermutationInvariant polynomial)
    (vector : Vector3) :
    evaluate polynomial vector =
      polynomial.constant + polynomial.xx * normSquared vector := by
  rw [invariant_quadratic_is_radial polynomial hInvariant]
  unfold evaluate radialQuadratic normSquared
  ring

/-- The pair `(constant, radial coefficient)` is uniquely determined. -/
theorem radial_coefficients_unique
    (firstConstant firstCoefficient secondConstant secondCoefficient : ℝ)
    (hEqual :
      ∀ vector : Vector3,
        evaluate (radialQuadratic firstConstant firstCoefficient) vector =
          evaluate (radialQuadratic secondConstant secondCoefficient) vector) :
    firstConstant = secondConstant /\
      firstCoefficient = secondCoefficient := by
  have hZero := hEqual zeroVector
  have hBasis := hEqual basisX
  norm_num [evaluate, radialQuadratic, zeroVector, basisX] at hZero hBasis
  exact ⟨hZero, by linarith⟩

/--
This is a proved finite fragment of Lemma 3.  It classifies degree-at-most-two
scalar invariants for the local vector representation.  It does not imply that
an arbitrary smooth invariant is polynomial; the exponential counterexample in
Program P.E-J rules out that stronger statement.
-/
structure QuadraticInvariantPhysicalStatus where
  actualJetRepresentationConstructed : Prop
  signedPermutationSubgroupEmbedded : Prop
  fullO3ActionConstructed : Prop
  polynomialDegreeBoundDerived : Prop
  quadraticInvariantClassificationApplied : Prop
  higherDegreeInvariantRingClassified : Prop
  smoothInvariantUpgradeProved : Prop


def quadraticInvariantPhysicalClosure
    (s : QuadraticInvariantPhysicalStatus) : Prop :=
  s.actualJetRepresentationConstructed /\
  s.signedPermutationSubgroupEmbedded /\
  s.fullO3ActionConstructed /\
  s.polynomialDegreeBoundDerived /\
  s.quadraticInvariantClassificationApplied /\
  s.higherDegreeInvariantRingClassified /\
  s.smoothInvariantUpgradeProved

end P0EFTJanusQuadraticJetInvariantClassification
end JanusFormal
