import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedFLRWSecondaryConstraint

/-!
# Nonlinear canonical Poisson Jacobi identity at symmetric second-jet level

The previous finite-site gate proves Jacobi only for affine functionals with
constant differentials.  Here a first derivative is an arbitrary four-vector
and a Hessian is an explicit symmetric `4 x 4` matrix.  The differential of a
canonical Poisson bracket is constructed from both Hessians, and the cyclic
Jacobi sum is proved identically for arbitrary first and symmetric second
jets.  A quadratic coordinate functional is also given with an actual
directional derivative, so the second-jet algebra is non-vacuous.

This is finite-dimensional local jet algebra.  It does not prove that the
Candidate-A constraints have the supplied Hessians on their singular domains,
nor functional-analytic Jacobi, continuum ADM closure, shift closure, or the
hypersurface-deformation algebra.
-/

namespace JanusFormal
namespace P0EFTJanusNonlinearCanonicalPoissonJetJacobi

set_option autoImplicit false

noncomputable section

open P0EFTJanusReducedFLRWSecondaryConstraint

abbrev Index4 := Fin 4
abbrev Vector4 := Index4 → ℝ
abbrev Matrix4 := Matrix Index4 Index4 ℝ

/-- Ten independent entries of a symmetric four-dimensional Hessian. -/
structure SymmetricHessian4 where
  h00 : ℝ
  h01 : ℝ
  h02 : ℝ
  h03 : ℝ
  h11 : ℝ
  h12 : ℝ
  h13 : ℝ
  h22 : ℝ
  h23 : ℝ
  h33 : ℝ

/-- Matrix represented by the ten symmetric Hessian entries. -/
def hessianMatrix (hessian : SymmetricHessian4) : Matrix4 :=
  ![![hessian.h00, hessian.h01, hessian.h02, hessian.h03],
    ![hessian.h01, hessian.h11, hessian.h12, hessian.h13],
    ![hessian.h02, hessian.h12, hessian.h22, hessian.h23],
    ![hessian.h03, hessian.h13, hessian.h23, hessian.h33]]

theorem hessianMatrix_symmetric (hessian : SymmetricHessian4) :
    (hessianMatrix hessian).transpose = hessianMatrix hessian := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Hessian action on a coordinate direction. -/
def hessianAction (hessian : SymmetricHessian4) (direction : Vector4) :
    Vector4 :=
  ![hessian.h00 * direction 0 + hessian.h01 * direction 1 +
      hessian.h02 * direction 2 + hessian.h03 * direction 3,
    hessian.h01 * direction 0 + hessian.h11 * direction 1 +
      hessian.h12 * direction 2 + hessian.h13 * direction 3,
    hessian.h02 * direction 0 + hessian.h12 * direction 1 +
      hessian.h22 * direction 2 + hessian.h23 * direction 3,
    hessian.h03 * direction 0 + hessian.h13 * direction 1 +
      hessian.h23 * direction 2 + hessian.h33 * direction 3]

/-- Canonical symplectic sharp map in `(aPlus,pPlus,aMinus,pMinus)` order. -/
def symplecticSharp (covector : Vector4) : Vector4 :=
  ![covector 1, -covector 0, covector 3, -covector 2]

/-- Canonical Poisson pairing of coordinate first derivatives. -/
def poisson (first second : Vector4) : ℝ :=
  first 0 * second 1 - first 1 * second 0 +
    first 2 * second 3 - first 3 * second 2

theorem poisson_antisymmetric (first second : Vector4) :
    poisson first second = -poisson second first := by
  simp only [poisson]
  ring

theorem poisson_self (first : Vector4) : poisson first first = 0 := by
  simp only [poisson]
  ring

/-- Convert the existing reduced canonical covector to the common vector
ordering used by this gate. -/
def covectorVector (covector : CanonicalCovector) : Vector4 :=
  ![covector.aPlus, covector.pPlus, covector.aMinus, covector.pMinus]

theorem poisson_covectorVector_eq_canonicalPoisson
    (first second : CanonicalCovector) :
    poisson (covectorVector first) (covectorVector second) =
      canonicalPoisson first second := by
  rfl

/-- First derivative of `{f,g}` from the two symmetric Hessians and first
derivatives: `H_f J dg - H_g J df`. -/
def bracketDifferential
    (firstHessian secondHessian : SymmetricHessian4)
    (firstDifferential secondDifferential : Vector4) : Vector4 :=
  hessianAction firstHessian (symplecticSharp secondDifferential) -
    hessianAction secondHessian (symplecticSharp firstDifferential)

/-- The canonical Jacobi identity for arbitrary first and symmetric second
jets.  Unlike the affine result, all three Hessians may be nonzero. -/
theorem nonlinear_poisson_secondJet_jacobi
    (firstHessian secondHessian thirdHessian : SymmetricHessian4)
    (firstDifferential secondDifferential thirdDifferential : Vector4) :
    poisson firstDifferential
        (bracketDifferential secondHessian thirdHessian
          secondDifferential thirdDifferential) +
      poisson secondDifferential
        (bracketDifferential thirdHessian firstHessian
          thirdDifferential firstDifferential) +
      poisson thirdDifferential
        (bracketDifferential firstHessian secondHessian
          firstDifferential secondDifferential) = 0 := by
  simp [poisson, bracketDifferential, hessianAction, symplecticSharp]
  ring

/-- Coordinate dot product used for quadratic functionals. -/
def coordinatePairing (first second : Vector4) : ℝ :=
  ∑ index, first index * second index

/-- A genuine nonlinear coordinate functional with the supplied symmetric
Hessian. -/
def quadraticFunctional
    (hessian : SymmetricHessian4) (linear : Vector4) (constant : ℝ)
    (point : Vector4) : ℝ :=
  constant + coordinatePairing linear point +
    (1 / 2 : ℝ) * coordinatePairing point (hessianAction hessian point)

/-- Its displayed coordinate gradient. -/
def quadraticGradient
    (hessian : SymmetricHessian4) (linear point : Vector4) : Vector4 :=
  linear + hessianAction hessian point

/-- Affine coordinate line through a four-vector. -/
def vectorLine (point direction : Vector4) (epsilon : ℝ) : Vector4 :=
  fun index => point index + epsilon * direction index

private theorem coordinate_line_hasDerivAt
    (base variation : ℝ) :
    HasDerivAt (fun epsilon : ℝ => base + epsilon * variation) variation 0 := by
  simpa using (hasDerivAt_id (x := (0 : ℝ))).mul_const variation
    |>.const_add base

private theorem triple_product_line_hasDerivAt
    (coefficient first firstVariation second secondVariation : ℝ) :
    HasDerivAt
      (fun epsilon : ℝ => coefficient *
        (first + epsilon * firstVariation) *
        (second + epsilon * secondVariation))
      (coefficient * firstVariation * second +
        coefficient * first * secondVariation) 0 := by
  have hFirst := coordinate_line_hasDerivAt first firstVariation
  have hSecond := coordinate_line_hasDerivAt second secondVariation
  have hProduct := (hFirst.const_mul coefficient).mul hSecond
  refine (hProduct.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    rfl
  · simp

private theorem affine_four_line_hasDerivAt
    (constant coefficient0 coefficient1 coefficient2 coefficient3
      base0 base1 base2 base3 variation0 variation1 variation2 variation3 : ℝ) :
    HasDerivAt
      (fun epsilon : ℝ => constant +
        coefficient0 * (base0 + epsilon * variation0) +
        coefficient1 * (base1 + epsilon * variation1) +
        coefficient2 * (base2 + epsilon * variation2) +
        coefficient3 * (base3 + epsilon * variation3))
      (coefficient0 * variation0 + coefficient1 * variation1 +
        coefficient2 * variation2 + coefficient3 * variation3) 0 := by
  have h0 := (coordinate_line_hasDerivAt base0 variation0).const_mul coefficient0
  have h1 := (coordinate_line_hasDerivAt base1 variation1).const_mul coefficient1
  have h2 := (coordinate_line_hasDerivAt base2 variation2).const_mul coefficient2
  have h3 := (coordinate_line_hasDerivAt base3 variation3).const_mul coefficient3
  have hRaw := (((h0.add h1).add h2).add h3).const_add constant
  refine (hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp
    ring
  · simp

/-- The quadratic functional has the genuine directional derivative given by
its gradient, for every affine coordinate variation. -/
theorem quadraticFunctional_vectorLine_hasDerivAt
    (hessian : SymmetricHessian4) (linear : Vector4) (constant : ℝ)
    (point direction : Vector4) :
    HasDerivAt
      (fun epsilon => quadraticFunctional hessian linear constant
        (vectorLine point direction epsilon))
      (coordinatePairing (quadraticGradient hessian linear point) direction) 0 := by
  have hLinear : HasDerivAt
      (fun epsilon : ℝ => ∑ index : Index4,
        linear index * (point index + epsilon * direction index))
      (∑ index : Index4, linear index * direction index) 0 := by
    apply HasDerivAt.fun_sum
    intro index _
    simpa using (coordinate_line_hasDerivAt (point index) (direction index)).const_mul
      (linear index)
  have hQuadraticRaw : HasDerivAt
      (fun epsilon : ℝ => ∑ first : Index4, ∑ second : Index4,
        hessianMatrix hessian first second *
          (point first + epsilon * direction first) *
          (point second + epsilon * direction second))
      (∑ first : Index4, ∑ second : Index4,
        (hessianMatrix hessian first second * direction first * point second +
          hessianMatrix hessian first second * point first * direction second)) 0 := by
    apply HasDerivAt.fun_sum
    intro first _
    apply HasDerivAt.fun_sum
    intro second _
    exact triple_product_line_hasDerivAt
      (hessianMatrix hessian first second)
      (point first) (direction first) (point second) (direction second)
  have hQuadratic := hQuadraticRaw.const_mul (1 / 2 : ℝ)
  have hRaw := (hLinear.add hQuadratic).const_add constant
  refine (hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [quadraticFunctional, coordinatePairing, vectorLine, hessianAction,
      hessianMatrix, Fin.sum_univ_four]
    ring
  · simp [quadraticGradient, coordinatePairing, hessianAction, hessianMatrix,
      Fin.sum_univ_four]
    ring

/-- The quadratic gradient itself has the supplied constant Hessian as its
actual derivative. -/
theorem quadraticGradient_vectorLine_hasDerivAt
    (hessian : SymmetricHessian4) (linear point direction : Vector4) :
    HasDerivAt
      (fun epsilon => quadraticGradient hessian linear
        (vectorLine point direction epsilon))
      (hessianAction hessian direction) 0 := by
  rw [hasDerivAt_pi]
  intro index
  fin_cases index
  · simpa [quadraticGradient, hessianAction, vectorLine] using
      affine_four_line_hasDerivAt 0
        hessian.h00 hessian.h01 hessian.h02 hessian.h03
        (point 0) (point 1) (point 2) (point 3)
        (direction 0) (direction 1) (direction 2) (direction 3)
  · simpa [quadraticGradient, hessianAction, vectorLine] using
      affine_four_line_hasDerivAt 0
        hessian.h01 hessian.h11 hessian.h12 hessian.h13
        (point 0) (point 1) (point 2) (point 3)
        (direction 0) (direction 1) (direction 2) (direction 3)
  · simpa [quadraticGradient, hessianAction, vectorLine] using
      affine_four_line_hasDerivAt 0
        hessian.h02 hessian.h12 hessian.h22 hessian.h23
        (point 0) (point 1) (point 2) (point 3)
        (direction 0) (direction 1) (direction 2) (direction 3)
  · simpa [quadraticGradient, hessianAction, vectorLine] using
      affine_four_line_hasDerivAt 0
        hessian.h03 hessian.h13 hessian.h23 hessian.h33
        (point 0) (point 1) (point 2) (point 3)
        (direction 0) (direction 1) (direction 2) (direction 3)

private theorem poisson_curve_hasDerivAt
    {first second : ℝ → Vector4}
    {firstDerivative secondDerivative : Vector4} {point : ℝ}
    (hFirst : HasDerivAt first firstDerivative point)
    (hSecond : HasDerivAt second secondDerivative point) :
    HasDerivAt (fun epsilon => poisson (first epsilon) (second epsilon))
      (poisson firstDerivative (second point) +
        poisson (first point) secondDerivative) point := by
  have hFirstAt := hasDerivAt_pi.mp hFirst
  have hSecondAt := hasDerivAt_pi.mp hSecond
  have hRaw :=
    ((((hFirstAt 0).mul (hSecondAt 1)).sub
      ((hFirstAt 1).mul (hSecondAt 0))).add
      ((hFirstAt 2).mul (hSecondAt 3))).sub
      ((hFirstAt 3).mul (hSecondAt 2))
  refine (hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)).congr_deriv ?_
  · intro epsilon
    simp [poisson]
  · simp [poisson]
    ring

/-- The bracket differential used by the nonlinear Jacobi theorem is the
actual derivative of the Poisson bracket of two genuine quadratic
functionals. -/
theorem quadraticPoisson_vectorLine_hasDerivAt
    (firstHessian secondHessian : SymmetricHessian4)
    (firstLinear secondLinear point direction : Vector4) :
    HasDerivAt
      (fun epsilon => poisson
        (quadraticGradient firstHessian firstLinear
          (vectorLine point direction epsilon))
        (quadraticGradient secondHessian secondLinear
          (vectorLine point direction epsilon)))
      (coordinatePairing
        (bracketDifferential firstHessian secondHessian
          (quadraticGradient firstHessian firstLinear point)
          (quadraticGradient secondHessian secondLinear point)) direction) 0 := by
  have hFirst := quadraticGradient_vectorLine_hasDerivAt
    firstHessian firstLinear point direction
  have hSecond := quadraticGradient_vectorLine_hasDerivAt
    secondHessian secondLinear point direction
  have hBracket := poisson_curve_hasDerivAt hFirst hSecond
  refine hBracket.congr_deriv ?_
  simp [poisson, coordinatePairing, bracketDifferential, quadraticGradient,
    hessianAction, symplecticSharp, vectorLine, Fin.sum_univ_four]
  ring

/-- A nonzero-Hessian witness shows that the Jacobi theorem is not merely the
affine constant-differential case. -/
def nonlinearHessianWitness : SymmetricHessian4 where
  h00 := 1
  h01 := 2
  h02 := 0
  h03 := 0
  h11 := 3
  h12 := 0
  h13 := 0
  h22 := 4
  h23 := 5
  h33 := 6

theorem nonlinearHessianWitness_nonzero :
    hessianMatrix nonlinearHessianWitness 0 0 ≠ 0 := by
  norm_num [hessianMatrix, nonlinearHessianWitness]

end

end P0EFTJanusNonlinearCanonicalPoissonJetJacobi
end JanusFormal
