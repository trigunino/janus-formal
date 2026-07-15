import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootFrechetSylvester

/-!
Explicit inversion of the Sylvester operator on a strictly positive real
diagonal square-root chart.  Entrywise, the inverse divides the `(i,j)`
component by `lambda_i + lambda_j`; strict positivity makes every denominator
nonzero.

This is a local diagonal-chart result.  It does not construct, or assert the
existence of, a global Lorentzian principal square-root branch.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveDiagonalSylvesterInverse

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions
open P0EFTJanusMatrixSquareRootFrechetSylvester

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4

abbrev Spectrum4 := Fin 4 -> Real

/-- Spectra on which every diagonal Sylvester denominator is positive. -/
def positiveDiagonalDomain : Set Spectrum4 :=
  { spectrum | ∀ i, 0 < spectrum i }

/-- Strict positivity is genuinely an open finite-dimensional chart. -/
theorem positiveDiagonalDomain_isOpen : IsOpen positiveDiagonalDomain := by
  rw [show positiveDiagonalDomain =
      ⋂ i : Fin 4, { spectrum : Spectrum4 | 0 < spectrum i } by
    ext spectrum
    simp [positiveDiagonalDomain]]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_Ioi.preimage (continuous_apply i)

/-- The open positive diagonal chart for the four square-root eigenvalues. -/
def PositiveDiagonalSpectrum :=
  { spectrum : Spectrum4 // spectrum ∈ positiveDiagonalDomain }

theorem denominator_pos (spectrum : PositiveDiagonalSpectrum) (i j : Fin 4) :
    0 < spectrum.1 i + spectrum.1 j :=
  add_pos (spectrum.2 i) (spectrum.2 j)

theorem denominator_ne_zero
    (spectrum : PositiveDiagonalSpectrum) (i j : Fin 4) :
    spectrum.1 i + spectrum.1 j ≠ 0 :=
  ne_of_gt (denominator_pos spectrum i j)

/-- Entrywise algebraic inverse of the diagonal Sylvester operator. -/
def diagonalSylvesterInverseLinearMap
    (spectrum : PositiveDiagonalSpectrum) : Matrix4 →ₗ[Real] Matrix4 where
  toFun variation i j :=
    variation i j / (spectrum.1 i + spectrum.1 j)
  map_add' first second := by
    ext i j
    exact add_div (first i j) (second i j) _
  map_smul' scalar variation := by
    ext i j
    simp [smul_eq_mul, mul_div_assoc]

/-- The entrywise inverse is continuous because the matrix space is finite
dimensional. -/
def diagonalSylvesterInverse
    (spectrum : PositiveDiagonalSpectrum) : Matrix4 →L[Real] Matrix4 :=
  LinearMap.toContinuousLinearMap
    (diagonalSylvesterInverseLinearMap spectrum)

@[simp]
theorem diagonalSylvesterInverse_apply
    (spectrum : PositiveDiagonalSpectrum) (variation : Matrix4) (i j : Fin 4) :
    diagonalSylvesterInverse spectrum variation i j =
      variation i j / (spectrum.1 i + spectrum.1 j) :=
  rfl

theorem diagonal_sylvester_entry
    (spectrum : Spectrum4) (variation : Matrix4) (i j : Fin 4) :
    sylvesterOperator (Matrix.diagonal spectrum) variation i j =
      (spectrum i + spectrum j) * variation i j := by
  simp only [sylvesterOperator_apply, Matrix.add_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem diagonalSylvesterInverse_left
    (spectrum : PositiveDiagonalSpectrum) (variation : Matrix4) :
    diagonalSylvesterInverse spectrum
        (sylvesterOperator (Matrix.diagonal spectrum.1) variation) =
      variation := by
  ext i j
  rw [diagonalSylvesterInverse_apply,
    diagonal_sylvester_entry spectrum.1 variation i j]
  exact mul_div_cancel_left₀
    (variation i j) (denominator_ne_zero spectrum i j)

theorem diagonalSylvesterInverse_right
    (spectrum : PositiveDiagonalSpectrum) (variation : Matrix4) :
    sylvesterOperator (Matrix.diagonal spectrum.1)
        (diagonalSylvesterInverse spectrum variation) =
      variation := by
  ext i j
  rw [diagonal_sylvester_entry spectrum.1
    (diagonalSylvesterInverse spectrum variation) i j,
    diagonalSylvesterInverse_apply]
  exact mul_div_cancel₀
    (variation i j) (denominator_ne_zero spectrum i j)

/-- The positive diagonal chart supplies the previously abstract two-sided
Sylvester inverse witness. -/
def positiveDiagonalSylvesterInverseWitness
    (spectrum : PositiveDiagonalSpectrum) :
    SylvesterInverseWitness (Matrix.diagonal spectrum.1) where
  inverse := diagonalSylvesterInverse spectrum
  leftInverse := diagonalSylvesterInverse_left spectrum
  rightInverse := diagonalSylvesterInverse_right spectrum

/-- On a differentiable square-root selection whose value at the base point
is positive diagonal, the Fréchet derivative is the explicit entrywise
Sylvester inverse composed with the target derivative. -/
theorem positiveDiagonal_squareRoot_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {root target : E → Matrix4}
    {targetDerivative : E →L[Real] Matrix4}
    {point : E}
    (spectrum : PositiveDiagonalSpectrum)
    (hValue : root point = Matrix.diagonal spectrum.1)
    (hRoot : DifferentiableAt Real root point)
    (hTarget : HasFDerivAt target targetDerivative point)
    (hSquare : forall x, squareMap (root x) = target x) :
    HasFDerivAt root
      ((diagonalSylvesterInverse spectrum).comp targetDerivative) point := by
  let witness : SylvesterInverseWitness (root point) := {
    inverse := diagonalSylvesterInverse spectrum
    leftInverse := fun variation => by
      rw [hValue]
      exact diagonalSylvesterInverse_left spectrum variation
    rightInverse := fun variation => by
      rw [hValue]
      exact diagonalSylvesterInverse_right spectrum variation }
  simpa [witness] using
    differentiable_squareRoot_hasFDerivAt witness hRoot hTarget hSquare

theorem positiveDiagonal_squareRoot_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {root target : E → Matrix4}
    {targetDerivative : E →L[Real] Matrix4}
    {point : E}
    (spectrum : PositiveDiagonalSpectrum)
    (hValue : root point = Matrix.diagonal spectrum.1)
    (hRoot : DifferentiableAt Real root point)
    (hTarget : HasFDerivAt target targetDerivative point)
    (hSquare : forall x, squareMap (root x) = target x) :
    fderiv Real root point =
      (diagonalSylvesterInverse spectrum).comp targetDerivative :=
  (positiveDiagonal_squareRoot_hasFDerivAt spectrum hValue hRoot hTarget
    hSquare).fderiv

end

end P0EFTJanusPositiveDiagonalSylvesterInverse
end JanusFormal
