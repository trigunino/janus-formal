import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzJordanIndependentMetricRoot

/-!
# Lorentzian no-go for diagonal tensor-pairing definiteness

The existing Lorentz-Jordan witness gives a nonzero symmetric covariant
tensor whose raised endomorphism is nonzero nilpotent.  Consequently the
quadratic trace pairing `tr((g⁻¹h)²)` vanishes.  Thus diagonal definiteness
cannot follow from Lorentzian linear algebra alone; the geometric dual must
be proved injective by bilinear separation instead.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMetricDiagonalDefinitenessNoGo4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusLorentzJordanIndependentMetricRoot

/-- Symmetric covariant tensor associated with the nonzero nilpotent
Lorentz-self-adjoint endomorphism. -/
def lorentzNullCovariantTensor : Matrix2 :=
  plusMetric * jordanNilpotent

theorem lorentzNullCovariantTensor_symmetric :
    lorentzNullCovariantTensor.transpose =
      lorentzNullCovariantTensor := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lorentzNullCovariantTensor, plusMetric, jordanNilpotent,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

theorem lorentzNullCovariantTensor_ne_zero :
    lorentzNullCovariantTensor ≠ 0 := by
  intro hZero
  have hEntry :=
    congrArg (fun matrix : Matrix2 => matrix 1 1) hZero
  norm_num [lorentzNullCovariantTensor, plusMetric, jordanNilpotent,
    Matrix.mul_apply, Fin.sum_univ_two] at hEntry

theorem lorentzNullCovariantTensor_raised :
    plusMetricInverse * lorentzNullCovariantTensor =
      jordanNilpotent := by
  rw [lorentzNullCovariantTensor, ← Matrix.mul_assoc,
    plusMetricInverse_mul_plusMetric]
  simp

theorem lorentzNullCovariantTensor_trace_square_zero :
    Matrix.trace
      ((plusMetricInverse * lorentzNullCovariantTensor) *
        (plusMetricInverse * lorentzNullCovariantTensor)) = 0 := by
  rw [lorentzNullCovariantTensor_raised, jordanNilpotent_square]
  simp

/-- Bilinear trace pairing induced by the same Lorentz metric. -/
def lorentzSymmetricTracePairing (first second : Matrix2) : Real :=
  Matrix.trace
    ((plusMetricInverse * first) * (plusMetricInverse * second))

private def symmetricTest00 : Matrix2 := !![1, 0; 0, 0]
private def symmetricTest01 : Matrix2 := !![0, 1; 1, 0]
private def symmetricTest11 : Matrix2 := !![0, 0; 0, 1]

private theorem symmetricTest00_symmetric :
    symmetricTest00.transpose = symmetricTest00 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricTest00, Matrix.transpose_apply]

private theorem symmetricTest01_symmetric :
    symmetricTest01.transpose = symmetricTest01 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricTest01, Matrix.transpose_apply]

private theorem symmetricTest11_symmetric :
    symmetricTest11.transpose = symmetricTest11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [symmetricTest11, Matrix.transpose_apply]

/-- The Lorentzian trace pairing is bilinearly nondegenerate on symmetric
covariant tensors even though its diagonal quadratic form has null vectors. -/
theorem lorentzSymmetricTracePairing_separates
    (tensor : Matrix2)
    (hSymmetric : tensor.transpose = tensor)
    (hOrthogonal :
      ∀ test : Matrix2, test.transpose = test →
        lorentzSymmetricTracePairing tensor test = 0) :
    tensor = 0 := by
  have h00 := hOrthogonal symmetricTest00 symmetricTest00_symmetric
  have h01 := hOrthogonal symmetricTest01 symmetricTest01_symmetric
  have h11 := hOrthogonal symmetricTest11 symmetricTest11_symmetric
  have hOffDiagonal : tensor 1 0 = tensor 0 1 := by
    have := congrArg (fun matrix : Matrix2 => matrix 0 1) hSymmetric
    simpa [Matrix.transpose_apply] using this
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [lorentzSymmetricTracePairing, plusMetricInverse,
      symmetricTest11, Matrix.trace, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h11
    exact h11
  · norm_num [lorentzSymmetricTracePairing, plusMetricInverse,
      symmetricTest01, Matrix.trace, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, hOffDiagonal] at h01
    simpa using h01
  · norm_num [lorentzSymmetricTracePairing, plusMetricInverse,
      symmetricTest01, Matrix.trace, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two, hOffDiagonal] at h01
    simpa using hOffDiagonal.trans h01
  · norm_num [lorentzSymmetricTracePairing, plusMetricInverse,
      symmetricTest00, Matrix.trace, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h00
    exact h00

/-- Auditable obstruction to using diagonal definiteness as the generic
Lorentzian nondegeneracy proof. -/
structure ThroatMetricDiagonalDefinitenessNoGoCertificate4D : Prop where
  symmetric :
    lorentzNullCovariantTensor.transpose =
      lorentzNullCovariantTensor
  nonzero :
    lorentzNullCovariantTensor ≠ 0
  traceSquareZero :
    Matrix.trace
      ((plusMetricInverse * lorentzNullCovariantTensor) *
        (plusMetricInverse * lorentzNullCovariantTensor)) = 0
  bilinearSeparation :
    ∀ tensor : Matrix2,
      tensor.transpose = tensor →
      (∀ test : Matrix2, test.transpose = test →
        lorentzSymmetricTracePairing tensor test = 0) →
      tensor = 0

def throatMetricDiagonalDefinitenessNoGoCertificate4D :
    ThroatMetricDiagonalDefinitenessNoGoCertificate4D where
  symmetric := lorentzNullCovariantTensor_symmetric
  nonzero := lorentzNullCovariantTensor_ne_zero
  traceSquareZero := lorentzNullCovariantTensor_trace_square_zero
  bilinearSeparation := lorentzSymmetricTracePairing_separates

end
end P0EFTJanusProgramPThroatMetricDiagonalDefinitenessNoGo4D
end JanusFormal
