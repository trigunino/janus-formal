import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableRelativeRoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalSylvesterInverse

/-!
# Sylvester inversion for positive diagonalizable relative roots

The explicit inverse on a positive diagonal spectrum is transported through
the supplied eigenbasis.  This proves Sylvester regularity for every explicit
positive diagonalizable presentation, without asserting global gluing.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveDiagonalizableSylvesterInverse4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveDiagonalSylvesterInverse
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Matrix4

/-- The strictly positive spectrum of the selected diagonal root. -/
def positiveRootSpectrum
    (data : PositiveDiagonalizableRelativeMatrix) :
    PositiveDiagonalSpectrum :=
  ⟨positiveSimilarityRootSpectrum data,
    positiveSimilarityRootSpectrum_pos data⟩

/-- The diagonal Sylvester inverse transported through the supplied
eigenbasis. -/
def positiveDiagonalizableSylvesterInverse
    (data : PositiveDiagonalizableRelativeMatrix) (target : Matrix4) : Matrix4 :=
  data.eigenbasis *
    diagonalSylvesterInverse (positiveRootSpectrum data)
      (data.eigenbasisInv * target * data.eigenbasis) *
    data.eigenbasisInv

theorem positiveDiagonalizableSylvesterInverse_left
    (data : PositiveDiagonalizableRelativeMatrix) (variation : Matrix4) :
    positiveDiagonalizableSylvesterInverse data
        (sylvesterOperator (positiveSimilarityRoot data) variation) =
      variation := by
  have hConjugated :
      data.eigenbasisInv *
          sylvesterOperator (positiveSimilarityRoot data) variation *
          data.eigenbasis =
        sylvesterOperator
          (Matrix.diagonal (positiveSimilarityRootSpectrum data))
          (data.eigenbasisInv * variation * data.eigenbasis) := by
    rw [sylvesterOperator_apply, sylvesterOperator_apply]
    unfold positiveSimilarityRoot positiveSimilarityDiagonalRoot
    calc
      data.eigenbasisInv *
          ((data.eigenbasis *
              Matrix.diagonal (positiveSimilarityRootSpectrum data) *
              data.eigenbasisInv) * variation +
            variation *
              (data.eigenbasis *
                Matrix.diagonal (positiveSimilarityRootSpectrum data) *
                data.eigenbasisInv)) * data.eigenbasis =
        (data.eigenbasisInv * data.eigenbasis) *
            Matrix.diagonal (positiveSimilarityRootSpectrum data) *
            (data.eigenbasisInv * variation * data.eigenbasis) +
          (data.eigenbasisInv * variation * data.eigenbasis) *
            Matrix.diagonal (positiveSimilarityRootSpectrum data) *
            (data.eigenbasisInv * data.eigenbasis) := by noncomm_ring
      _ = Matrix.diagonal (positiveSimilarityRootSpectrum data) *
            (data.eigenbasisInv * variation * data.eigenbasis) +
          (data.eigenbasisInv * variation * data.eigenbasis) *
            Matrix.diagonal (positiveSimilarityRootSpectrum data) := by
        rw [data.inv_mul_basis]
        simp
  unfold positiveDiagonalizableSylvesterInverse
  rw [hConjugated]
  have hDiagonalInverse :
      diagonalSylvesterInverse (positiveRootSpectrum data)
          (sylvesterOperator
            (Matrix.diagonal (positiveSimilarityRootSpectrum data))
            (data.eigenbasisInv * variation * data.eigenbasis)) =
        data.eigenbasisInv * variation * data.eigenbasis := by
    simpa [positiveRootSpectrum] using
      diagonalSylvesterInverse_left (positiveRootSpectrum data)
        (data.eigenbasisInv * variation * data.eigenbasis)
  rw [hDiagonalInverse]
  calc
    data.eigenbasis *
          (data.eigenbasisInv * variation * data.eigenbasis) *
          data.eigenbasisInv =
      (data.eigenbasis * data.eigenbasisInv) * variation *
        (data.eigenbasis * data.eigenbasisInv) := by noncomm_ring
    _ = variation := by rw [data.basis_mul_inv]; simp

theorem positiveDiagonalizableSylvesterInverse_right
    (data : PositiveDiagonalizableRelativeMatrix) (target : Matrix4) :
    sylvesterOperator (positiveSimilarityRoot data)
        (positiveDiagonalizableSylvesterInverse data target) =
      target := by
  have hConjugated (variation : Matrix4) :
      sylvesterOperator (positiveSimilarityRoot data)
          (data.eigenbasis * variation * data.eigenbasisInv) =
        data.eigenbasis *
          sylvesterOperator
            (Matrix.diagonal (positiveSimilarityRootSpectrum data)) variation *
          data.eigenbasisInv := by
    rw [sylvesterOperator_apply, sylvesterOperator_apply]
    unfold positiveSimilarityRoot positiveSimilarityDiagonalRoot
    calc
      (data.eigenbasis *
            Matrix.diagonal (positiveSimilarityRootSpectrum data) *
            data.eigenbasisInv) *
            (data.eigenbasis * variation * data.eigenbasisInv) +
          (data.eigenbasis * variation * data.eigenbasisInv) *
            (data.eigenbasis *
              Matrix.diagonal (positiveSimilarityRootSpectrum data) *
              data.eigenbasisInv) =
        data.eigenbasis *
          (Matrix.diagonal (positiveSimilarityRootSpectrum data) *
              (data.eigenbasisInv * data.eigenbasis) * variation +
            variation * (data.eigenbasisInv * data.eigenbasis) *
              Matrix.diagonal (positiveSimilarityRootSpectrum data)) *
          data.eigenbasisInv := by noncomm_ring
      _ = data.eigenbasis *
          (Matrix.diagonal (positiveSimilarityRootSpectrum data) * variation +
            variation * Matrix.diagonal
              (positiveSimilarityRootSpectrum data)) *
          data.eigenbasisInv := by rw [data.inv_mul_basis]; simp
  unfold positiveDiagonalizableSylvesterInverse
  rw [hConjugated]
  have hDiagonalInverse :
      sylvesterOperator
          (Matrix.diagonal (positiveSimilarityRootSpectrum data))
          (diagonalSylvesterInverse (positiveRootSpectrum data)
            (data.eigenbasisInv * target * data.eigenbasis)) =
        data.eigenbasisInv * target * data.eigenbasis := by
    simpa [positiveRootSpectrum] using
      diagonalSylvesterInverse_right (positiveRootSpectrum data)
        (data.eigenbasisInv * target * data.eigenbasis)
  rw [hDiagonalInverse]
  calc
    data.eigenbasis *
          (data.eigenbasisInv * target * data.eigenbasis) *
          data.eigenbasisInv =
      (data.eigenbasis * data.eigenbasisInv) * target *
        (data.eigenbasis * data.eigenbasisInv) := by noncomm_ring
    _ = target := by rw [data.basis_mul_inv]; simp

/-- Every supplied positive diagonalizable relative root is Sylvester regular. -/
theorem positiveDiagonalizable_sylvester_bijective
    (data : PositiveDiagonalizableRelativeMatrix) :
    Function.Bijective (sylvesterOperator (positiveSimilarityRoot data)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨positiveDiagonalizableSylvesterInverse data,
      positiveDiagonalizableSylvesterInverse_left data,
      positiveDiagonalizableSylvesterInverse_right data⟩

end

end P0EFTJanusPositiveDiagonalizableSylvesterInverse4D
end JanusFormal
