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

/-- Linearity of the transported inverse. -/
def positiveDiagonalizableSylvesterInverseLinearMap
    (data : PositiveDiagonalizableRelativeMatrix) : Matrix4 →ₗ[Real] Matrix4 where
  toFun := positiveDiagonalizableSylvesterInverse data
  map_add' first second := by
    unfold positiveDiagonalizableSylvesterInverse
    rw [mul_add, add_mul, map_add]
    noncomm_ring
  map_smul' scalar target := by
    unfold positiveDiagonalizableSylvesterInverse
    rw [Matrix.mul_smul, Matrix.smul_mul, map_smul]
    simp

/-- The transported inverse is continuous in finite dimension. -/
def positiveDiagonalizableSylvesterInverseCLM
    (data : PositiveDiagonalizableRelativeMatrix) : Matrix4 →L[Real] Matrix4 :=
  LinearMap.toContinuousLinearMap
    (positiveDiagonalizableSylvesterInverseLinearMap data)

@[simp]
theorem positiveDiagonalizableSylvesterInverseCLM_apply
    (data : PositiveDiagonalizableRelativeMatrix) (target : Matrix4) :
    positiveDiagonalizableSylvesterInverseCLM data target =
      positiveDiagonalizableSylvesterInverse data target :=
  rfl

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

/-- Explicit two-sided continuous inverse consumed by the general square-root
Fréchet derivative theory. -/
def positiveDiagonalizableSylvesterInverseWitness
    (data : PositiveDiagonalizableRelativeMatrix) :
    SylvesterInverseWitness (positiveSimilarityRoot data) where
  inverse := positiveDiagonalizableSylvesterInverseCLM data
  leftInverse := positiveDiagonalizableSylvesterInverse_left data
  rightInverse := positiveDiagonalizableSylvesterInverse_right data

/-- At a positive diagonalizable presentation, every differentiable
square-root selection has the explicit inverse-Sylvester derivative. -/
theorem positiveDiagonalizable_squareRoot_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {root target : E → Matrix4}
    {targetDerivative : E →L[Real] Matrix4}
    {point : E}
    (data : PositiveDiagonalizableRelativeMatrix)
    (hValue : root point = positiveSimilarityRoot data)
    (hRoot : DifferentiableAt Real root point)
    (hTarget : HasFDerivAt target targetDerivative point)
    (hSquare : ∀ x, squareMap (root x) = target x) :
    fderiv Real root point =
      (positiveDiagonalizableSylvesterInverseCLM data).comp targetDerivative := by
  have hActual := hRoot.hasFDerivAt
  have hEquation :=
    squareRoot_derivative_equation hActual hTarget hSquare
  have hLeft (variation : Matrix4) :
      positiveDiagonalizableSylvesterInverseCLM data
          (sylvesterOperator (root point) variation) = variation := by
    rw [hValue, positiveDiagonalizableSylvesterInverseCLM_apply]
    exact positiveDiagonalizableSylvesterInverse_left data variation
  apply ContinuousLinearMap.ext
  intro direction
  calc
    fderiv Real root point direction =
        positiveDiagonalizableSylvesterInverseCLM data
          (sylvesterOperator (root point)
            (fderiv Real root point direction)) :=
      (hLeft (fderiv Real root point direction)).symm
    _ = positiveDiagonalizableSylvesterInverseCLM data
        (((sylvesterOperator (root point)).comp
          (fderiv Real root point)) direction) := rfl
    _ = positiveDiagonalizableSylvesterInverseCLM data
        (targetDerivative direction) := by rw [hEquation]
    _ = ((positiveDiagonalizableSylvesterInverseCLM data).comp
        targetDerivative) direction := rfl

end

end P0EFTJanusPositiveDiagonalizableSylvesterInverse4D
end JanusFormal
