import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableRelativeRoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootFrechetSylvester

/-!
# Frontier control for positive diagonalizable roots

For a fixed real diagonalization with positive spectrum, this gate varies one
supplied eigenvalue down to zero while keeping the eigenbasis fixed.  The
transported nonnegative root continues to square to the transported target.
At the zero endpoint an explicitly conjugated matrix unit is a nonzero kernel
vector of the Sylvester operator.

This does not classify collisions with general Jordan strata or glue choices
of diagonalization globally.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveDiagonalizableRootFrontierControl4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusMatrixSquareRootFrechetSylvester
open Filter

abbrev Matrix4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Matrix4
abbrev Spectrum4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Spectrum4

/-- Replace one eigenvalue in the supplied ordered spectrum. -/
def replacePositiveSpectrumValue
    (data : PositiveDiagonalizableRelativeMatrix)
    (index : Fin 4) (value : Real) : Spectrum4 :=
  Function.update data.eigenvalue index value

/-- Target matrix along the fixed-eigenbasis path. -/
def positiveDiagonalizableTargetPath
    (data : PositiveDiagonalizableRelativeMatrix)
    (index : Fin 4) (value : Real) : Matrix4 :=
  data.eigenbasis *
    Matrix.diagonal (replacePositiveSpectrumValue data index value) *
      data.eigenbasisInv

/-- Nonnegative square root along the fixed-eigenbasis path. -/
def positiveDiagonalizableRootPath
    (data : PositiveDiagonalizableRelativeMatrix)
    (index : Fin 4) (value : Real) : Matrix4 :=
  data.eigenbasis *
    Matrix.diagonal
      (fun coordinate =>
        Real.sqrt (replacePositiveSpectrumValue data index value coordinate)) *
      data.eigenbasisInv

/-- The transported target varies continuously with the selected eigenvalue. -/
theorem positiveDiagonalizableTargetPath_continuous
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) :
    Continuous (positiveDiagonalizableTargetPath data index) := by
  unfold positiveDiagonalizableTargetPath replacePositiveSpectrumValue
  fun_prop

/-- The nonnegative transported root extends continuously to the zero
eigenvalue endpoint. -/
theorem positiveDiagonalizableRootPath_continuous
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) :
    Continuous (positiveDiagonalizableRootPath data index) := by
  unfold positiveDiagonalizableRootPath replacePositiveSpectrumValue
  fun_prop

theorem positiveDiagonalizableRootPath_tendsto_zero
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) :
    Tendsto (positiveDiagonalizableRootPath data index)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (positiveDiagonalizableRootPath data index 0)) :=
  (positiveDiagonalizableRootPath_continuous data index).continuousAt.tendsto.mono_left
    inf_le_left

/-- Spectral coordinate obtained by returning a matrix to the supplied
eigenbasis and reading its selected diagonal entry. -/
def positiveDiagonalizableConjugatedEigenCoordinate
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4)
    (matrix : Matrix4) : Real :=
  (data.eigenbasisInv * matrix * data.eigenbasis) index index

/-- Interior path on which one target eigenvalue is `parameter⁻¹`. -/
def positiveDiagonalizableDivergentRootPath
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4)
    (parameter : Real) : Matrix4 :=
  positiveDiagonalizableRootPath data index parameter⁻¹

/-- In the supplied eigenbasis, the selected coordinate of the transported
root is exactly the square root of the varied eigenvalue. -/
theorem positiveDiagonalizableConjugatedEigenCoordinate_rootPath
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4)
    (value : Real) :
    positiveDiagonalizableConjugatedEigenCoordinate data index
        (positiveDiagonalizableRootPath data index value) =
      Real.sqrt value := by
  let diagonalRoot : Matrix4 :=
    Matrix.diagonal
      (fun coordinate =>
        Real.sqrt (replacePositiveSpectrumValue data index value coordinate))
  have hConjugate :
      data.eigenbasisInv *
            (data.eigenbasis * diagonalRoot * data.eigenbasisInv) *
          data.eigenbasis =
        diagonalRoot := by
    calc
      data.eigenbasisInv *
            (data.eigenbasis * diagonalRoot * data.eigenbasisInv) *
          data.eigenbasis =
        (data.eigenbasisInv * data.eigenbasis) * diagonalRoot *
          (data.eigenbasisInv * data.eigenbasis) := by noncomm_ring
      _ = diagonalRoot := by rw [data.inv_mul_basis]; simp
  change
    (data.eigenbasisInv *
          (data.eigenbasis * diagonalRoot * data.eigenbasisInv) *
        data.eigenbasis) index index = Real.sqrt value
  rw [hConjugate]
  simp [diagonalRoot, replacePositiveSpectrumValue]

/-- The selected spectral coordinate diverges along the reciprocal-eigenvalue
path as the positive parameter approaches zero. -/
theorem positiveDiagonalizableDivergentEigenCoordinate_tendsto_atTop
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) :
    Tendsto
      (fun parameter =>
        positiveDiagonalizableConjugatedEigenCoordinate data index
          (positiveDiagonalizableDivergentRootPath data index parameter))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hDivergence :
      Tendsto (fun parameter : Real => Real.sqrt parameter⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_inv_nhdsGT_zero
  simpa [positiveDiagonalizableDivergentRootPath,
    positiveDiagonalizableConjugatedEigenCoordinate_rootPath] using hDivergence

theorem positiveDiagonalizableRootPath_square
    (data : PositiveDiagonalizableRelativeMatrix)
    (index : Fin 4) {value : Real} (hValue : 0 ≤ value) :
    positiveDiagonalizableRootPath data index value *
        positiveDiagonalizableRootPath data index value =
      positiveDiagonalizableTargetPath data index value := by
  have hSpectrum : ∀ coordinate,
      0 ≤ replacePositiveSpectrumValue data index value coordinate := by
    intro coordinate
    by_cases hCoordinate : coordinate = index
    · subst coordinate
      simpa [replacePositiveSpectrumValue] using hValue
    · simp [replacePositiveSpectrumValue, hCoordinate,
        le_of_lt (data.eigenvalue_pos coordinate)]
  have hDiagonal :
      Matrix.diagonal
          (fun coordinate =>
            Real.sqrt
              (replacePositiveSpectrumValue data index value coordinate)) *
          Matrix.diagonal
            (fun coordinate =>
              Real.sqrt
                (replacePositiveSpectrumValue data index value coordinate)) =
        Matrix.diagonal (replacePositiveSpectrumValue data index value) := by
    ext first second
    by_cases hIndices : first = second
    · subst second
      simp [Real.mul_self_sqrt (hSpectrum first)]
    · simp [hIndices]
  unfold positiveDiagonalizableRootPath positiveDiagonalizableTargetPath
  rw [← hDiagonal]
  calc
    (data.eigenbasis *
          Matrix.diagonal
            (fun coordinate =>
              Real.sqrt
                (replacePositiveSpectrumValue data index value coordinate)) *
        data.eigenbasisInv) *
        (data.eigenbasis *
            Matrix.diagonal
              (fun coordinate =>
                Real.sqrt
                  (replacePositiveSpectrumValue data index value coordinate)) *
          data.eigenbasisInv) =
      data.eigenbasis *
          Matrix.diagonal
            (fun coordinate =>
              Real.sqrt
                (replacePositiveSpectrumValue data index value coordinate)) *
        (data.eigenbasisInv * data.eigenbasis) *
          Matrix.diagonal
            (fun coordinate =>
              Real.sqrt
                (replacePositiveSpectrumValue data index value coordinate)) *
        data.eigenbasisInv := by noncomm_ring
    _ = data.eigenbasis *
        (Matrix.diagonal
            (fun coordinate =>
              Real.sqrt
                (replacePositiveSpectrumValue data index value coordinate)) *
          Matrix.diagonal
            (fun coordinate =>
              Real.sqrt
                (replacePositiveSpectrumValue data index value coordinate))) *
        data.eigenbasisInv := by
          rw [data.inv_mul_basis]
          simp only [Matrix.mul_one, Matrix.mul_assoc]

/-- The reciprocal-eigenvalue path remains an exact square-root path for every
positive parameter. -/
theorem positiveDiagonalizableDivergentRootPath_square
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4)
    {parameter : Real} (hParameter : 0 < parameter) :
    positiveDiagonalizableDivergentRootPath data index parameter *
        positiveDiagonalizableDivergentRootPath data index parameter =
      positiveDiagonalizableTargetPath data index parameter⁻¹ := by
  exact positiveDiagonalizableRootPath_square data index
    (le_of_lt (inv_pos.mpr hParameter))

/-- At its original positive eigenvalue, the target path returns the supplied
target matrix. -/
theorem positiveDiagonalizableTargetPath_at_eigenvalue
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) :
    positiveDiagonalizableTargetPath data index (data.eigenvalue index) =
      data.target := by
  have hSpectrum :
      replacePositiveSpectrumValue data index (data.eigenvalue index) =
        data.eigenvalue := by
    funext coordinate
    by_cases hCoordinate : coordinate = index
    · subst coordinate
      simp [replacePositiveSpectrumValue]
    · simp [replacePositiveSpectrumValue, hCoordinate]
  rw [positiveDiagonalizableTargetPath, hSpectrum, ← data.target_eq]

/-- At its original positive eigenvalue, the root path returns the selected
positive similarity root. -/
theorem positiveDiagonalizableRootPath_at_eigenvalue
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) :
    positiveDiagonalizableRootPath data index (data.eigenvalue index) =
      positiveSimilarityRoot data := by
  have hSpectrum :
      replacePositiveSpectrumValue data index (data.eigenvalue index) =
        data.eigenvalue := by
    funext coordinate
    by_cases hCoordinate : coordinate = index
    · subst coordinate
      simp [replacePositiveSpectrumValue]
    · simp [replacePositiveSpectrumValue, hCoordinate]
  rw [positiveDiagonalizableRootPath, hSpectrum]
  rfl

/-- Matrix unit transported to the supplied eigenbasis. -/
def positiveDiagonalizableBoundaryKernel
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) : Matrix4 :=
  data.eigenbasis * Matrix.single index index 1 * data.eigenbasisInv

theorem positiveDiagonalizableBoundaryKernel_ne_zero
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) :
    positiveDiagonalizableBoundaryKernel data index ≠ 0 := by
  intro hZero
  have hTransport := congrArg
    (fun matrix : Matrix4 => data.eigenbasisInv * matrix * data.eigenbasis)
    hZero
  have hSingle : (Matrix.single index index 1 : Matrix4) = 0 := by
    calc
      (Matrix.single index index 1 : Matrix4) =
          (data.eigenbasisInv * data.eigenbasis) *
            Matrix.single index index 1 *
              (data.eigenbasisInv * data.eigenbasis) := by
                rw [data.inv_mul_basis]
                simp
      _ = data.eigenbasisInv *
          positiveDiagonalizableBoundaryKernel data index *
            data.eigenbasis := by
              simp only [positiveDiagonalizableBoundaryKernel]
              noncomm_ring
      _ = 0 := by rw [hZero]; simp
  have hEntry := congrArg (fun matrix : Matrix4 => matrix index index) hSingle
  simp [Matrix.single] at hEntry

theorem positiveDiagonalizableBoundaryKernel_sylvester_eq_zero
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) :
    sylvesterOperator (positiveDiagonalizableRootPath data index 0)
        (positiveDiagonalizableBoundaryKernel data index) = 0 := by
  let diagonalRoot : Matrix4 :=
    Matrix.diagonal
      (fun coordinate =>
        Real.sqrt (replacePositiveSpectrumValue data index 0 coordinate))
  let matrixUnit : Matrix4 := Matrix.single index index 1
  have hDiagonalKernel :
      diagonalRoot * matrixUnit + matrixUnit * diagonalRoot = 0 := by
    ext first second
    by_cases hEntry : index = first ∧ index = second
    · rcases hEntry with ⟨rfl, rfl⟩
      simp [diagonalRoot, matrixUnit, Matrix.diagonal_mul,
        Matrix.mul_diagonal, replacePositiveSpectrumValue, Matrix.single]
    · simp [diagonalRoot, matrixUnit, Matrix.diagonal_mul,
        Matrix.mul_diagonal, replacePositiveSpectrumValue, Matrix.single,
        hEntry]
  change
    (data.eigenbasis * diagonalRoot * data.eigenbasisInv) *
          (data.eigenbasis * matrixUnit * data.eigenbasisInv) +
        (data.eigenbasis * matrixUnit * data.eigenbasisInv) *
          (data.eigenbasis * diagonalRoot * data.eigenbasisInv) = 0
  calc
    (data.eigenbasis * diagonalRoot * data.eigenbasisInv) *
          (data.eigenbasis * matrixUnit * data.eigenbasisInv) +
        (data.eigenbasis * matrixUnit * data.eigenbasisInv) *
          (data.eigenbasis * diagonalRoot * data.eigenbasisInv) =
        data.eigenbasis * diagonalRoot *
              (data.eigenbasisInv * data.eigenbasis) * matrixUnit *
              data.eigenbasisInv +
          data.eigenbasis * matrixUnit *
              (data.eigenbasisInv * data.eigenbasis) * diagonalRoot *
              data.eigenbasisInv := by noncomm_ring
    _ =
        data.eigenbasis * (diagonalRoot * matrixUnit + matrixUnit * diagonalRoot) *
          data.eigenbasisInv := by
            rw [data.inv_mul_basis]
            noncomm_ring
    _ = 0 := by rw [hDiagonalKernel]; simp

/-- The Sylvester linearization loses injectivity at the endpoint where one
transported root eigenvalue reaches zero. -/
theorem positiveDiagonalizableBoundarySylvester_not_injective
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) :
    ¬Function.Injective
      (sylvesterOperator (positiveDiagonalizableRootPath data index 0)) := by
  intro hInjective
  apply positiveDiagonalizableBoundaryKernel_ne_zero data index
  apply hInjective
  rw [positiveDiagonalizableBoundaryKernel_sylvester_eq_zero]
  exact (map_zero
    (sylvesterOperator (positiveDiagonalizableRootPath data index 0))).symm

end

end P0EFTJanusPositiveDiagonalizableRootFrontierControl4D
end JanusFormal
