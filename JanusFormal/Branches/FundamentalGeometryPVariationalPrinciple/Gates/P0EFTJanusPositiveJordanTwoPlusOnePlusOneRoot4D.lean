import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanThreePlusOneRoot4D

/-!
# Positive real Jordan roots on the `2 + 1 + 1` primary stratum

This gate closes the supplied real primary decomposition formed by one
size-two Jordan block and two singleton blocks.  Their three eigenvalues are
arbitrary and strictly positive.  The block root is transported by a supplied
similarity, is continuous on the fixed stratum, and is Sylvester regular.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveJordanTwoPlusOnePlusOneRoot4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveDiagonalSylvesterInverse
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
open P0EFTJanusPositiveJordanTwoPlusTwoRoot4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalSylvesterInverse.Matrix4

abbrev Jordan211Eigenvalues :=
  PositiveEigenvalue × (PositiveEigenvalue × PositiveEigenvalue)

def jordan211RootSpectrum
    (pair firstSingleton secondSingleton : PositiveEigenvalue) :
    PositiveDiagonalSpectrum :=
  ⟨![Real.sqrt pair.1, Real.sqrt pair.1,
      Real.sqrt firstSingleton.1, Real.sqrt secondSingleton.1], by
    change ∀ i, 0 < ![Real.sqrt pair.1, Real.sqrt pair.1,
      Real.sqrt firstSingleton.1, Real.sqrt secondSingleton.1] i
    intro i
    fin_cases i
    · exact Real.sqrt_pos.2 pair.2
    · exact Real.sqrt_pos.2 pair.2
    · exact Real.sqrt_pos.2 firstSingleton.2
    · exact Real.sqrt_pos.2 secondSingleton.2⟩

def jordan211TargetSpectrum
    (pair firstSingleton secondSingleton : PositiveEigenvalue) : Fin 4 → Real :=
  ![pair.1, pair.1, firstSingleton.1, secondSingleton.1]

def jordan211DiagonalRoot
    (pair firstSingleton secondSingleton : PositiveEigenvalue) : Matrix4 :=
  Matrix.diagonal
    (jordan211RootSpectrum pair firstSingleton secondSingleton).1

def jordan211DiagonalTarget
    (pair firstSingleton secondSingleton : PositiveEigenvalue) : Matrix4 :=
  Matrix.diagonal
    (jordan211TargetSpectrum pair firstSingleton secondSingleton)

def jordan211RootNilpotent
    (pair _firstSingleton _secondSingleton : PositiveEigenvalue) : Matrix4 :=
  ![![0, jordan22RootOffDiagonal pair, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

def jordan211TargetNilpotent : Matrix4 :=
  ![![0, 1, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

def canonicalJordan211Root
    (pair firstSingleton secondSingleton : PositiveEigenvalue) : Matrix4 :=
  jordan211DiagonalRoot pair firstSingleton secondSingleton +
    jordan211RootNilpotent pair firstSingleton secondSingleton

def canonicalJordan211Target
    (pair firstSingleton secondSingleton : PositiveEigenvalue) : Matrix4 :=
  jordan211DiagonalTarget pair firstSingleton secondSingleton +
    jordan211TargetNilpotent

theorem jordan211RootNilpotent_square
    (pair firstSingleton secondSingleton : PositiveEigenvalue) :
    jordan211RootNilpotent pair firstSingleton secondSingleton *
        jordan211RootNilpotent pair firstSingleton secondSingleton = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordan211RootNilpotent, Matrix.mul_apply, Fin.sum_univ_four]

theorem jordan211DiagonalRoot_commutes_nilpotent
    (pair firstSingleton secondSingleton : PositiveEigenvalue) :
    jordan211DiagonalRoot pair firstSingleton secondSingleton *
        jordan211RootNilpotent pair firstSingleton secondSingleton =
      jordan211RootNilpotent pair firstSingleton secondSingleton *
        jordan211DiagonalRoot pair firstSingleton secondSingleton := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [jordan211DiagonalRoot, jordan211RootSpectrum,
    jordan211RootNilpotent, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

theorem canonicalJordan211Root_square
    (pair firstSingleton secondSingleton : PositiveEigenvalue) :
    canonicalJordan211Root pair firstSingleton secondSingleton *
        canonicalJordan211Root pair firstSingleton secondSingleton =
      canonicalJordan211Target pair firstSingleton secondSingleton := by
  have hPairSquare : Real.sqrt pair.1 * Real.sqrt pair.1 = pair.1 :=
    Real.mul_self_sqrt (le_of_lt pair.2)
  have hFirstSquare :
      Real.sqrt firstSingleton.1 * Real.sqrt firstSingleton.1 =
        firstSingleton.1 :=
    Real.mul_self_sqrt (le_of_lt firstSingleton.2)
  have hSecondSquare :
      Real.sqrt secondSingleton.1 * Real.sqrt secondSingleton.1 =
        secondSingleton.1 :=
    Real.mul_self_sqrt (le_of_lt secondSingleton.2)
  have hPairNe : Real.sqrt pair.1 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 pair.2)
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [canonicalJordan211Root, canonicalJordan211Target,
    jordan211DiagonalRoot, jordan211DiagonalTarget, jordan211RootSpectrum,
    jordan211TargetSpectrum, jordan211RootNilpotent,
    jordan211TargetNilpotent, jordan22RootOffDiagonal, Matrix.mul_apply,
    Fin.sum_univ_four, hPairSquare, hFirstSquare, hSecondSquare]
  all_goals field_simp [hPairNe]
  all_goals ring

abbrev RawJordan211Data := Jordan211Eigenvalues × (Matrix4 × Matrix4)

def jordan211SimilarityLocus : Set RawJordan211Data :=
  {data | data.2.2 * data.2.1 = 1 ∧ data.2.1 * data.2.2 = 1}

abbrev Jordan211Data := jordan211SimilarityLocus

def pairEigenvalue (data : Jordan211Data) : PositiveEigenvalue := data.1.1.1

def firstSingletonEigenvalue (data : Jordan211Data) : PositiveEigenvalue :=
  data.1.1.2.1

def secondSingletonEigenvalue (data : Jordan211Data) : PositiveEigenvalue :=
  data.1.1.2.2

def jordan211Change (data : Jordan211Data) : Matrix4 := data.1.2.1

def jordan211Inverse (data : Jordan211Data) : Matrix4 := data.1.2.2

def jordan211Target (data : Jordan211Data) : Matrix4 :=
  jordan211Change data *
    canonicalJordan211Target (pairEigenvalue data)
      (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
    jordan211Inverse data

def jordan211Root (data : Jordan211Data) : Matrix4 :=
  jordan211Change data *
    canonicalJordan211Root (pairEigenvalue data)
      (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
    jordan211Inverse data

theorem jordan211Inverse_change (data : Jordan211Data) :
    jordan211Inverse data * jordan211Change data = 1 :=
  data.property.1

theorem jordan211Change_inverse (data : Jordan211Data) :
    jordan211Change data * jordan211Inverse data = 1 :=
  data.property.2

theorem jordan211Root_square (data : Jordan211Data) :
    jordan211Root data * jordan211Root data = jordan211Target data := by
  have hCanonical := canonicalJordan211Root_square
    (pairEigenvalue data) (firstSingletonEigenvalue data)
    (secondSingletonEigenvalue data)
  have hInverseChange := jordan211Inverse_change data
  unfold jordan211Root jordan211Target
  calc
    (jordan211Change data *
          canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
        jordan211Inverse data) *
        (jordan211Change data *
          canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
        jordan211Inverse data) =
      jordan211Change data *
        canonicalJordan211Root (pairEigenvalue data)
          (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
        (jordan211Inverse data * jordan211Change data) *
        canonicalJordan211Root (pairEigenvalue data)
          (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
        jordan211Inverse data := by noncomm_ring
    _ = jordan211Change data *
        (canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
          canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data)) *
        jordan211Inverse data := by
      rw [hInverseChange]
      simp [mul_assoc]
    _ = jordan211Change data *
        canonicalJordan211Target (pairEigenvalue data)
          (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
        jordan211Inverse data := by rw [hCanonical]

def rebaseJordan211Data
    (data : Jordan211Data) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) : Jordan211Data :=
  ⟨⟨data.1.1,
      ⟨change * jordan211Change data, jordan211Inverse data * inverse⟩⟩, by
    constructor
    · change (jordan211Inverse data * inverse) *
        (change * jordan211Change data) = 1
      calc
        _ = jordan211Inverse data * (inverse * change) *
            jordan211Change data := by noncomm_ring
        _ = jordan211Inverse data * jordan211Change data := by
          rw [hInverseChange]
          simp
        _ = 1 := jordan211Inverse_change data
    · change (change * jordan211Change data) *
        (jordan211Inverse data * inverse) = 1
      calc
        _ = change * (jordan211Change data * jordan211Inverse data) *
            inverse := by noncomm_ring
        _ = change * inverse := by rw [jordan211Change_inverse]; simp
        _ = 1 := hChangeInverse⟩

theorem jordan211Root_rebase
    (data : Jordan211Data) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    jordan211Root
        (rebaseJordan211Data data change inverse hInverseChange hChangeInverse) =
      change * jordan211Root data * inverse := by
  unfold jordan211Root rebaseJordan211Data pairEigenvalue
    firstSingletonEigenvalue secondSingletonEigenvalue jordan211Change
    jordan211Inverse
  noncomm_ring

theorem canonicalJordan211Root_continuous :
    Continuous (fun data : Jordan211Eigenvalues =>
      canonicalJordan211Root data.1 data.2.1 data.2.2) := by
  apply continuous_matrix
  intro i j
  have hOffDiagonal : Continuous
      (fun data : Jordan211Eigenvalues => jordan22RootOffDiagonal data.1) :=
    jordan22RootOffDiagonal_continuous.comp continuous_fst
  fin_cases i <;> fin_cases j <;>
    simp [canonicalJordan211Root, jordan211DiagonalRoot,
      jordan211RootSpectrum, jordan211RootNilpotent]
  all_goals first | exact hOffDiagonal | fun_prop

theorem jordan211Root_continuous : Continuous jordan211Root := by
  have hEigenvalues : Continuous
      (fun data : Jordan211Data => data.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hCanonical : Continuous
      (fun data : Jordan211Data =>
        canonicalJordan211Root (pairEigenvalue data)
          (firstSingletonEigenvalue data) (secondSingletonEigenvalue data)) :=
    canonicalJordan211Root_continuous.comp hEigenvalues
  have hChange : Continuous jordan211Change := by
    unfold jordan211Change
    fun_prop
  have hInverse : Continuous jordan211Inverse := by
    unfold jordan211Inverse
    fun_prop
  unfold jordan211Root
  exact (hChange.matrix_mul hCanonical).matrix_mul hInverse

def jordan211SylvesterPerturbation
    (pair firstSingleton secondSingleton : PositiveEigenvalue) :
    Matrix4 →L[Real] Matrix4 :=
  sylvesterOperator
    (jordan211RootNilpotent pair firstSingleton secondSingleton)

def jordan211SylvesterCorrection
    (pair firstSingleton secondSingleton : PositiveEigenvalue) :
    Matrix4 →L[Real] Matrix4 :=
  (diagonalSylvesterInverse
      (jordan211RootSpectrum pair firstSingleton secondSingleton)).comp
    (jordan211SylvesterPerturbation pair firstSingleton secondSingleton)

theorem jordan211SylvesterPerturbation_cube
    (pair firstSingleton secondSingleton : PositiveEigenvalue)
    (variation : Matrix4) :
    jordan211SylvesterPerturbation pair firstSingleton secondSingleton
      (jordan211SylvesterPerturbation pair firstSingleton secondSingleton
        (jordan211SylvesterPerturbation pair firstSingleton secondSingleton
          variation)) = 0 := by
  have hSquare := jordan211RootNilpotent_square
    pair firstSingleton secondSingleton
  have hLeft (matrix : Matrix4) :
      jordan211RootNilpotent pair firstSingleton secondSingleton *
          (jordan211RootNilpotent pair firstSingleton secondSingleton *
            matrix) = 0 := by
    rw [← mul_assoc, hSquare, zero_mul]
  simp only [jordan211SylvesterPerturbation, sylvesterOperator_apply]
  noncomm_ring [hSquare]
  simp only [hLeft, mul_zero, smul_zero, add_zero]

theorem jordan211Diagonal_perturbation_commute
    (pair firstSingleton secondSingleton : PositiveEigenvalue)
    (variation : Matrix4) :
    sylvesterOperator
        (jordan211DiagonalRoot pair firstSingleton secondSingleton)
        (jordan211SylvesterPerturbation pair firstSingleton secondSingleton
          variation) =
      jordan211SylvesterPerturbation pair firstSingleton secondSingleton
        (sylvesterOperator
          (jordan211DiagonalRoot pair firstSingleton secondSingleton)
          variation) := by
  have hCommutes := jordan211DiagonalRoot_commutes_nilpotent
    pair firstSingleton secondSingleton
  have hCommutesRight (matrix : Matrix4) :
      jordan211DiagonalRoot pair firstSingleton secondSingleton *
          (jordan211RootNilpotent pair firstSingleton secondSingleton *
            matrix) =
        jordan211RootNilpotent pair firstSingleton secondSingleton *
          (jordan211DiagonalRoot pair firstSingleton secondSingleton *
            matrix) := by
    rw [← mul_assoc, hCommutes, mul_assoc]
  simp only [jordan211SylvesterPerturbation, sylvesterOperator_apply]
  noncomm_ring [hCommutes]
  rw [hCommutesRight]
  module

theorem jordan211DiagonalInverse_perturbation_commute
    (pair firstSingleton secondSingleton : PositiveEigenvalue)
    (variation : Matrix4) :
    diagonalSylvesterInverse
        (jordan211RootSpectrum pair firstSingleton secondSingleton)
        (jordan211SylvesterPerturbation pair firstSingleton secondSingleton
          variation) =
      jordan211SylvesterPerturbation pair firstSingleton secondSingleton
        (diagonalSylvesterInverse
          (jordan211RootSpectrum pair firstSingleton secondSingleton)
          variation) := by
  apply Function.LeftInverse.injective
    (diagonalSylvesterInverse_left
      (jordan211RootSpectrum pair firstSingleton secondSingleton))
  calc
    sylvesterOperator
        (jordan211DiagonalRoot pair firstSingleton secondSingleton)
        (diagonalSylvesterInverse
          (jordan211RootSpectrum pair firstSingleton secondSingleton)
          (jordan211SylvesterPerturbation pair firstSingleton secondSingleton
            variation)) =
      jordan211SylvesterPerturbation pair firstSingleton secondSingleton
        variation := by
      exact diagonalSylvesterInverse_right
        (jordan211RootSpectrum pair firstSingleton secondSingleton)
        (jordan211SylvesterPerturbation pair firstSingleton secondSingleton
          variation)
    _ = jordan211SylvesterPerturbation pair firstSingleton secondSingleton
        (sylvesterOperator
          (jordan211DiagonalRoot pair firstSingleton secondSingleton)
          (diagonalSylvesterInverse
            (jordan211RootSpectrum pair firstSingleton secondSingleton)
            variation)) := by
      congr 1
      exact (diagonalSylvesterInverse_right
        (jordan211RootSpectrum pair firstSingleton secondSingleton)
        variation).symm
    _ = sylvesterOperator
        (jordan211DiagonalRoot pair firstSingleton secondSingleton)
        (jordan211SylvesterPerturbation pair firstSingleton secondSingleton
          (diagonalSylvesterInverse
            (jordan211RootSpectrum pair firstSingleton secondSingleton)
            variation)) := by
      exact (jordan211Diagonal_perturbation_commute pair firstSingleton
        secondSingleton
        (diagonalSylvesterInverse
          (jordan211RootSpectrum pair firstSingleton secondSingleton)
          variation)).symm

theorem jordan211SylvesterCorrection_cube
    (pair firstSingleton secondSingleton : PositiveEigenvalue)
    (variation : Matrix4) :
    jordan211SylvesterCorrection pair firstSingleton secondSingleton
      (jordan211SylvesterCorrection pair firstSingleton secondSingleton
        (jordan211SylvesterCorrection pair firstSingleton secondSingleton
          variation)) = 0 := by
  let inverseDiagonal : Module.End Real Matrix4 :=
    (diagonalSylvesterInverse
      (jordan211RootSpectrum pair firstSingleton secondSingleton)).toLinearMap
  let perturbation : Module.End Real Matrix4 :=
    (jordan211SylvesterPerturbation pair firstSingleton
      secondSingleton).toLinearMap
  have hCommute : Commute inverseDiagonal perturbation := by
    apply LinearMap.ext
    intro rhs
    exact jordan211DiagonalInverse_perturbation_commute pair firstSingleton
      secondSingleton rhs
  have hPerturbationPow : perturbation ^ 3 = 0 := by
    apply LinearMap.ext
    intro rhs
    exact jordan211SylvesterPerturbation_cube pair firstSingleton
      secondSingleton rhs
  have hProduct : (inverseDiagonal * perturbation) ^ 3 = 0 := by
    rw [hCommute.mul_pow, hPerturbationPow, mul_zero]
  change ((inverseDiagonal * perturbation) ^ 3) variation = 0
  rw [hProduct]
  rfl

def canonicalJordan211SylvesterInverse
    (pair firstSingleton secondSingleton : PositiveEigenvalue) :
    Matrix4 →L[Real] Matrix4 :=
  let correction :=
    jordan211SylvesterCorrection pair firstSingleton secondSingleton
  ((ContinuousLinearMap.id Real Matrix4 - correction) +
      correction.comp correction).comp
    (diagonalSylvesterInverse
      (jordan211RootSpectrum pair firstSingleton secondSingleton))

theorem canonicalJordan211Sylvester_decompose
    (pair firstSingleton secondSingleton : PositiveEigenvalue)
    (variation : Matrix4) :
    sylvesterOperator
        (canonicalJordan211Root pair firstSingleton secondSingleton)
        variation =
      sylvesterOperator
          (jordan211DiagonalRoot pair firstSingleton secondSingleton)
          variation +
        jordan211SylvesterPerturbation pair firstSingleton secondSingleton
          variation := by
  unfold canonicalJordan211Root jordan211SylvesterPerturbation
  simp only [sylvesterOperator_apply]
  noncomm_ring

theorem canonicalJordan211SylvesterInverse_left
    (pair firstSingleton secondSingleton : PositiveEigenvalue)
    (variation : Matrix4) :
    canonicalJordan211SylvesterInverse pair firstSingleton secondSingleton
        (sylvesterOperator
          (canonicalJordan211Root pair firstSingleton secondSingleton)
          variation) = variation := by
  have hBase :
      diagonalSylvesterInverse
          (jordan211RootSpectrum pair firstSingleton secondSingleton)
          (sylvesterOperator
            (canonicalJordan211Root pair firstSingleton secondSingleton)
            variation) =
        variation +
          jordan211SylvesterCorrection pair firstSingleton secondSingleton
            variation := by
    rw [canonicalJordan211Sylvester_decompose, map_add]
    change diagonalSylvesterInverse
          (jordan211RootSpectrum pair firstSingleton secondSingleton)
          (sylvesterOperator
            (Matrix.diagonal
              (jordan211RootSpectrum pair firstSingleton secondSingleton).1)
            variation) +
        diagonalSylvesterInverse
          (jordan211RootSpectrum pair firstSingleton secondSingleton)
          (jordan211SylvesterPerturbation pair firstSingleton secondSingleton
            variation) =
      variation +
        jordan211SylvesterCorrection pair firstSingleton secondSingleton
          variation
    rw [diagonalSylvesterInverse_left]
    rfl
  unfold canonicalJordan211SylvesterInverse
  simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply,
    ContinuousLinearMap.id_apply]
  rw [hBase]
  simp only [map_add]
  rw [jordan211SylvesterCorrection_cube]
  module

theorem canonicalJordan211Sylvester_injective
    (pair firstSingleton secondSingleton : PositiveEigenvalue) :
    Function.Injective
      (sylvesterOperator
        (canonicalJordan211Root pair firstSingleton secondSingleton)) :=
  Function.LeftInverse.injective
    (canonicalJordan211SylvesterInverse_left pair firstSingleton
      secondSingleton)

theorem canonicalJordan211Sylvester_surjective
    (pair firstSingleton secondSingleton : PositiveEigenvalue) :
    Function.Surjective
      (sylvesterOperator
        (canonicalJordan211Root pair firstSingleton secondSingleton)) := by
  have hInjective : Function.Injective
      (sylvesterOperator
        (canonicalJordan211Root pair firstSingleton
          secondSingleton)).toLinearMap :=
    canonicalJordan211Sylvester_injective pair firstSingleton secondSingleton
  exact LinearMap.injective_iff_surjective.mp hInjective

theorem canonicalJordan211SylvesterInverse_right
    (pair firstSingleton secondSingleton : PositiveEigenvalue)
    (rhs : Matrix4) :
    sylvesterOperator
        (canonicalJordan211Root pair firstSingleton secondSingleton)
        (canonicalJordan211SylvesterInverse pair firstSingleton
          secondSingleton rhs) = rhs := by
  obtain ⟨variation, hVariation⟩ :=
    canonicalJordan211Sylvester_surjective pair firstSingleton secondSingleton
      rhs
  rw [← hVariation, canonicalJordan211SylvesterInverse_left]

def jordan211SylvesterInverse
    (data : Jordan211Data) (rhs : Matrix4) : Matrix4 :=
  jordan211Change data *
    canonicalJordan211SylvesterInverse (pairEigenvalue data)
      (firstSingletonEigenvalue data) (secondSingletonEigenvalue data)
      (jordan211Inverse data * rhs * jordan211Change data) *
    jordan211Inverse data

theorem jordan211Sylvester_inverse_apply
    (data : Jordan211Data) (rhs : Matrix4) :
    sylvesterOperator (jordan211Root data)
        (jordan211SylvesterInverse data rhs) = rhs := by
  let canonicalVariation := canonicalJordan211SylvesterInverse
    (pairEigenvalue data) (firstSingletonEigenvalue data)
    (secondSingletonEigenvalue data)
    (jordan211Inverse data * rhs * jordan211Change data)
  have hCanonical :
      sylvesterOperator
          (canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data))
          canonicalVariation =
        jordan211Inverse data * rhs * jordan211Change data :=
    canonicalJordan211SylvesterInverse_right (pairEigenvalue data)
      (firstSingletonEigenvalue data) (secondSingletonEigenvalue data)
      (jordan211Inverse data * rhs * jordan211Change data)
  have hInverseChange := jordan211Inverse_change data
  have hChangeInverse := jordan211Change_inverse data
  unfold jordan211Root jordan211SylvesterInverse
  change sylvesterOperator
      (jordan211Change data *
          canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
        jordan211Inverse data)
      (jordan211Change data * canonicalVariation * jordan211Inverse data) = rhs
  simp only [sylvesterOperator_apply] at hCanonical ⊢
  have hFirstProduct :
      (jordan211Change data *
            canonicalJordan211Root (pairEigenvalue data)
              (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
          jordan211Inverse data) *
          (jordan211Change data * canonicalVariation * jordan211Inverse data) =
        jordan211Change data *
          (canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
            canonicalVariation) * jordan211Inverse data := by
    calc
      _ = jordan211Change data *
          canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
          (jordan211Inverse data * jordan211Change data) * canonicalVariation *
          jordan211Inverse data := by noncomm_ring
      _ = _ := by rw [hInverseChange]; simp [mul_assoc]
  have hSecondProduct :
      (jordan211Change data * canonicalVariation * jordan211Inverse data) *
          (jordan211Change data *
            canonicalJordan211Root (pairEigenvalue data)
              (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
            jordan211Inverse data) =
        jordan211Change data *
          (canonicalVariation * canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data)) *
          jordan211Inverse data := by
    calc
      _ = jordan211Change data * canonicalVariation *
          (jordan211Inverse data * jordan211Change data) *
          canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
          jordan211Inverse data := by noncomm_ring
      _ = _ := by rw [hInverseChange]; simp [mul_assoc]
  calc
    _ = jordan211Change data *
        (canonicalJordan211Root (pairEigenvalue data)
              (firstSingletonEigenvalue data) (secondSingletonEigenvalue data) *
            canonicalVariation +
          canonicalVariation * canonicalJordan211Root (pairEigenvalue data)
            (firstSingletonEigenvalue data) (secondSingletonEigenvalue data)) *
        jordan211Inverse data := by
      rw [hFirstProduct, hSecondProduct]
      noncomm_ring
    _ = jordan211Change data *
        (jordan211Inverse data * rhs * jordan211Change data) *
        jordan211Inverse data := by rw [hCanonical]
    _ = rhs := by
      calc
        _ = (jordan211Change data * jordan211Inverse data) * rhs *
            (jordan211Change data * jordan211Inverse data) := by noncomm_ring
        _ = rhs := by rw [hChangeInverse]; simp

theorem jordan211Sylvester_surjective (data : Jordan211Data) :
    Function.Surjective (sylvesterOperator (jordan211Root data)) := by
  intro rhs
  exact ⟨jordan211SylvesterInverse data rhs,
    jordan211Sylvester_inverse_apply data rhs⟩

theorem jordan211Sylvester_injective (data : Jordan211Data) :
    Function.Injective (sylvesterOperator (jordan211Root data)) := by
  have hSurjective : Function.Surjective
      (sylvesterOperator (jordan211Root data)).toLinearMap :=
    jordan211Sylvester_surjective data
  exact LinearMap.injective_iff_surjective.mpr hSurjective

theorem jordan211Sylvester_bijective (data : Jordan211Data) :
    Function.Bijective (sylvesterOperator (jordan211Root data)) :=
  ⟨jordan211Sylvester_injective data, jordan211Sylvester_surjective data⟩

end

end P0EFTJanusPositiveJordanTwoPlusOnePlusOneRoot4D
end JanusFormal
