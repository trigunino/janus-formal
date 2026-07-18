import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanTwoPlusTwoRoot4D

/-!
# Positive real Jordan roots on the `3 + 1` primary stratum

This gate closes the supplied real primary decomposition formed by one
size-three Jordan block and one singleton, both with arbitrary strictly
positive eigenvalues.  The canonical binomial root is transported through a
supplied similarity.  Its Sylvester inverse is the five-term finite Neumann
series forced by the cube-zero root nilpotent.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveJordanThreePlusOneRoot4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveDiagonalSylvesterInverse
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
open P0EFTJanusPositiveJordanTwoPlusTwoRoot4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalSylvesterInverse.Matrix4

def jordan31RootSpectrum
    (triple singleton : PositiveEigenvalue) : PositiveDiagonalSpectrum :=
  ⟨![Real.sqrt triple.1, Real.sqrt triple.1, Real.sqrt triple.1,
      Real.sqrt singleton.1], by
    change ∀ i, 0 < ![Real.sqrt triple.1, Real.sqrt triple.1,
      Real.sqrt triple.1, Real.sqrt singleton.1] i
    intro i
    fin_cases i
    · exact Real.sqrt_pos.2 triple.2
    · exact Real.sqrt_pos.2 triple.2
    · exact Real.sqrt_pos.2 triple.2
    · exact Real.sqrt_pos.2 singleton.2⟩

def jordan31TargetSpectrum
    (triple singleton : PositiveEigenvalue) : Fin 4 → Real :=
  ![triple.1, triple.1, triple.1, singleton.1]

def jordan31DiagonalRoot
    (triple singleton : PositiveEigenvalue) : Matrix4 :=
  Matrix.diagonal (jordan31RootSpectrum triple singleton).1

def jordan31DiagonalTarget
    (triple singleton : PositiveEigenvalue) : Matrix4 :=
  Matrix.diagonal (jordan31TargetSpectrum triple singleton)

def jordan31SecondOffDiagonal (eigenvalue : PositiveEigenvalue) : Real :=
  -(8 * (Real.sqrt eigenvalue.1) ^ 3)⁻¹

def jordan31RootNilpotent
    (triple _singleton : PositiveEigenvalue) : Matrix4 :=
  ![![0, jordan22RootOffDiagonal triple,
      jordan31SecondOffDiagonal triple, 0],
    ![0, 0, jordan22RootOffDiagonal triple, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

def jordan31TargetNilpotent : Matrix4 :=
  ![![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

def canonicalJordan31Root
    (triple singleton : PositiveEigenvalue) : Matrix4 :=
  jordan31DiagonalRoot triple singleton +
    jordan31RootNilpotent triple singleton

def canonicalJordan31Target
    (triple singleton : PositiveEigenvalue) : Matrix4 :=
  jordan31DiagonalTarget triple singleton + jordan31TargetNilpotent

theorem jordan31RootNilpotent_cube
    (triple singleton : PositiveEigenvalue) :
    jordan31RootNilpotent triple singleton *
          jordan31RootNilpotent triple singleton *
        jordan31RootNilpotent triple singleton = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordan31RootNilpotent, Matrix.mul_apply, Fin.sum_univ_four]

theorem jordan31DiagonalRoot_commutes_nilpotent
    (triple singleton : PositiveEigenvalue) :
    jordan31DiagonalRoot triple singleton *
        jordan31RootNilpotent triple singleton =
      jordan31RootNilpotent triple singleton *
        jordan31DiagonalRoot triple singleton := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordan31DiagonalRoot, jordan31RootSpectrum,
      jordan31RootNilpotent, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem canonicalJordan31Root_square
    (triple singleton : PositiveEigenvalue) :
    canonicalJordan31Root triple singleton *
        canonicalJordan31Root triple singleton =
      canonicalJordan31Target triple singleton := by
  have hTripleSquare : Real.sqrt triple.1 * Real.sqrt triple.1 = triple.1 :=
    Real.mul_self_sqrt (le_of_lt triple.2)
  have hSingletonSquare :
      Real.sqrt singleton.1 * Real.sqrt singleton.1 = singleton.1 :=
    Real.mul_self_sqrt (le_of_lt singleton.2)
  have hTripleNe : Real.sqrt triple.1 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 triple.2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalJordan31Root, canonicalJordan31Target,
      jordan31DiagonalRoot, jordan31DiagonalTarget, jordan31RootSpectrum,
      jordan31TargetSpectrum, jordan31RootNilpotent,
      jordan31TargetNilpotent, jordan22RootOffDiagonal,
      jordan31SecondOffDiagonal, Matrix.mul_apply, Fin.sum_univ_four,
      hTripleSquare, hSingletonSquare] <;>
    field_simp [hTripleNe] <;> ring

abbrev RawJordan31Data :=
  (PositiveEigenvalue × PositiveEigenvalue) × (Matrix4 × Matrix4)

def jordan31SimilarityLocus : Set RawJordan31Data :=
  {data | data.2.2 * data.2.1 = 1 ∧ data.2.1 * data.2.2 = 1}

abbrev Jordan31Data := jordan31SimilarityLocus

def tripleEigenvalue (data : Jordan31Data) : PositiveEigenvalue := data.1.1.1

def singletonEigenvalue (data : Jordan31Data) : PositiveEigenvalue := data.1.1.2

def jordan31Change (data : Jordan31Data) : Matrix4 := data.1.2.1

def jordan31Inverse (data : Jordan31Data) : Matrix4 := data.1.2.2

def jordan31Target (data : Jordan31Data) : Matrix4 :=
  jordan31Change data *
    canonicalJordan31Target (tripleEigenvalue data)
      (singletonEigenvalue data) * jordan31Inverse data

def jordan31Root (data : Jordan31Data) : Matrix4 :=
  jordan31Change data *
    canonicalJordan31Root (tripleEigenvalue data)
      (singletonEigenvalue data) * jordan31Inverse data

theorem jordan31Inverse_change (data : Jordan31Data) :
    jordan31Inverse data * jordan31Change data = 1 :=
  data.property.1

theorem jordan31Change_inverse (data : Jordan31Data) :
    jordan31Change data * jordan31Inverse data = 1 :=
  data.property.2

theorem jordan31Root_square (data : Jordan31Data) :
    jordan31Root data * jordan31Root data = jordan31Target data := by
  have hCanonical := canonicalJordan31Root_square
    (tripleEigenvalue data) (singletonEigenvalue data)
  have hInverseChange := jordan31Inverse_change data
  unfold jordan31Root jordan31Target
  calc
    (jordan31Change data *
          canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data) * jordan31Inverse data) *
        (jordan31Change data *
          canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data) * jordan31Inverse data) =
      jordan31Change data *
        canonicalJordan31Root (tripleEigenvalue data)
          (singletonEigenvalue data) *
        (jordan31Inverse data * jordan31Change data) *
        canonicalJordan31Root (tripleEigenvalue data)
          (singletonEigenvalue data) * jordan31Inverse data := by noncomm_ring
    _ = jordan31Change data *
        (canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data) *
          canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data)) * jordan31Inverse data := by
      rw [hInverseChange]
      simp [mul_assoc]
    _ = jordan31Change data *
        canonicalJordan31Target (tripleEigenvalue data)
          (singletonEigenvalue data) * jordan31Inverse data := by rw [hCanonical]

def rebaseJordan31Data
    (data : Jordan31Data) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) : Jordan31Data :=
  ⟨⟨data.1.1,
      ⟨change * jordan31Change data, jordan31Inverse data * inverse⟩⟩, by
    constructor
    · change (jordan31Inverse data * inverse) *
        (change * jordan31Change data) = 1
      calc
        (jordan31Inverse data * inverse) *
            (change * jordan31Change data) =
          jordan31Inverse data * (inverse * change) *
            jordan31Change data := by noncomm_ring
        _ = jordan31Inverse data * jordan31Change data := by
          rw [hInverseChange]
          simp
        _ = 1 := jordan31Inverse_change data
    · change (change * jordan31Change data) *
        (jordan31Inverse data * inverse) = 1
      calc
        (change * jordan31Change data) *
            (jordan31Inverse data * inverse) =
          change * (jordan31Change data * jordan31Inverse data) *
            inverse := by noncomm_ring
        _ = change * inverse := by rw [jordan31Change_inverse]; simp
        _ = 1 := hChangeInverse⟩

theorem jordan31Root_rebase
    (data : Jordan31Data) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    jordan31Root
        (rebaseJordan31Data data change inverse hInverseChange hChangeInverse) =
      change * jordan31Root data * inverse := by
  unfold jordan31Root rebaseJordan31Data tripleEigenvalue singletonEigenvalue
    jordan31Change jordan31Inverse
  noncomm_ring

@[fun_prop]
theorem jordan31SecondOffDiagonal_continuous :
    Continuous jordan31SecondOffDiagonal := by
  have hSqrt : Continuous
      (fun eigenvalue : PositiveEigenvalue => Real.sqrt eigenvalue.1) :=
    Real.continuous_sqrt.comp continuous_subtype_val
  have hDenominator : Continuous
      (fun eigenvalue : PositiveEigenvalue =>
        8 * (Real.sqrt eigenvalue.1) ^ 3) :=
    continuous_const.mul (hSqrt.pow 3)
  unfold jordan31SecondOffDiagonal
  exact (hDenominator.inv₀ (fun eigenvalue hZero =>
    (mul_ne_zero (by norm_num)
      (pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.2 eigenvalue.2)))) hZero)).neg

theorem canonicalJordan31Root_continuous :
    Continuous (fun data : PositiveEigenvalue × PositiveEigenvalue =>
      canonicalJordan31Root data.1 data.2) := by
  apply continuous_matrix
  intro i j
  have hFirst : Continuous
      (fun data : PositiveEigenvalue × PositiveEigenvalue =>
        jordan22RootOffDiagonal data.1) :=
    jordan22RootOffDiagonal_continuous.comp continuous_fst
  have hSecond : Continuous
      (fun data : PositiveEigenvalue × PositiveEigenvalue =>
        jordan31SecondOffDiagonal data.1) :=
    jordan31SecondOffDiagonal_continuous.comp continuous_fst
  fin_cases i <;> fin_cases j <;>
    simp [canonicalJordan31Root, jordan31DiagonalRoot,
      jordan31RootSpectrum, jordan31RootNilpotent]
  all_goals first | exact hFirst | exact hSecond | fun_prop

theorem jordan31Root_continuous : Continuous jordan31Root := by
  have hEigenvalues : Continuous
      (fun data : Jordan31Data => data.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hCanonical : Continuous
      (fun data : Jordan31Data =>
        canonicalJordan31Root (tripleEigenvalue data)
          (singletonEigenvalue data)) :=
    canonicalJordan31Root_continuous.comp hEigenvalues
  have hChange : Continuous jordan31Change := by
    unfold jordan31Change
    fun_prop
  have hInverse : Continuous jordan31Inverse := by
    unfold jordan31Inverse
    fun_prop
  unfold jordan31Root
  exact (hChange.matrix_mul hCanonical).matrix_mul hInverse

def jordan31SylvesterPerturbation
    (triple singleton : PositiveEigenvalue) : Matrix4 →L[Real] Matrix4 :=
  sylvesterOperator (jordan31RootNilpotent triple singleton)

def jordan31SylvesterCorrection
    (triple singleton : PositiveEigenvalue) : Matrix4 →L[Real] Matrix4 :=
  (diagonalSylvesterInverse (jordan31RootSpectrum triple singleton)).comp
    (jordan31SylvesterPerturbation triple singleton)

theorem jordan31SylvesterPerturbation_fifth
    (triple singleton : PositiveEigenvalue) (variation : Matrix4) :
    jordan31SylvesterPerturbation triple singleton
      (jordan31SylvesterPerturbation triple singleton
        (jordan31SylvesterPerturbation triple singleton
          (jordan31SylvesterPerturbation triple singleton
            (jordan31SylvesterPerturbation triple singleton variation)))) = 0 := by
  let nilpotent := jordan31RootNilpotent triple singleton
  have hCube : nilpotent * nilpotent * nilpotent = 0 :=
    jordan31RootNilpotent_cube triple singleton
  have hLeft (matrix : Matrix4) :
      nilpotent * (nilpotent * (nilpotent * matrix)) = 0 := by
    rw [← mul_assoc, ← mul_assoc, hCube, zero_mul]
  simp only [jordan31SylvesterPerturbation, sylvesterOperator_apply]
  change
    nilpotent *
          (nilpotent *
              (nilpotent *
                  (nilpotent * (nilpotent * variation + variation * nilpotent) +
                    (nilpotent * variation + variation * nilpotent) *
                      nilpotent) +
                (nilpotent * (nilpotent * variation + variation * nilpotent) +
                    (nilpotent * variation + variation * nilpotent) *
                      nilpotent) * nilpotent) +
            (nilpotent *
                (nilpotent * (nilpotent * variation + variation * nilpotent) +
                  (nilpotent * variation + variation * nilpotent) * nilpotent) +
              (nilpotent * (nilpotent * variation + variation * nilpotent) +
                  (nilpotent * variation + variation * nilpotent) * nilpotent) *
                nilpotent) * nilpotent) +
      (nilpotent *
            (nilpotent *
                (nilpotent * (nilpotent * variation + variation * nilpotent) +
                  (nilpotent * variation + variation * nilpotent) * nilpotent) +
              (nilpotent * (nilpotent * variation + variation * nilpotent) +
                  (nilpotent * variation + variation * nilpotent) * nilpotent) *
                nilpotent) +
          (nilpotent *
              (nilpotent * (nilpotent * variation + variation * nilpotent) +
                (nilpotent * variation + variation * nilpotent) * nilpotent) +
            (nilpotent * (nilpotent * variation + variation * nilpotent) +
                (nilpotent * variation + variation * nilpotent) * nilpotent) *
              nilpotent) * nilpotent) * nilpotent = 0
  noncomm_ring [hCube]
  simp only [hLeft, mul_zero, smul_zero, add_zero]

theorem jordan31Diagonal_perturbation_commute
    (triple singleton : PositiveEigenvalue) (variation : Matrix4) :
    sylvesterOperator (jordan31DiagonalRoot triple singleton)
        (jordan31SylvesterPerturbation triple singleton variation) =
      jordan31SylvesterPerturbation triple singleton
        (sylvesterOperator (jordan31DiagonalRoot triple singleton)
          variation) := by
  have hCommutes := jordan31DiagonalRoot_commutes_nilpotent triple singleton
  have hCommutesRight (matrix : Matrix4) :
      jordan31DiagonalRoot triple singleton *
          (jordan31RootNilpotent triple singleton * matrix) =
        jordan31RootNilpotent triple singleton *
          (jordan31DiagonalRoot triple singleton * matrix) := by
    rw [← mul_assoc, hCommutes, mul_assoc]
  simp only [jordan31SylvesterPerturbation, sylvesterOperator_apply]
  noncomm_ring [hCommutes]
  rw [hCommutesRight]
  module

theorem jordan31DiagonalInverse_perturbation_commute
    (triple singleton : PositiveEigenvalue) (variation : Matrix4) :
    diagonalSylvesterInverse (jordan31RootSpectrum triple singleton)
        (jordan31SylvesterPerturbation triple singleton variation) =
      jordan31SylvesterPerturbation triple singleton
        (diagonalSylvesterInverse (jordan31RootSpectrum triple singleton)
          variation) := by
  apply Function.LeftInverse.injective
    (diagonalSylvesterInverse_left (jordan31RootSpectrum triple singleton))
  calc
    sylvesterOperator (jordan31DiagonalRoot triple singleton)
        (diagonalSylvesterInverse (jordan31RootSpectrum triple singleton)
          (jordan31SylvesterPerturbation triple singleton variation)) =
      jordan31SylvesterPerturbation triple singleton variation := by
        exact diagonalSylvesterInverse_right
          (jordan31RootSpectrum triple singleton)
          (jordan31SylvesterPerturbation triple singleton variation)
    _ = jordan31SylvesterPerturbation triple singleton
        (sylvesterOperator (jordan31DiagonalRoot triple singleton)
          (diagonalSylvesterInverse (jordan31RootSpectrum triple singleton)
            variation)) := by
      congr 1
      exact (diagonalSylvesterInverse_right
        (jordan31RootSpectrum triple singleton) variation).symm
    _ = sylvesterOperator (jordan31DiagonalRoot triple singleton)
        (jordan31SylvesterPerturbation triple singleton
          (diagonalSylvesterInverse (jordan31RootSpectrum triple singleton)
            variation)) := by
      exact (jordan31Diagonal_perturbation_commute triple singleton
        (diagonalSylvesterInverse (jordan31RootSpectrum triple singleton)
          variation)).symm

theorem jordan31SylvesterCorrection_fifth
    (triple singleton : PositiveEigenvalue) (variation : Matrix4) :
    jordan31SylvesterCorrection triple singleton
      (jordan31SylvesterCorrection triple singleton
        (jordan31SylvesterCorrection triple singleton
          (jordan31SylvesterCorrection triple singleton
            (jordan31SylvesterCorrection triple singleton variation)))) = 0 := by
  let inverseDiagonal : Module.End Real Matrix4 :=
    (diagonalSylvesterInverse
      (jordan31RootSpectrum triple singleton)).toLinearMap
  let perturbation : Module.End Real Matrix4 :=
    (jordan31SylvesterPerturbation triple singleton).toLinearMap
  have hCommute : Commute inverseDiagonal perturbation := by
    apply LinearMap.ext
    intro rhs
    exact jordan31DiagonalInverse_perturbation_commute triple singleton rhs
  have hPerturbationPow : perturbation ^ 5 = 0 := by
    apply LinearMap.ext
    intro rhs
    exact jordan31SylvesterPerturbation_fifth triple singleton rhs
  have hProduct : (inverseDiagonal * perturbation) ^ 5 = 0 := by
    rw [hCommute.mul_pow, hPerturbationPow, mul_zero]
  change ((inverseDiagonal * perturbation) ^ 5) variation = 0
  rw [hProduct]
  rfl

def canonicalJordan31SylvesterInverse
    (triple singleton : PositiveEigenvalue) : Matrix4 →L[Real] Matrix4 :=
  let correction := jordan31SylvesterCorrection triple singleton
  let square := correction.comp correction
  let cube := correction.comp square
  let fourth := correction.comp cube
  ((((ContinuousLinearMap.id Real Matrix4 - correction) + square) - cube) +
      fourth).comp
    (diagonalSylvesterInverse (jordan31RootSpectrum triple singleton))

theorem canonicalJordan31Sylvester_decompose
    (triple singleton : PositiveEigenvalue) (variation : Matrix4) :
    sylvesterOperator (canonicalJordan31Root triple singleton) variation =
      sylvesterOperator (jordan31DiagonalRoot triple singleton) variation +
        jordan31SylvesterPerturbation triple singleton variation := by
  unfold canonicalJordan31Root jordan31SylvesterPerturbation
  simp only [sylvesterOperator_apply]
  noncomm_ring

theorem canonicalJordan31SylvesterInverse_left
    (triple singleton : PositiveEigenvalue) (variation : Matrix4) :
    canonicalJordan31SylvesterInverse triple singleton
        (sylvesterOperator (canonicalJordan31Root triple singleton) variation) =
      variation := by
  have hBase :
      diagonalSylvesterInverse (jordan31RootSpectrum triple singleton)
          (sylvesterOperator (canonicalJordan31Root triple singleton)
            variation) =
        variation + jordan31SylvesterCorrection triple singleton variation := by
    rw [canonicalJordan31Sylvester_decompose, map_add]
    change diagonalSylvesterInverse (jordan31RootSpectrum triple singleton)
          (sylvesterOperator
            (Matrix.diagonal (jordan31RootSpectrum triple singleton).1)
            variation) +
        diagonalSylvesterInverse (jordan31RootSpectrum triple singleton)
          (jordan31SylvesterPerturbation triple singleton variation) =
      variation + jordan31SylvesterCorrection triple singleton variation
    rw [diagonalSylvesterInverse_left]
    rfl
  unfold canonicalJordan31SylvesterInverse
  simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply,
    ContinuousLinearMap.id_apply]
  rw [hBase]
  simp only [map_add]
  rw [jordan31SylvesterCorrection_fifth]
  module

theorem canonicalJordan31Sylvester_injective
    (triple singleton : PositiveEigenvalue) :
    Function.Injective
      (sylvesterOperator (canonicalJordan31Root triple singleton)) :=
  Function.LeftInverse.injective
    (canonicalJordan31SylvesterInverse_left triple singleton)

theorem canonicalJordan31Sylvester_surjective
    (triple singleton : PositiveEigenvalue) :
    Function.Surjective
      (sylvesterOperator (canonicalJordan31Root triple singleton)) := by
  have hInjective : Function.Injective
      (sylvesterOperator
        (canonicalJordan31Root triple singleton)).toLinearMap :=
    canonicalJordan31Sylvester_injective triple singleton
  exact LinearMap.injective_iff_surjective.mp hInjective

theorem canonicalJordan31SylvesterInverse_right
    (triple singleton : PositiveEigenvalue) (rhs : Matrix4) :
    sylvesterOperator (canonicalJordan31Root triple singleton)
        (canonicalJordan31SylvesterInverse triple singleton rhs) = rhs := by
  obtain ⟨variation, hVariation⟩ :=
    canonicalJordan31Sylvester_surjective triple singleton rhs
  rw [← hVariation, canonicalJordan31SylvesterInverse_left]

def jordan31SylvesterInverse
    (data : Jordan31Data) (rhs : Matrix4) : Matrix4 :=
  jordan31Change data *
    canonicalJordan31SylvesterInverse
      (tripleEigenvalue data) (singletonEigenvalue data)
      (jordan31Inverse data * rhs * jordan31Change data) *
    jordan31Inverse data

theorem jordan31Sylvester_inverse_apply
    (data : Jordan31Data) (rhs : Matrix4) :
    sylvesterOperator (jordan31Root data)
        (jordan31SylvesterInverse data rhs) = rhs := by
  let canonicalVariation := canonicalJordan31SylvesterInverse
    (tripleEigenvalue data) (singletonEigenvalue data)
    (jordan31Inverse data * rhs * jordan31Change data)
  have hCanonical :
      sylvesterOperator
          (canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data)) canonicalVariation =
        jordan31Inverse data * rhs * jordan31Change data :=
    canonicalJordan31SylvesterInverse_right
      (tripleEigenvalue data) (singletonEigenvalue data)
      (jordan31Inverse data * rhs * jordan31Change data)
  have hInverseChange := jordan31Inverse_change data
  have hChangeInverse := jordan31Change_inverse data
  unfold jordan31Root jordan31SylvesterInverse
  change sylvesterOperator
      (jordan31Change data *
          canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data) * jordan31Inverse data)
      (jordan31Change data * canonicalVariation * jordan31Inverse data) = rhs
  simp only [sylvesterOperator_apply] at hCanonical ⊢
  have hFirstProduct :
      (jordan31Change data *
            canonicalJordan31Root (tripleEigenvalue data)
              (singletonEigenvalue data) * jordan31Inverse data) *
          (jordan31Change data * canonicalVariation * jordan31Inverse data) =
        jordan31Change data *
          (canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data) * canonicalVariation) *
          jordan31Inverse data := by
    calc
      _ = jordan31Change data *
          canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data) *
          (jordan31Inverse data * jordan31Change data) * canonicalVariation *
          jordan31Inverse data := by noncomm_ring
      _ = _ := by rw [hInverseChange]; simp [mul_assoc]
  have hSecondProduct :
      (jordan31Change data * canonicalVariation * jordan31Inverse data) *
          (jordan31Change data *
            canonicalJordan31Root (tripleEigenvalue data)
              (singletonEigenvalue data) * jordan31Inverse data) =
        jordan31Change data *
          (canonicalVariation * canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data)) * jordan31Inverse data := by
    calc
      _ = jordan31Change data * canonicalVariation *
          (jordan31Inverse data * jordan31Change data) *
          canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data) * jordan31Inverse data := by noncomm_ring
      _ = _ := by rw [hInverseChange]; simp [mul_assoc]
  calc
    _ = jordan31Change data *
        (canonicalJordan31Root (tripleEigenvalue data)
              (singletonEigenvalue data) * canonicalVariation +
          canonicalVariation * canonicalJordan31Root (tripleEigenvalue data)
            (singletonEigenvalue data)) * jordan31Inverse data := by
      rw [hFirstProduct, hSecondProduct]
      noncomm_ring
    _ = jordan31Change data *
        (jordan31Inverse data * rhs * jordan31Change data) *
          jordan31Inverse data := by rw [hCanonical]
    _ = rhs := by
      calc
        _ = (jordan31Change data * jordan31Inverse data) * rhs *
            (jordan31Change data * jordan31Inverse data) := by noncomm_ring
        _ = rhs := by rw [hChangeInverse]; simp

theorem jordan31Sylvester_surjective (data : Jordan31Data) :
    Function.Surjective (sylvesterOperator (jordan31Root data)) := by
  intro rhs
  exact ⟨jordan31SylvesterInverse data rhs,
    jordan31Sylvester_inverse_apply data rhs⟩

theorem jordan31Sylvester_injective (data : Jordan31Data) :
    Function.Injective (sylvesterOperator (jordan31Root data)) := by
  have hSurjective : Function.Surjective
      (sylvesterOperator (jordan31Root data)).toLinearMap :=
    jordan31Sylvester_surjective data
  exact LinearMap.injective_iff_surjective.mpr hSurjective

theorem jordan31Sylvester_bijective (data : Jordan31Data) :
    Function.Bijective (sylvesterOperator (jordan31Root data)) :=
  ⟨jordan31Sylvester_injective data, jordan31Sylvester_surjective data⟩

end

end P0EFTJanusPositiveJordanThreePlusOneRoot4D
end JanusFormal
