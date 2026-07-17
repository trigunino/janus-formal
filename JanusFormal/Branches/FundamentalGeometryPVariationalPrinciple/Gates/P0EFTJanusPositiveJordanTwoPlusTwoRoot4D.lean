import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalSylvesterInverse

/-!
# Positive real Jordan roots on the `2 + 2` primary stratum

This gate treats a supplied real primary decomposition consisting of two
Jordan blocks of size two.  Both eigenvalues are arbitrary and strictly
positive.  The canonical binomial roots are transported by a supplied
similarity, vary continuously on the fixed stratum, and have bijective
Sylvester linearization.

The remaining positive real Jordan partitions of dimension four are isolated
explicitly; no claim about nonpositive or complex spectrum is made here.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveJordanTwoPlusTwoRoot4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveDiagonalSylvesterInverse
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalSylvesterInverse.Matrix4

/-- Positive root eigenvalues repeated on their two canonical blocks. -/
def jordan22RootSpectrum
    (first second : PositiveEigenvalue) : PositiveDiagonalSpectrum :=
  ⟨![Real.sqrt first.1, Real.sqrt first.1,
      Real.sqrt second.1, Real.sqrt second.1], by
    change ∀ i, 0 < ![Real.sqrt first.1, Real.sqrt first.1,
      Real.sqrt second.1, Real.sqrt second.1] i
    intro i
    fin_cases i
    · exact Real.sqrt_pos.2 first.2
    · exact Real.sqrt_pos.2 first.2
    · exact Real.sqrt_pos.2 second.2
    · exact Real.sqrt_pos.2 second.2⟩

def jordan22TargetSpectrum
    (first second : PositiveEigenvalue) : Fin 4 → Real :=
  ![first.1, first.1, second.1, second.1]

def jordan22DiagonalRoot
    (first second : PositiveEigenvalue) : Matrix4 :=
  Matrix.diagonal (jordan22RootSpectrum first second).1

def jordan22DiagonalTarget
    (first second : PositiveEigenvalue) : Matrix4 :=
  Matrix.diagonal (jordan22TargetSpectrum first second)

def jordan22RootOffDiagonal (eigenvalue : PositiveEigenvalue) : Real :=
  (2 * Real.sqrt eigenvalue.1)⁻¹

/-- Nilpotent part of the root on the two standard Jordan blocks. -/
def jordan22RootNilpotent
    (first second : PositiveEigenvalue) : Matrix4 :=
  ![![0, jordan22RootOffDiagonal first, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, jordan22RootOffDiagonal second],
    ![0, 0, 0, 0]]

/-- Unit superdiagonal nilpotents of the two target Jordan blocks. -/
def jordan22TargetNilpotent : Matrix4 :=
  ![![0, 1, 0, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 1],
    ![0, 0, 0, 0]]

def canonicalJordan22Root
    (first second : PositiveEigenvalue) : Matrix4 :=
  jordan22DiagonalRoot first second + jordan22RootNilpotent first second

def canonicalJordan22Target
    (first second : PositiveEigenvalue) : Matrix4 :=
  jordan22DiagonalTarget first second + jordan22TargetNilpotent

theorem jordan22RootNilpotent_square
    (first second : PositiveEigenvalue) :
    jordan22RootNilpotent first second *
        jordan22RootNilpotent first second = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordan22RootNilpotent, Matrix.mul_apply, Fin.sum_univ_four]

theorem jordan22DiagonalRoot_commutes_nilpotent
    (first second : PositiveEigenvalue) :
    jordan22DiagonalRoot first second * jordan22RootNilpotent first second =
      jordan22RootNilpotent first second *
        jordan22DiagonalRoot first second := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordan22DiagonalRoot, jordan22RootSpectrum,
      jordan22RootNilpotent, jordan22RootOffDiagonal, Matrix.mul_apply,
      Fin.sum_univ_four] <;> ring

theorem jordan22DiagonalRoot_square
    (first second : PositiveEigenvalue) :
    jordan22DiagonalRoot first second * jordan22DiagonalRoot first second =
      jordan22DiagonalTarget first second := by
  have hFirst : Real.sqrt first.1 * Real.sqrt first.1 = first.1 :=
    Real.mul_self_sqrt (le_of_lt first.2)
  have hSecond : Real.sqrt second.1 * Real.sqrt second.1 = second.1 :=
    Real.mul_self_sqrt (le_of_lt second.2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordan22DiagonalRoot, jordan22RootSpectrum,
      jordan22DiagonalTarget, jordan22TargetSpectrum, Matrix.mul_apply,
      Fin.sum_univ_four, hFirst, hSecond]

theorem jordan22DiagonalRoot_nilpotent_cross
    (first second : PositiveEigenvalue) :
    jordan22DiagonalRoot first second * jordan22RootNilpotent first second +
        jordan22RootNilpotent first second *
          jordan22DiagonalRoot first second =
      jordan22TargetNilpotent := by
  have hFirstNe : Real.sqrt first.1 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 first.2)
  have hSecondNe : Real.sqrt second.1 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 second.2)
  have hFirst :
      Real.sqrt first.1 * ((Real.sqrt first.1)⁻¹ * 2⁻¹) +
          (Real.sqrt first.1)⁻¹ * 2⁻¹ * Real.sqrt first.1 = 1 := by
    field_simp [hFirstNe]
    ring
  have hSecond :
      Real.sqrt second.1 * ((Real.sqrt second.1)⁻¹ * 2⁻¹) +
          (Real.sqrt second.1)⁻¹ * 2⁻¹ * Real.sqrt second.1 = 1 := by
    field_simp [hSecondNe]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordan22DiagonalRoot, jordan22RootSpectrum,
      jordan22RootNilpotent, jordan22RootOffDiagonal,
      jordan22TargetNilpotent, Matrix.mul_apply, Fin.sum_univ_four,
      hFirst, hSecond]

theorem canonicalJordan22Root_square
    (first second : PositiveEigenvalue) :
    canonicalJordan22Root first second * canonicalJordan22Root first second =
      canonicalJordan22Target first second := by
  have hDiagonal := jordan22DiagonalRoot_square first second
  have hNilpotent := jordan22RootNilpotent_square first second
  have hCross := jordan22DiagonalRoot_nilpotent_cross first second
  unfold canonicalJordan22Root canonicalJordan22Target
  calc
    (jordan22DiagonalRoot first second +
          jordan22RootNilpotent first second) *
        (jordan22DiagonalRoot first second +
          jordan22RootNilpotent first second) =
      jordan22DiagonalRoot first second * jordan22DiagonalRoot first second +
        (jordan22DiagonalRoot first second *
            jordan22RootNilpotent first second +
          jordan22RootNilpotent first second *
            jordan22DiagonalRoot first second) +
        jordan22RootNilpotent first second *
          jordan22RootNilpotent first second := by noncomm_ring
    _ = jordan22DiagonalTarget first second + jordan22TargetNilpotent := by
      rw [hDiagonal, hCross, hNilpotent]
      simp

/-- Raw coordinates of a fixed `2 + 2` Jordan stratum: two positive
eigenvalues and a change-of-basis/inverse pair. -/
abbrev RawJordan22Data :=
  (PositiveEigenvalue × PositiveEigenvalue) × (Matrix4 × Matrix4)

def jordan22SimilarityLocus : Set RawJordan22Data :=
  {data | data.2.2 * data.2.1 = 1 ∧ data.2.1 * data.2.2 = 1}

abbrev Jordan22Data := jordan22SimilarityLocus

def firstEigenvalue (data : Jordan22Data) : PositiveEigenvalue := data.1.1.1

def secondEigenvalue (data : Jordan22Data) : PositiveEigenvalue := data.1.1.2

def jordan22Change (data : Jordan22Data) : Matrix4 := data.1.2.1

def jordan22Inverse (data : Jordan22Data) : Matrix4 := data.1.2.2

def jordan22Target (data : Jordan22Data) : Matrix4 :=
  jordan22Change data *
    canonicalJordan22Target (firstEigenvalue data) (secondEigenvalue data) *
      jordan22Inverse data

def jordan22Root (data : Jordan22Data) : Matrix4 :=
  jordan22Change data *
    canonicalJordan22Root (firstEigenvalue data) (secondEigenvalue data) *
      jordan22Inverse data

theorem jordan22Inverse_change (data : Jordan22Data) :
    jordan22Inverse data * jordan22Change data = 1 :=
  data.property.1

theorem jordan22Change_inverse (data : Jordan22Data) :
    jordan22Change data * jordan22Inverse data = 1 :=
  data.property.2

theorem jordan22Root_square (data : Jordan22Data) :
    jordan22Root data * jordan22Root data = jordan22Target data := by
  have hCanonical := canonicalJordan22Root_square
    (firstEigenvalue data) (secondEigenvalue data)
  have hInverseChange := jordan22Inverse_change data
  unfold jordan22Root jordan22Target
  calc
    (jordan22Change data *
          canonicalJordan22Root (firstEigenvalue data) (secondEigenvalue data) *
        jordan22Inverse data) *
        (jordan22Change data *
            canonicalJordan22Root (firstEigenvalue data)
              (secondEigenvalue data) *
          jordan22Inverse data) =
      jordan22Change data *
        canonicalJordan22Root (firstEigenvalue data) (secondEigenvalue data) *
        (jordan22Inverse data * jordan22Change data) *
        canonicalJordan22Root (firstEigenvalue data) (secondEigenvalue data) *
        jordan22Inverse data := by noncomm_ring
    _ = jordan22Change data *
        (canonicalJordan22Root (firstEigenvalue data)
          (secondEigenvalue data) *
        canonicalJordan22Root (firstEigenvalue data)
          (secondEigenvalue data)) * jordan22Inverse data := by
      rw [hInverseChange]
      simp [mul_assoc]
    _ = jordan22Change data *
        canonicalJordan22Target (firstEigenvalue data)
          (secondEigenvalue data) * jordan22Inverse data := by rw [hCanonical]

/-- Rebase the supplied primary decomposition by another similarity. -/
def rebaseJordan22Data
    (data : Jordan22Data) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) : Jordan22Data :=
  ⟨⟨data.1.1,
      ⟨change * jordan22Change data, jordan22Inverse data * inverse⟩⟩, by
    constructor
    · change (jordan22Inverse data * inverse) *
        (change * jordan22Change data) = 1
      calc
        (jordan22Inverse data * inverse) *
            (change * jordan22Change data) =
          jordan22Inverse data * (inverse * change) *
            jordan22Change data := by noncomm_ring
        _ = jordan22Inverse data * jordan22Change data := by
          rw [hInverseChange]
          simp
        _ = 1 := jordan22Inverse_change data
    · change (change * jordan22Change data) *
        (jordan22Inverse data * inverse) = 1
      calc
        (change * jordan22Change data) *
            (jordan22Inverse data * inverse) =
          change * (jordan22Change data * jordan22Inverse data) *
            inverse := by noncomm_ring
        _ = change * inverse := by
          rw [jordan22Change_inverse]
          simp
        _ = 1 := hChangeInverse⟩

theorem jordan22Root_rebase
    (data : Jordan22Data) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    jordan22Root
        (rebaseJordan22Data data change inverse hInverseChange hChangeInverse) =
      change * jordan22Root data * inverse := by
  unfold jordan22Root rebaseJordan22Data firstEigenvalue secondEigenvalue
    jordan22Change jordan22Inverse
  noncomm_ring

@[fun_prop]
theorem jordan22RootOffDiagonal_continuous :
    Continuous jordan22RootOffDiagonal := by
  have hSqrt : Continuous
      (fun eigenvalue : PositiveEigenvalue => Real.sqrt eigenvalue.1) :=
    Real.continuous_sqrt.comp continuous_subtype_val
  unfold jordan22RootOffDiagonal
  exact (continuous_const.mul hSqrt).inv₀ (fun eigenvalue hZero => by
    exact (mul_ne_zero (by norm_num)
      (ne_of_gt (Real.sqrt_pos.2 eigenvalue.2))) hZero)

theorem canonicalJordan22Root_continuous :
    Continuous (fun data : PositiveEigenvalue × PositiveEigenvalue =>
      canonicalJordan22Root data.1 data.2) := by
  apply continuous_matrix
  intro i j
  have hFirst : Continuous
      (fun data : PositiveEigenvalue × PositiveEigenvalue =>
        jordan22RootOffDiagonal data.1) :=
    jordan22RootOffDiagonal_continuous.comp continuous_fst
  have hSecond : Continuous
      (fun data : PositiveEigenvalue × PositiveEigenvalue =>
        jordan22RootOffDiagonal data.2) :=
    jordan22RootOffDiagonal_continuous.comp continuous_snd
  fin_cases i <;> fin_cases j <;>
    simp [canonicalJordan22Root, jordan22DiagonalRoot, jordan22RootSpectrum,
      jordan22RootNilpotent]
  all_goals first | exact hFirst | exact hSecond | fun_prop

theorem jordan22Root_continuous : Continuous jordan22Root := by
  have hEigenvalues : Continuous
      (fun data : Jordan22Data => data.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hCanonical : Continuous
      (fun data : Jordan22Data =>
        canonicalJordan22Root (firstEigenvalue data) (secondEigenvalue data)) :=
    canonicalJordan22Root_continuous.comp hEigenvalues
  have hChange : Continuous jordan22Change := by
    unfold jordan22Change
    fun_prop
  have hInverse : Continuous jordan22Inverse := by
    unfold jordan22Inverse
    fun_prop
  unfold jordan22Root
  exact (hChange.matrix_mul hCanonical).matrix_mul hInverse

/-- Nilpotent perturbation of the diagonal Sylvester operator. -/
def jordan22SylvesterPerturbation
    (first second : PositiveEigenvalue) : Matrix4 →L[Real] Matrix4 :=
  sylvesterOperator (jordan22RootNilpotent first second)

/-- The normalized perturbation `L_D⁻¹ L_N`. -/
def jordan22SylvesterCorrection
    (first second : PositiveEigenvalue) : Matrix4 →L[Real] Matrix4 :=
  (diagonalSylvesterInverse (jordan22RootSpectrum first second)).comp
    (jordan22SylvesterPerturbation first second)

theorem jordan22SylvesterPerturbation_cube
    (first second : PositiveEigenvalue) (variation : Matrix4) :
    jordan22SylvesterPerturbation first second
        (jordan22SylvesterPerturbation first second
          (jordan22SylvesterPerturbation first second variation)) = 0 := by
  have hSquare := jordan22RootNilpotent_square first second
  have hLeft (matrix : Matrix4) :
      jordan22RootNilpotent first second *
          (jordan22RootNilpotent first second * matrix) = 0 := by
    rw [← mul_assoc, hSquare, zero_mul]
  simp only [jordan22SylvesterPerturbation, sylvesterOperator_apply]
  noncomm_ring [hSquare]
  simp only [hLeft, mul_zero, smul_zero, add_zero]

theorem jordan22Diagonal_perturbation_commute
    (first second : PositiveEigenvalue) (variation : Matrix4) :
    sylvesterOperator (jordan22DiagonalRoot first second)
        (jordan22SylvesterPerturbation first second variation) =
      jordan22SylvesterPerturbation first second
        (sylvesterOperator (jordan22DiagonalRoot first second) variation) := by
  have hCommutes := jordan22DiagonalRoot_commutes_nilpotent first second
  have hCommutesRight (matrix : Matrix4) :
      jordan22DiagonalRoot first second *
          (jordan22RootNilpotent first second * matrix) =
        jordan22RootNilpotent first second *
          (jordan22DiagonalRoot first second * matrix) := by
    rw [← mul_assoc, hCommutes, mul_assoc]
  simp only [jordan22SylvesterPerturbation, sylvesterOperator_apply]
  noncomm_ring [hCommutes]
  rw [hCommutesRight]
  module

theorem jordan22DiagonalInverse_perturbation_commute
    (first second : PositiveEigenvalue) (variation : Matrix4) :
    diagonalSylvesterInverse (jordan22RootSpectrum first second)
        (jordan22SylvesterPerturbation first second variation) =
      jordan22SylvesterPerturbation first second
        (diagonalSylvesterInverse (jordan22RootSpectrum first second)
          variation) := by
  apply Function.LeftInverse.injective
    (diagonalSylvesterInverse_left (jordan22RootSpectrum first second))
  calc
    sylvesterOperator (jordan22DiagonalRoot first second)
        (diagonalSylvesterInverse (jordan22RootSpectrum first second)
          (jordan22SylvesterPerturbation first second variation)) =
      jordan22SylvesterPerturbation first second variation := by
        exact diagonalSylvesterInverse_right
          (jordan22RootSpectrum first second)
          (jordan22SylvesterPerturbation first second variation)
    _ = jordan22SylvesterPerturbation first second
        (sylvesterOperator (jordan22DiagonalRoot first second)
          (diagonalSylvesterInverse (jordan22RootSpectrum first second)
            variation)) := by
      congr 1
      exact (diagonalSylvesterInverse_right
        (jordan22RootSpectrum first second) variation).symm
    _ = sylvesterOperator (jordan22DiagonalRoot first second)
        (jordan22SylvesterPerturbation first second
          (diagonalSylvesterInverse (jordan22RootSpectrum first second)
            variation)) := by
      exact (jordan22Diagonal_perturbation_commute first second
        (diagonalSylvesterInverse (jordan22RootSpectrum first second)
          variation)).symm

theorem jordan22SylvesterCorrection_cube
    (first second : PositiveEigenvalue) (variation : Matrix4) :
    jordan22SylvesterCorrection first second
        (jordan22SylvesterCorrection first second
          (jordan22SylvesterCorrection first second variation)) = 0 := by
  let inverseDiagonal : Module.End Real Matrix4 :=
    (diagonalSylvesterInverse
      (jordan22RootSpectrum first second)).toLinearMap
  let perturbation : Module.End Real Matrix4 :=
    (jordan22SylvesterPerturbation first second).toLinearMap
  have hCommute : inverseDiagonal * perturbation =
      perturbation * inverseDiagonal := by
    apply LinearMap.ext
    intro rhs
    exact jordan22DiagonalInverse_perturbation_commute first second rhs
  have hPerturbationCube : perturbation * perturbation * perturbation = 0 := by
    apply LinearMap.ext
    intro rhs
    exact jordan22SylvesterPerturbation_cube first second rhs
  have hSquareProduct :
      (inverseDiagonal * perturbation) *
          (inverseDiagonal * perturbation) =
        (inverseDiagonal * inverseDiagonal) *
          (perturbation * perturbation) := by
    calc
      (inverseDiagonal * perturbation) *
          (inverseDiagonal * perturbation) =
        inverseDiagonal * (perturbation * inverseDiagonal) *
          perturbation := by simp only [mul_assoc]
      _ = inverseDiagonal * (inverseDiagonal * perturbation) *
          perturbation := by rw [← hCommute]
      _ = (inverseDiagonal * inverseDiagonal) *
          (perturbation * perturbation) := by simp only [mul_assoc]
  have hCommuteSquare :
      (perturbation * perturbation) * inverseDiagonal =
        inverseDiagonal * (perturbation * perturbation) := by
    calc
      (perturbation * perturbation) * inverseDiagonal =
        perturbation * (perturbation * inverseDiagonal) := by
          simp only [mul_assoc]
      _ = perturbation * (inverseDiagonal * perturbation) := by
        rw [← hCommute]
      _ = (perturbation * inverseDiagonal) * perturbation := by
        simp only [mul_assoc]
      _ = (inverseDiagonal * perturbation) * perturbation := by
        rw [← hCommute]
      _ = inverseDiagonal * (perturbation * perturbation) := by
        simp only [mul_assoc]
  have hReorder :
      (inverseDiagonal * perturbation) *
          (inverseDiagonal * perturbation) *
        (inverseDiagonal * perturbation) =
      (inverseDiagonal * inverseDiagonal * inverseDiagonal) *
        (perturbation * perturbation * perturbation) := by
    rw [hSquareProduct]
    calc
      (inverseDiagonal * inverseDiagonal) *
          (perturbation * perturbation) *
        (inverseDiagonal * perturbation) =
        (inverseDiagonal * inverseDiagonal) *
          ((perturbation * perturbation) * inverseDiagonal) *
          perturbation := by simp only [mul_assoc]
      _ = (inverseDiagonal * inverseDiagonal) *
          (inverseDiagonal * (perturbation * perturbation)) *
          perturbation := by rw [hCommuteSquare]
      _ = (inverseDiagonal * inverseDiagonal * inverseDiagonal) *
          (perturbation * perturbation * perturbation) := by
        simp only [mul_assoc]
  have hProduct :
      (inverseDiagonal * perturbation) *
          (inverseDiagonal * perturbation) *
        (inverseDiagonal * perturbation) = 0 := by
    rw [hReorder, hPerturbationCube, mul_zero]
  change ((inverseDiagonal * perturbation) *
      (inverseDiagonal * perturbation) *
      (inverseDiagonal * perturbation)) variation = 0
  rw [hProduct]
  rfl

/-- Finite Neumann inverse of the canonical `2 + 2` Sylvester operator. -/
def canonicalJordan22SylvesterInverse
    (first second : PositiveEigenvalue) : Matrix4 →L[Real] Matrix4 :=
  let correction := jordan22SylvesterCorrection first second
  ((ContinuousLinearMap.id Real Matrix4 - correction) +
      correction.comp correction).comp
    (diagonalSylvesterInverse (jordan22RootSpectrum first second))

theorem canonicalJordan22Sylvester_decompose
    (first second : PositiveEigenvalue) (variation : Matrix4) :
    sylvesterOperator (canonicalJordan22Root first second) variation =
      sylvesterOperator (jordan22DiagonalRoot first second) variation +
        jordan22SylvesterPerturbation first second variation := by
  unfold canonicalJordan22Root jordan22SylvesterPerturbation
  simp only [sylvesterOperator_apply]
  noncomm_ring

theorem canonicalJordan22SylvesterInverse_left
    (first second : PositiveEigenvalue) (variation : Matrix4) :
    canonicalJordan22SylvesterInverse first second
        (sylvesterOperator (canonicalJordan22Root first second) variation) =
      variation := by
  have hBase :
      diagonalSylvesterInverse (jordan22RootSpectrum first second)
          (sylvesterOperator (canonicalJordan22Root first second) variation) =
        variation + jordan22SylvesterCorrection first second variation := by
    rw [canonicalJordan22Sylvester_decompose, map_add]
    change diagonalSylvesterInverse (jordan22RootSpectrum first second)
          (sylvesterOperator
            (Matrix.diagonal (jordan22RootSpectrum first second).1)
            variation) +
        diagonalSylvesterInverse (jordan22RootSpectrum first second)
          (jordan22SylvesterPerturbation first second variation) =
      variation + jordan22SylvesterCorrection first second variation
    rw [diagonalSylvesterInverse_left]
    rfl
  unfold canonicalJordan22SylvesterInverse
  simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply,
    ContinuousLinearMap.id_apply]
  rw [hBase]
  simp only [map_add]
  rw [jordan22SylvesterCorrection_cube]
  module

theorem canonicalJordan22Sylvester_injective
    (first second : PositiveEigenvalue) :
    Function.Injective
      (sylvesterOperator (canonicalJordan22Root first second)) :=
  Function.LeftInverse.injective
    (canonicalJordan22SylvesterInverse_left first second)

theorem canonicalJordan22Sylvester_surjective
    (first second : PositiveEigenvalue) :
    Function.Surjective
      (sylvesterOperator (canonicalJordan22Root first second)) := by
  have hInjective : Function.Injective
      (sylvesterOperator (canonicalJordan22Root first second)).toLinearMap :=
    canonicalJordan22Sylvester_injective first second
  exact LinearMap.injective_iff_surjective.mp hInjective

theorem canonicalJordan22SylvesterInverse_right
    (first second : PositiveEigenvalue) (rhs : Matrix4) :
    sylvesterOperator (canonicalJordan22Root first second)
        (canonicalJordan22SylvesterInverse first second rhs) = rhs := by
  obtain ⟨variation, hVariation⟩ :=
    canonicalJordan22Sylvester_surjective first second rhs
  rw [← hVariation, canonicalJordan22SylvesterInverse_left]

def jordan22SylvesterInverse
    (data : Jordan22Data) (rhs : Matrix4) : Matrix4 :=
  jordan22Change data *
    canonicalJordan22SylvesterInverse
      (firstEigenvalue data) (secondEigenvalue data)
      (jordan22Inverse data * rhs * jordan22Change data) *
    jordan22Inverse data

theorem jordan22Sylvester_inverse_apply
    (data : Jordan22Data) (rhs : Matrix4) :
    sylvesterOperator (jordan22Root data)
        (jordan22SylvesterInverse data rhs) = rhs := by
  let canonicalVariation :=
    canonicalJordan22SylvesterInverse
      (firstEigenvalue data) (secondEigenvalue data)
      (jordan22Inverse data * rhs * jordan22Change data)
  have hCanonical :
      sylvesterOperator
          (canonicalJordan22Root (firstEigenvalue data)
            (secondEigenvalue data)) canonicalVariation =
        jordan22Inverse data * rhs * jordan22Change data :=
    canonicalJordan22SylvesterInverse_right
      (firstEigenvalue data) (secondEigenvalue data)
      (jordan22Inverse data * rhs * jordan22Change data)
  have hInverseChange := jordan22Inverse_change data
  have hChangeInverse := jordan22Change_inverse data
  unfold jordan22Root jordan22SylvesterInverse
  change sylvesterOperator
      (jordan22Change data *
          canonicalJordan22Root (firstEigenvalue data) (secondEigenvalue data) *
        jordan22Inverse data)
      (jordan22Change data * canonicalVariation * jordan22Inverse data) = rhs
  simp only [sylvesterOperator_apply] at hCanonical ⊢
  have hFirstProduct :
      (jordan22Change data *
            canonicalJordan22Root (firstEigenvalue data)
              (secondEigenvalue data) * jordan22Inverse data) *
          (jordan22Change data * canonicalVariation * jordan22Inverse data) =
        jordan22Change data *
          (canonicalJordan22Root (firstEigenvalue data)
            (secondEigenvalue data) * canonicalVariation) *
          jordan22Inverse data := by
    calc
      (jordan22Change data *
            canonicalJordan22Root (firstEigenvalue data)
              (secondEigenvalue data) * jordan22Inverse data) *
          (jordan22Change data * canonicalVariation * jordan22Inverse data) =
        jordan22Change data *
          canonicalJordan22Root (firstEigenvalue data)
            (secondEigenvalue data) *
          (jordan22Inverse data * jordan22Change data) * canonicalVariation *
          jordan22Inverse data := by noncomm_ring
      _ = jordan22Change data *
          (canonicalJordan22Root (firstEigenvalue data)
            (secondEigenvalue data) * canonicalVariation) *
          jordan22Inverse data := by
        rw [hInverseChange]
        simp [mul_assoc]
  have hSecondProduct :
      (jordan22Change data * canonicalVariation * jordan22Inverse data) *
          (jordan22Change data *
            canonicalJordan22Root (firstEigenvalue data)
              (secondEigenvalue data) * jordan22Inverse data) =
        jordan22Change data *
          (canonicalVariation * canonicalJordan22Root (firstEigenvalue data)
            (secondEigenvalue data)) * jordan22Inverse data := by
    calc
      (jordan22Change data * canonicalVariation * jordan22Inverse data) *
          (jordan22Change data *
            canonicalJordan22Root (firstEigenvalue data)
              (secondEigenvalue data) * jordan22Inverse data) =
        jordan22Change data * canonicalVariation *
          (jordan22Inverse data * jordan22Change data) *
          canonicalJordan22Root (firstEigenvalue data)
            (secondEigenvalue data) * jordan22Inverse data := by noncomm_ring
      _ = jordan22Change data *
          (canonicalVariation * canonicalJordan22Root (firstEigenvalue data)
            (secondEigenvalue data)) * jordan22Inverse data := by
        rw [hInverseChange]
        simp [mul_assoc]
  calc
    (jordan22Change data *
            canonicalJordan22Root (firstEigenvalue data)
              (secondEigenvalue data) *
          jordan22Inverse data) *
          (jordan22Change data * canonicalVariation * jordan22Inverse data) +
        (jordan22Change data * canonicalVariation * jordan22Inverse data) *
          (jordan22Change data *
              canonicalJordan22Root (firstEigenvalue data)
                (secondEigenvalue data) *
            jordan22Inverse data) =
      jordan22Change data *
        (canonicalJordan22Root (firstEigenvalue data)
              (secondEigenvalue data) * canonicalVariation +
          canonicalVariation * canonicalJordan22Root (firstEigenvalue data)
            (secondEigenvalue data)) * jordan22Inverse data := by
      rw [hFirstProduct, hSecondProduct]
      noncomm_ring
    _ = jordan22Change data *
        (jordan22Inverse data * rhs * jordan22Change data) *
          jordan22Inverse data := by rw [hCanonical]
    _ = rhs := by
      calc
        jordan22Change data *
            (jordan22Inverse data * rhs * jordan22Change data) *
          jordan22Inverse data =
          (jordan22Change data * jordan22Inverse data) * rhs *
            (jordan22Change data * jordan22Inverse data) := by noncomm_ring
        _ = rhs := by rw [hChangeInverse]; simp

theorem jordan22Sylvester_surjective (data : Jordan22Data) :
    Function.Surjective (sylvesterOperator (jordan22Root data)) := by
  intro rhs
  exact ⟨jordan22SylvesterInverse data rhs,
    jordan22Sylvester_inverse_apply data rhs⟩

theorem jordan22Sylvester_injective (data : Jordan22Data) :
    Function.Injective (sylvesterOperator (jordan22Root data)) := by
  have hSurjective : Function.Surjective
      (sylvesterOperator (jordan22Root data)).toLinearMap :=
    jordan22Sylvester_surjective data
  exact LinearMap.injective_iff_surjective.mpr hSurjective

theorem jordan22Sylvester_bijective (data : Jordan22Data) :
    Function.Bijective (sylvesterOperator (jordan22Root data)) :=
  ⟨jordan22Sylvester_injective data, jordan22Sylvester_surjective data⟩

/-- Honest residual after closing the positive real `2 + 2` partition. -/
def residualPositiveJordanPartition4 (blocks : List Nat) : Prop :=
  blocks.sum = 4 ∧ (∀ size ∈ blocks, 0 < size) ∧ blocks ≠ [2, 2]

theorem residualPositiveJordanPartition4_iff (blocks : List Nat) :
    residualPositiveJordanPartition4 blocks ↔
      blocks.sum = 4 ∧ (∀ size ∈ blocks, 0 < size) ∧ blocks ≠ [2, 2] :=
  Iff.rfl

end

end P0EFTJanusPositiveJordanTwoPlusTwoRoot4D
end JanusFormal
