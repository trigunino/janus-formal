import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawPolynomialRootReduction4D

/-!
# A raw two-eigenvalue Hermite cubic root

This gate closes the raw relation
`(A - lambda I)^2 (A - mu I)^2 = 0` for distinct positive real scalars.
The root is the explicit cubic Hermite interpolant of `sqrt`, so no Jordan
presentation is required.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawDoubleDoubleHermiteRoot4D

set_option autoImplicit false

noncomputable section

open scoped MatrixOrder
open Polynomial
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveRawQuadraticRootReduction4D
open P0EFTJanusPositiveRawPolynomialRootReduction4D
open P0EFTJanusRawSpectralBridgeReduction4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRealSquareRootSpectralObstructions4D
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
open P0EFTJanusPositiveJordanTwoPlusTwoRoot4D

abbrev Matrix4 := P0EFTJanusPositiveRawPolynomialRootReduction4D.Matrix4

def hermiteCubicValueCorrection (first second : Real) : Real :=
  Real.sqrt second - Real.sqrt first -
    (second - first) / (2 * Real.sqrt first)

def hermiteCubicSlopeCorrection (first second : Real) : Real :=
  1 / (2 * Real.sqrt second) - 1 / (2 * Real.sqrt first)

def hermiteCubicSecondCoefficient (first second : Real) : Real :=
  let displacement := second - first
  (3 * hermiteCubicValueCorrection first second -
      hermiteCubicSlopeCorrection first second * displacement) /
    displacement ^ 2

def hermiteCubicThirdCoefficient (first second : Real) : Real :=
  let displacement := second - first
  (hermiteCubicSlopeCorrection first second * displacement -
      2 * hermiteCubicValueCorrection first second) /
    displacement ^ 3

/-- The cubic matching both values and both first derivatives of `sqrt` at
the two supplied positive nodes. -/
def positiveDoubleDoubleHermitePolynomial
    (first second : Real) : Polynomial Real :=
  let centered := X - C first
  C (Real.sqrt first) +
    C (1 / (2 * Real.sqrt first)) * centered +
    C (hermiteCubicSecondCoefficient first second) * centered ^ 2 +
    C (hermiteCubicThirdCoefficient first second) * centered ^ 3

theorem positiveDoubleDoubleHermitePolynomial_natDegree_le_three
    (first second : Real) :
    (positiveDoubleDoubleHermitePolynomial first second).natDegree ≤ 3 := by
  unfold positiveDoubleDoubleHermitePolynomial
  have hConstant : (C (Real.sqrt first) : Polynomial Real).natDegree ≤ 3 := by
    simp
  have hLinear :
      (C (1 / (2 * Real.sqrt first)) * (X - C first)).natDegree ≤ 3 :=
    (natDegree_C_mul_le _ _).trans
      ((natDegree_X_sub_C_le first).trans (by norm_num))
  have hQuadratic :
      (C (hermiteCubicSecondCoefficient first second) *
        (X - C first) ^ 2).natDegree ≤ 3 :=
    (natDegree_C_mul_le _ _).trans
      ((natDegree_pow_le_of_le 2 (natDegree_X_sub_C_le first)).trans
        (by norm_num))
  have hCubic :
      (C (hermiteCubicThirdCoefficient first second) *
        (X - C first) ^ 3).natDegree ≤ 3 :=
    (natDegree_C_mul_le _ _).trans
      ((natDegree_pow_le_of_le 3 (natDegree_X_sub_C_le first)).trans
        (by norm_num))
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le hConstant hLinear) hQuadratic) hCubic

theorem positiveDoubleDoubleHermitePolynomial_eval_first
    (first second : Real) :
    (positiveDoubleDoubleHermitePolynomial first second).eval first =
      Real.sqrt first := by
  simp [positiveDoubleDoubleHermitePolynomial]

theorem positiveDoubleDoubleHermitePolynomial_derivative_eval_first
    (first second : Real) :
    (positiveDoubleDoubleHermitePolynomial first second).derivative.eval first =
      1 / (2 * Real.sqrt first) := by
  simp [positiveDoubleDoubleHermitePolynomial, derivative_pow]

theorem positiveDoubleDoubleHermitePolynomial_eval_second
    {first second : Real} (hFirst : 0 < first)
    (hDistinct : first ≠ second) :
    (positiveDoubleDoubleHermitePolynomial first second).eval second =
      Real.sqrt second := by
  have hDisplacement : second - first ≠ 0 := sub_ne_zero.mpr hDistinct.symm
  have hSqrtFirst : Real.sqrt first ≠ 0 := (Real.sqrt_pos.2 hFirst).ne'
  simp [positiveDoubleDoubleHermitePolynomial,
    hermiteCubicSecondCoefficient, hermiteCubicThirdCoefficient,
    hermiteCubicValueCorrection, hermiteCubicSlopeCorrection]
  field_simp [hDisplacement, hSqrtFirst]
  ring

theorem positiveDoubleDoubleHermitePolynomial_derivative_eval_second
    {first second : Real} (hFirst : 0 < first) (hSecond : 0 < second)
    (hDistinct : first ≠ second) :
    (positiveDoubleDoubleHermitePolynomial first second).derivative.eval second =
      1 / (2 * Real.sqrt second) := by
  have hDisplacement : second - first ≠ 0 := sub_ne_zero.mpr hDistinct.symm
  have hSqrtFirst : Real.sqrt first ≠ 0 := (Real.sqrt_pos.2 hFirst).ne'
  have hSqrtSecond : Real.sqrt second ≠ 0 := (Real.sqrt_pos.2 hSecond).ne'
  simp [positiveDoubleDoubleHermitePolynomial,
    hermiteCubicSecondCoefficient, hermiteCubicThirdCoefficient,
    hermiteCubicValueCorrection, hermiteCubicSlopeCorrection,
    derivative_pow]
  field_simp [hDisplacement, hSqrtFirst, hSqrtSecond]
  ring

private theorem X_sub_C_sq_dvd_of_eval_derivative_eq_zero
    {node : Real} {polynomial : Polynomial Real}
    (hEval : polynomial.eval node = 0)
    (hDerivative : polynomial.derivative.eval node = 0) :
    (X - C node) ^ 2 ∣ polynomial := by
  have hLinear : X - C node ∣ polynomial :=
    (dvd_iff_isRoot).2 hEval
  obtain ⟨quotient, hPolynomial⟩ := hLinear
  have hQuotientEval : quotient.eval node = 0 := by
    rw [hPolynomial] at hDerivative
    simpa [derivative_mul] using hDerivative
  obtain ⟨secondQuotient, hQuotient⟩ :=
    (dvd_iff_isRoot).2 hQuotientEval
  refine ⟨secondQuotient, ?_⟩
  rw [hPolynomial, hQuotient]
  ring

def positiveDoubleDoubleSquareResidual
    (first second : Real) : Polynomial Real :=
  positiveDoubleDoubleHermitePolynomial first second *
      positiveDoubleDoubleHermitePolynomial first second - X

theorem positiveDoubleDoubleSquareResidual_eval_first
    {first second : Real} (hFirst : 0 < first) :
    (positiveDoubleDoubleSquareResidual first second).eval first = 0 := by
  rw [positiveDoubleDoubleSquareResidual, eval_sub, eval_mul,
    positiveDoubleDoubleHermitePolynomial_eval_first, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hFirst.le)

theorem positiveDoubleDoubleSquareResidual_derivative_eval_first
    {first second : Real} (hFirst : 0 < first) :
    (positiveDoubleDoubleSquareResidual first second).derivative.eval first = 0 := by
  have hSqrt : Real.sqrt first ≠ 0 := (Real.sqrt_pos.2 hFirst).ne'
  simp [positiveDoubleDoubleSquareResidual,
    positiveDoubleDoubleHermitePolynomial_eval_first,
    positiveDoubleDoubleHermitePolynomial_derivative_eval_first,
    hSqrt]
  field_simp [hSqrt]
  ring

theorem positiveDoubleDoubleSquareResidual_eval_second
    {first second : Real} (hFirst : 0 < first) (hSecond : 0 < second)
    (hDistinct : first ≠ second) :
    (positiveDoubleDoubleSquareResidual first second).eval second = 0 := by
  rw [positiveDoubleDoubleSquareResidual, eval_sub, eval_mul,
    positiveDoubleDoubleHermitePolynomial_eval_second hFirst hDistinct, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hSecond.le)

theorem positiveDoubleDoubleSquareResidual_derivative_eval_second
    {first second : Real} (hFirst : 0 < first) (hSecond : 0 < second)
    (hDistinct : first ≠ second) :
    (positiveDoubleDoubleSquareResidual first second).derivative.eval second = 0 := by
  have hSqrt : Real.sqrt second ≠ 0 := (Real.sqrt_pos.2 hSecond).ne'
  simp [positiveDoubleDoubleSquareResidual,
    positiveDoubleDoubleHermitePolynomial_eval_second hFirst hDistinct,
    positiveDoubleDoubleHermitePolynomial_derivative_eval_second
      hFirst hSecond hDistinct,
    hSqrt]
  field_simp [hSqrt]
  ring

theorem positiveDoubleDoubleAnnihilator_dvd_squareResidual
    {first second : Real} (hFirst : 0 < first) (hSecond : 0 < second)
    (hDistinct : first ≠ second) :
    (X - C first) ^ 2 * (X - C second) ^ 2 ∣
      positiveDoubleDoubleSquareResidual first second := by
  have hFirstDvd : (X - C first) ^ 2 ∣
      positiveDoubleDoubleSquareResidual first second :=
    X_sub_C_sq_dvd_of_eval_derivative_eq_zero
      (positiveDoubleDoubleSquareResidual_eval_first hFirst)
      (positiveDoubleDoubleSquareResidual_derivative_eval_first hFirst)
  have hSecondDvd : (X - C second) ^ 2 ∣
      positiveDoubleDoubleSquareResidual first second :=
    X_sub_C_sq_dvd_of_eval_derivative_eq_zero
      (positiveDoubleDoubleSquareResidual_eval_second hFirst hSecond hDistinct)
      (positiveDoubleDoubleSquareResidual_derivative_eval_second
        hFirst hSecond hDistinct)
  have hCoprime : IsCoprime ((X - C first) ^ 2) ((X - C second) ^ 2) :=
    (isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hDistinct).isUnit).pow
  exact hCoprime.mul_dvd hFirstDvd hSecondDvd

/-- A raw two-node Hermite annihilator, without any supplied eigenbasis. -/
def HasPositiveDistinctDoubleDoubleRelation4 (target : Matrix4) : Prop :=
  ∃ first second : Real, 0 < first ∧ 0 < second ∧ first ≠ second ∧
    let firstDisplacement := target - first • (1 : Matrix4)
    let secondDisplacement := target - second • (1 : Matrix4)
    firstDisplacement * firstDisplacement *
        secondDisplacement * secondDisplacement = 0

theorem canonicalJordan22Target_hasPositiveDistinctDoubleDoubleRelation
    (first second : PositiveEigenvalue) (hDistinct : first.1 ≠ second.1) :
    HasPositiveDistinctDoubleDoubleRelation4
      (canonicalJordan22Target first second) := by
  refine ⟨first.1, second.1, first.2, second.2, hDistinct, ?_⟩
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalJordan22Target, jordan22DiagonalTarget,
      jordan22TargetSpectrum, jordan22TargetNilpotent,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem canonicalJordan22Target_not_isHermitian
    (first second : PositiveEigenvalue) :
    ¬ (canonicalJordan22Target first second).IsHermitian := by
  intro hHermitian
  have hEntry := hHermitian.apply (0 : Fin 4) (1 : Fin 4)
  simp [canonicalJordan22Target, jordan22DiagonalTarget,
    jordan22TargetSpectrum, jordan22TargetNilpotent] at hEntry

theorem canonicalJordan22Target_not_posSemidef
    (first second : PositiveEigenvalue) :
    ¬ (canonicalJordan22Target first second).PosSemidef := by
  intro hPosSemidef
  exact canonicalJordan22Target_not_isHermitian first second
    hPosSemidef.isHermitian

theorem canonicalJordan22Target_not_positiveRealQuadraticRelation
    (first second : PositiveEigenvalue) (hDistinct : first.1 ≠ second.1) :
    ¬ HasPositiveRealQuadraticRelation4
      (canonicalJordan22Target first second) := by
  rintro ⟨left, right, _hLeft, _hRight, hRelation⟩
  have h00 := congrArg
    (fun matrix : Matrix4 => matrix (0 : Fin 4) (0 : Fin 4)) hRelation
  have h01 := congrArg
    (fun matrix : Matrix4 => matrix (0 : Fin 4) (1 : Fin 4)) hRelation
  have h22 := congrArg
    (fun matrix : Matrix4 => matrix (2 : Fin 4) (2 : Fin 4)) hRelation
  have h23 := congrArg
    (fun matrix : Matrix4 => matrix (2 : Fin 4) (3 : Fin 4)) hRelation
  simp [canonicalJordan22Target, jordan22DiagonalTarget,
    jordan22TargetSpectrum, jordan22TargetNilpotent,
    Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four] at h00 h01 h22 h23
  rcases h00 with hFirstLeft | hFirstRight <;>
    rcases h22 with hSecondLeft | hSecondRight
  all_goals
    apply hDistinct
    linarith

theorem canonicalJordan22Target_not_positiveSingleEigenvalueQuarticRelation
    (first second : PositiveEigenvalue) (hDistinct : first.1 ≠ second.1) :
    ¬ HasPositiveSingleEigenvalueQuarticRelation4
      (canonicalJordan22Target first second) := by
  rintro ⟨eigenvalue, hFourth⟩
  have h00 := congrArg
    (fun matrix : Matrix4 => matrix (0 : Fin 4) (0 : Fin 4)) hFourth
  have h22 := congrArg
    (fun matrix : Matrix4 => matrix (2 : Fin 4) (2 : Fin 4)) hFourth
  simp [scaledJordanDisplacementFourth, canonicalJordan22Target,
    jordan22DiagonalTarget, jordan22TargetSpectrum, jordan22TargetNilpotent,
    Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four] at h00 h22
  apply hDistinct
  nlinarith [sq_nonneg (first.1 - eigenvalue.1),
    sq_nonneg (second.1 - eigenvalue.1)]

def positiveDoubleDoubleHermiteRoot4
    (target : Matrix4) (first second : Real) : Matrix4 :=
  Polynomial.aeval target
    (positiveDoubleDoubleHermitePolynomial first second)

theorem positiveDoubleDoubleHermitePolynomial_minpoly_congruence
    {target : Matrix4} {first second : Real}
    (hFirst : 0 < first) (hSecond : 0 < second)
    (hDistinct : first ≠ second)
    (hRelation :
      let firstDisplacement := target - first • (1 : Matrix4)
      let secondDisplacement := target - second • (1 : Matrix4)
      firstDisplacement * firstDisplacement *
          secondDisplacement * secondDisplacement = 0) :
    minpoly Real target ∣
      positiveDoubleDoubleSquareResidual first second := by
  have hAnnihilator :
      Polynomial.aeval target
        ((X - C first) ^ 2 * (X - C second) ^ 2) = 0 := by
    simpa [pow_two, Algebra.smul_def, mul_assoc] using hRelation
  have hMinpolyAnnihilator : minpoly Real target ∣
      (X - C first) ^ 2 * (X - C second) ^ 2 :=
    minpoly.dvd Real target hAnnihilator
  exact hMinpolyAnnihilator.trans
    (positiveDoubleDoubleAnnihilator_dvd_squareResidual
      hFirst hSecond hDistinct)

theorem positiveDoubleDoubleHermiteRoot4_square
    {target : Matrix4} {first second : Real}
    (hFirst : 0 < first) (hSecond : 0 < second)
    (hDistinct : first ≠ second)
    (hRelation :
      let firstDisplacement := target - first • (1 : Matrix4)
      let secondDisplacement := target - second • (1 : Matrix4)
      firstDisplacement * firstDisplacement *
          secondDisplacement * secondDisplacement = 0) :
    positiveDoubleDoubleHermiteRoot4 target first second *
        positiveDoubleDoubleHermiteRoot4 target first second = target := by
  exact cubicMinpolyRoot4_square
    (positiveDoubleDoubleHermitePolynomial_minpoly_congruence
      hFirst hSecond hDistinct hRelation)

theorem positiveDistinctDoubleDoubleRelation_hasCubicMinpolyRoot
    {target : Matrix4}
    (hTarget : HasPositiveDistinctDoubleDoubleRelation4 target) :
    HasCubicPolynomialSquareRootModuloMinpoly4 target := by
  obtain ⟨first, second, hFirst, hSecond, hDistinct, hRelation⟩ := hTarget
  exact ⟨positiveDoubleDoubleHermitePolynomial first second,
    positiveDoubleDoubleHermitePolynomial_natDegree_le_three first second,
    positiveDoubleDoubleHermitePolynomial_minpoly_congruence
      hFirst hSecond hDistinct hRelation⟩

theorem positiveDistinctDoubleDoubleRelation_hasRealSquareRoot
    {target : Matrix4}
    (hTarget : HasPositiveDistinctDoubleDoubleRelation4 target) :
    HasRealSquareRoot target := by
  obtain ⟨first, second, hFirst, hSecond, hDistinct, hRelation⟩ := hTarget
  exact ⟨positiveDoubleDoubleHermiteRoot4 target first second,
    positiveDoubleDoubleHermiteRoot4_square hFirst hSecond hDistinct hRelation⟩

/-- Exact residual after adjoining the distinct positive double-double Hermite
locus to all previously closed positive raw loci. -/
def PositiveOutsideKnownLociAndDoubleDoubleRootResidual4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    ¬ target.PosSemidef → ¬ HasPositiveRealQuadraticRelation4 target →
      ¬ HasPositiveSingleEigenvalueQuarticRelation4 target →
        ¬ HasPositiveDistinctDoubleDoubleRelation4 target →
          HasRealSquareRoot target

theorem positiveRawRootClosure_iff_outsideKnownLociAndDoubleDouble :
    PositiveRawRootClosure4 ↔
      PositiveOutsideKnownLociAndDoubleDoubleRootResidual4 := by
  constructor
  · intro closure target hSpectrum _hNotCFC _hNotQuadratic _hNotQuartic
      _hNotDoubleDouble
    exact closure target hSpectrum
  · intro residual target hSpectrum
    by_cases hPosSemidef : target.PosSemidef
    · exact posSemidef_hasRealSquareRoot hPosSemidef
    · by_cases hQuadratic : HasPositiveRealQuadraticRelation4 target
      · exact positiveRealQuadraticRelation_hasRealSquareRoot hQuadratic
      · by_cases hQuartic : HasPositiveSingleEigenvalueQuarticRelation4 target
        · exact positiveSingleEigenvalueQuarticRelation_hasRealSquareRoot hQuartic
        · by_cases hDoubleDouble :
            HasPositiveDistinctDoubleDoubleRelation4 target
          · exact positiveDistinctDoubleDoubleRelation_hasRealSquareRoot
              hDoubleDouble
          · exact residual target hSpectrum hPosSemidef hQuadratic hQuartic
              hDoubleDouble

end

end P0EFTJanusPositiveRawDoubleDoubleHermiteRoot4D
end JanusFormal
