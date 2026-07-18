import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawDoubleDoubleHermiteRoot4D

/-!
# A raw positive `3 + 1` Hermite cubic root

For distinct positive nodes, this gate closes
`(A - lambda I)^3 (A - mu I) = 0`.  The explicit cubic matches the value,
first derivative and second derivative of `sqrt` at `lambda`, and its value at
`mu`.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawTripleSingleHermiteRoot4D

set_option autoImplicit false

noncomputable section

open scoped MatrixOrder
open Polynomial
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
open P0EFTJanusPositiveJordanThreePlusOneRoot4D
open P0EFTJanusPositiveRawQuadraticRootReduction4D
open P0EFTJanusPositiveRawPolynomialRootReduction4D
open P0EFTJanusPositiveRawDoubleDoubleHermiteRoot4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRealSquareRootSpectralObstructions4D
open P0EFTJanusRawSpectralBridgeReduction4D

abbrev Matrix4 := P0EFTJanusPositiveRawDoubleDoubleHermiteRoot4D.Matrix4

def tripleSingleHermiteCubicCorrection (first second : Real) : Real :=
  let displacement := second - first
  (Real.sqrt second - Real.sqrt first -
      displacement / (2 * Real.sqrt first) +
      displacement ^ 2 / (8 * (Real.sqrt first) ^ 3)) /
    displacement ^ 3

/-- Taylor order two at `first`, with the cubic coefficient fixed by the value
at `second`. -/
def positiveTripleSingleHermitePolynomial
    (first second : Real) : Polynomial Real :=
  let centered := X - C first
  C (Real.sqrt first) +
    C (1 / (2 * Real.sqrt first)) * centered -
    C (1 / (8 * (Real.sqrt first) ^ 3)) * centered ^ 2 +
    C (tripleSingleHermiteCubicCorrection first second) * centered ^ 3

theorem positiveTripleSingleHermitePolynomial_natDegree_le_three
    (first second : Real) :
    (positiveTripleSingleHermitePolynomial first second).natDegree ≤ 3 := by
  unfold positiveTripleSingleHermitePolynomial
  have hConstant : (C (Real.sqrt first) : Polynomial Real).natDegree ≤ 3 := by
    simp
  have hLinear :
      (C (1 / (2 * Real.sqrt first)) * (X - C first)).natDegree ≤ 3 :=
    (natDegree_C_mul_le _ _).trans
      ((natDegree_X_sub_C_le first).trans (by norm_num))
  have hQuadratic :
      (C (1 / (8 * Real.sqrt first ^ 3)) *
        (X - C first) ^ 2).natDegree ≤ 3 :=
    (natDegree_C_mul_le _ _).trans
      ((natDegree_pow_le_of_le 2 (natDegree_X_sub_C_le first)).trans
        (by norm_num))
  have hCubic :
      (C (tripleSingleHermiteCubicCorrection first second) *
        (X - C first) ^ 3).natDegree ≤ 3 :=
    (natDegree_C_mul_le _ _).trans
      ((natDegree_pow_le_of_le 3 (natDegree_X_sub_C_le first)).trans
        (by norm_num))
  have hSub :
      ((C (Real.sqrt first) +
          C (1 / (2 * Real.sqrt first)) * (X - C first)) -
        C (1 / (8 * Real.sqrt first ^ 3)) * (X - C first) ^ 2).natDegree ≤ 3 :=
    (natDegree_sub_le _ _).trans
      (max_le (natDegree_add_le_of_degree_le hConstant hLinear) hQuadratic)
  exact natDegree_add_le_of_degree_le
    hSub hCubic

theorem positiveTripleSingleHermitePolynomial_eval_first
    (first second : Real) :
    (positiveTripleSingleHermitePolynomial first second).eval first =
      Real.sqrt first := by
  simp [positiveTripleSingleHermitePolynomial]

theorem positiveTripleSingleHermitePolynomial_derivative_eval_first
    (first second : Real) :
    (positiveTripleSingleHermitePolynomial first second).derivative.eval first =
      1 / (2 * Real.sqrt first) := by
  simp [positiveTripleSingleHermitePolynomial, derivative_pow]

theorem positiveTripleSingleHermitePolynomial_secondDerivative_eval_first
    (first second : Real) :
    (positiveTripleSingleHermitePolynomial first second).derivative.derivative.eval first =
      -1 / (4 * (Real.sqrt first) ^ 3) := by
  simp [positiveTripleSingleHermitePolynomial, derivative_pow]
  ring

theorem positiveTripleSingleHermitePolynomial_eval_second
    {first second : Real} (hFirst : 0 < first)
    (hDistinct : first ≠ second) :
    (positiveTripleSingleHermitePolynomial first second).eval second =
      Real.sqrt second := by
  have hDisplacement : second - first ≠ 0 := sub_ne_zero.mpr hDistinct.symm
  have hSqrtFirst : Real.sqrt first ≠ 0 := (Real.sqrt_pos.2 hFirst).ne'
  simp [positiveTripleSingleHermitePolynomial,
    tripleSingleHermiteCubicCorrection]
  field_simp [hDisplacement, hSqrtFirst]
  ring

def positiveTripleSingleSquareResidual
    (first second : Real) : Polynomial Real :=
  positiveTripleSingleHermitePolynomial first second *
      positiveTripleSingleHermitePolynomial first second - X

theorem positiveTripleSingleSquareResidual_eval_first
    {first second : Real} (hFirst : 0 < first) :
    (positiveTripleSingleSquareResidual first second).eval first = 0 := by
  rw [positiveTripleSingleSquareResidual, eval_sub, eval_mul,
    positiveTripleSingleHermitePolynomial_eval_first, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hFirst.le)

theorem positiveTripleSingleSquareResidual_derivative_eval_first
    {first second : Real} (hFirst : 0 < first) :
    (positiveTripleSingleSquareResidual first second).derivative.eval first = 0 := by
  have hSqrt : Real.sqrt first ≠ 0 := (Real.sqrt_pos.2 hFirst).ne'
  simp [positiveTripleSingleSquareResidual,
    positiveTripleSingleHermitePolynomial_eval_first,
    positiveTripleSingleHermitePolynomial_derivative_eval_first, hSqrt]
  field_simp [hSqrt]
  ring

theorem positiveTripleSingleSquareResidual_secondDerivative_eval_first
    {first second : Real} (hFirst : 0 < first) :
    (positiveTripleSingleSquareResidual first second).derivative.derivative.eval first = 0 := by
  have hSqrt : Real.sqrt first ≠ 0 := (Real.sqrt_pos.2 hFirst).ne'
  simp [positiveTripleSingleSquareResidual,
    positiveTripleSingleHermitePolynomial_eval_first,
    positiveTripleSingleHermitePolynomial_derivative_eval_first,
    positiveTripleSingleHermitePolynomial_secondDerivative_eval_first]
  field_simp [hSqrt]
  ring

theorem positiveTripleSingleSquareResidual_eval_second
    {first second : Real} (hFirst : 0 < first) (hSecond : 0 < second)
    (hDistinct : first ≠ second) :
    (positiveTripleSingleSquareResidual first second).eval second = 0 := by
  rw [positiveTripleSingleSquareResidual, eval_sub, eval_mul,
    positiveTripleSingleHermitePolynomial_eval_second hFirst hDistinct, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hSecond.le)

private theorem X_sub_C_cube_dvd_of_three_jets_zero
    {node : Real} {polynomial : Polynomial Real}
    (hEval : polynomial.eval node = 0)
    (hDerivative : polynomial.derivative.eval node = 0)
    (hSecondDerivative : polynomial.derivative.derivative.eval node = 0) :
    (X - C node) ^ 3 ∣ polynomial := by
  by_cases hZero : polynomial = 0
  · simp [hZero]
  · apply (le_rootMultiplicity_iff hZero).mp
    exact Nat.succ_le_iff.mpr
      (lt_rootMultiplicity_of_isRoot_iterate_derivative hZero (by
        intro order hOrder
        interval_cases order
        · simpa [Polynomial.IsRoot] using hEval
        · simpa [Polynomial.IsRoot, Function.iterate_succ_apply] using
            hDerivative
        · simpa [Polynomial.IsRoot, Function.iterate_succ_apply] using
            hSecondDerivative))

theorem positiveTripleSingleAnnihilator_dvd_squareResidual
    {first second : Real} (hFirst : 0 < first) (hSecond : 0 < second)
    (hDistinct : first ≠ second) :
    (X - C first) ^ 3 * (X - C second) ∣
      positiveTripleSingleSquareResidual first second := by
  have hFirstDvd : (X - C first) ^ 3 ∣
      positiveTripleSingleSquareResidual first second :=
    X_sub_C_cube_dvd_of_three_jets_zero
      (positiveTripleSingleSquareResidual_eval_first hFirst)
      (positiveTripleSingleSquareResidual_derivative_eval_first hFirst)
      (positiveTripleSingleSquareResidual_secondDerivative_eval_first hFirst)
  have hSecondDvd : X - C second ∣
      positiveTripleSingleSquareResidual first second :=
    (dvd_iff_isRoot).2
      (positiveTripleSingleSquareResidual_eval_second
        hFirst hSecond hDistinct)
  have hCoprime : IsCoprime ((X - C first) ^ 3) (X - C second) :=
    (isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hDistinct).isUnit).pow_left
  exact hCoprime.mul_dvd hFirstDvd hSecondDvd

/-- A raw positive `3 + 1` annihilator with distinct scalar nodes. -/
def HasPositiveDistinctTripleSingleRelation4 (target : Matrix4) : Prop :=
  ∃ first second : Real, 0 < first ∧ 0 < second ∧ first ≠ second ∧
    let firstDisplacement := target - first • (1 : Matrix4)
    let secondDisplacement := target - second • (1 : Matrix4)
    firstDisplacement * firstDisplacement * firstDisplacement *
        secondDisplacement = 0

theorem canonicalJordan31Target_hasPositiveDistinctTripleSingleRelation
    (triple singleton : PositiveEigenvalue)
    (hDistinct : triple.1 ≠ singleton.1) :
    HasPositiveDistinctTripleSingleRelation4
      (canonicalJordan31Target triple singleton) := by
  refine ⟨triple.1, singleton.1, triple.2, singleton.2, hDistinct, ?_⟩
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalJordan31Target, jordan31DiagonalTarget,
      jordan31TargetSpectrum, jordan31TargetNilpotent,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem canonicalJordan31Target_not_isHermitian
    (triple singleton : PositiveEigenvalue) :
    ¬ (canonicalJordan31Target triple singleton).IsHermitian := by
  intro hHermitian
  have hEntry := hHermitian.apply (0 : Fin 4) (1 : Fin 4)
  simp [canonicalJordan31Target, jordan31DiagonalTarget,
    jordan31TargetSpectrum, jordan31TargetNilpotent] at hEntry

theorem canonicalJordan31Target_not_posSemidef
    (triple singleton : PositiveEigenvalue) :
    ¬ (canonicalJordan31Target triple singleton).PosSemidef := by
  intro hPosSemidef
  exact canonicalJordan31Target_not_isHermitian triple singleton
    hPosSemidef.isHermitian

theorem canonicalJordan31Target_not_positiveRealQuadraticRelation
    (triple singleton : PositiveEigenvalue) :
    ¬ HasPositiveRealQuadraticRelation4
      (canonicalJordan31Target triple singleton) := by
  rintro ⟨left, right, _hLeft, _hRight, hRelation⟩
  have h02 := congrArg
    (fun matrix : Matrix4 => matrix (0 : Fin 4) (2 : Fin 4)) hRelation
  have hFirstRow : (![(0 : Real), 1, 0, 0] : Fin 4 → Real) 2 = 0 := by rfl
  have hSecondRow : (![(0 : Real), 0, 1, 0] : Fin 4 → Real) 2 = 1 := by rfl
  have hThirdRow : (![(0 : Real), 0, 0, 0] : Fin 4 → Real) 2 = 0 := by rfl
  have hFourthRow : (![(0 : Real), 0, 0, 0] : Fin 4 → Real) 2 = 0 := by rfl
  have h02Fin : (0 : Fin 4) ≠ 2 := by decide
  have h12Fin : (1 : Fin 4) ≠ 2 := by decide
  have h0s2Fin : (0 : Fin 4) ≠ Fin.succ (2 : Fin 3) := by decide
  have hs22Fin : Fin.succ (2 : Fin 3) ≠ (2 : Fin 4) := by decide
  norm_num [canonicalJordan31Target, jordan31DiagonalTarget,
    jordan31TargetSpectrum, jordan31TargetNilpotent,
    Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
    hFirstRow, hSecondRow, hThirdRow, hFourthRow,
    h02Fin, h12Fin, h0s2Fin, hs22Fin] at h02

theorem canonicalJordan31Target_not_positiveSingleEigenvalueQuarticRelation
    (triple singleton : PositiveEigenvalue)
    (hDistinct : triple.1 ≠ singleton.1) :
    ¬ HasPositiveSingleEigenvalueQuarticRelation4
      (canonicalJordan31Target triple singleton) := by
  rintro ⟨eigenvalue, hFourth⟩
  have h00 := congrArg
    (fun matrix : Matrix4 => matrix (0 : Fin 4) (0 : Fin 4)) hFourth
  have h33 := congrArg
    (fun matrix : Matrix4 => matrix (3 : Fin 4) (3 : Fin 4)) hFourth
  simp [scaledJordanDisplacementFourth, canonicalJordan31Target,
    jordan31DiagonalTarget, jordan31TargetSpectrum, jordan31TargetNilpotent,
    Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four] at h00 h33
  apply hDistinct
  nlinarith [sq_nonneg (triple.1 - eigenvalue.1),
    sq_nonneg (singleton.1 - eigenvalue.1)]

theorem canonicalJordan31Target_not_positiveDistinctDoubleDoubleRelation
    (triple singleton : PositiveEigenvalue)
    (hDistinct : triple.1 ≠ singleton.1) :
    ¬ HasPositiveDistinctDoubleDoubleRelation4
      (canonicalJordan31Target triple singleton) := by
  rintro ⟨left, right, _hLeft, _hRight, _hNodesDistinct, hRelation⟩
  have h00 := congrArg
    (fun matrix : Matrix4 => matrix (0 : Fin 4) (0 : Fin 4)) hRelation
  have h33 := congrArg
    (fun matrix : Matrix4 => matrix (3 : Fin 4) (3 : Fin 4)) hRelation
  have h02 := congrArg
    (fun matrix : Matrix4 => matrix (0 : Fin 4) (2 : Fin 4)) hRelation
  simp [canonicalJordan31Target, jordan31DiagonalTarget,
    jordan31TargetSpectrum, jordan31TargetNilpotent,
    Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four] at h00 h33 h02
  rcases h00 with hTripleLeft | hTripleRight <;>
    rcases h33 with hSingletonLeft | hSingletonRight
  all_goals
    apply hDistinct
    nlinarith [sq_nonneg (left - right)]

def positiveTripleSingleHermiteRoot4
    (target : Matrix4) (first second : Real) : Matrix4 :=
  Polynomial.aeval target
    (positiveTripleSingleHermitePolynomial first second)

theorem positiveTripleSingleHermitePolynomial_minpoly_congruence
    {target : Matrix4} {first second : Real}
    (hFirst : 0 < first) (hSecond : 0 < second)
    (hDistinct : first ≠ second)
    (hRelation :
      let firstDisplacement := target - first • (1 : Matrix4)
      let secondDisplacement := target - second • (1 : Matrix4)
      firstDisplacement * firstDisplacement * firstDisplacement *
          secondDisplacement = 0) :
    minpoly Real target ∣
      positiveTripleSingleSquareResidual first second := by
  have hAnnihilator :
      Polynomial.aeval target
        ((X - C first) ^ 3 * (X - C second)) = 0 := by
    simpa [pow_succ, pow_two, Algebra.smul_def, mul_assoc] using hRelation
  have hMinpolyAnnihilator : minpoly Real target ∣
      (X - C first) ^ 3 * (X - C second) :=
    minpoly.dvd Real target hAnnihilator
  exact hMinpolyAnnihilator.trans
    (positiveTripleSingleAnnihilator_dvd_squareResidual
      hFirst hSecond hDistinct)

theorem positiveTripleSingleHermiteRoot4_square
    {target : Matrix4} {first second : Real}
    (hFirst : 0 < first) (hSecond : 0 < second)
    (hDistinct : first ≠ second)
    (hRelation :
      let firstDisplacement := target - first • (1 : Matrix4)
      let secondDisplacement := target - second • (1 : Matrix4)
      firstDisplacement * firstDisplacement * firstDisplacement *
          secondDisplacement = 0) :
    positiveTripleSingleHermiteRoot4 target first second *
        positiveTripleSingleHermiteRoot4 target first second = target := by
  exact cubicMinpolyRoot4_square
    (positiveTripleSingleHermitePolynomial_minpoly_congruence
      hFirst hSecond hDistinct hRelation)

theorem positiveDistinctTripleSingleRelation_hasCubicMinpolyRoot
    {target : Matrix4}
    (hTarget : HasPositiveDistinctTripleSingleRelation4 target) :
    HasCubicPolynomialSquareRootModuloMinpoly4 target := by
  obtain ⟨first, second, hFirst, hSecond, hDistinct, hRelation⟩ := hTarget
  exact ⟨positiveTripleSingleHermitePolynomial first second,
    positiveTripleSingleHermitePolynomial_natDegree_le_three first second,
    positiveTripleSingleHermitePolynomial_minpoly_congruence
      hFirst hSecond hDistinct hRelation⟩

theorem positiveDistinctTripleSingleRelation_hasRealSquareRoot
    {target : Matrix4}
    (hTarget : HasPositiveDistinctTripleSingleRelation4 target) :
    HasRealSquareRoot target := by
  obtain ⟨first, second, hFirst, hSecond, hDistinct, hRelation⟩ := hTarget
  exact ⟨positiveTripleSingleHermiteRoot4 target first second,
    positiveTripleSingleHermiteRoot4_square
      hFirst hSecond hDistinct hRelation⟩

/-- Exact positive raw residual after adjoining the `3 + 1` Hermite locus. -/
def PositiveOutsideKnownLociAndTripleSingleRootResidual4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    ¬ target.PosSemidef → ¬ HasPositiveRealQuadraticRelation4 target →
      ¬ HasPositiveSingleEigenvalueQuarticRelation4 target →
        ¬ HasPositiveDistinctDoubleDoubleRelation4 target →
          ¬ HasPositiveDistinctTripleSingleRelation4 target →
            HasRealSquareRoot target

theorem positiveRawRootClosure_iff_outsideKnownLociAndTripleSingle :
    PositiveRawRootClosure4 ↔
      PositiveOutsideKnownLociAndTripleSingleRootResidual4 := by
  constructor
  · intro closure target hSpectrum _hNotCFC _hNotQuadratic _hNotQuartic
      _hNotDoubleDouble _hNotTripleSingle
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
          · by_cases hTripleSingle :
              HasPositiveDistinctTripleSingleRelation4 target
            · exact positiveDistinctTripleSingleRelation_hasRealSquareRoot
                hTripleSingle
            · exact residual target hSpectrum hPosSemidef hQuadratic hQuartic
                hDoubleDouble hTripleSingle

end

end P0EFTJanusPositiveRawTripleSingleHermiteRoot4D
end JanusFormal
