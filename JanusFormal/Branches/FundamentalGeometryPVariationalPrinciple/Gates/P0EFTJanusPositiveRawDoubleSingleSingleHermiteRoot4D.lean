import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawTripleSingleHermiteRoot4D

/-!
# A raw positive `2 + 1 + 1` Hermite cubic root

For three pairwise distinct positive nodes, this gate closes
`(A - lambda I)^2 (A - mu I) (A - nu I) = 0`.  The explicit cubic matches
the value and first derivative of `sqrt` at `lambda`, and its values at
`mu` and `nu`.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawDoubleSingleSingleHermiteRoot4D

set_option autoImplicit false

noncomputable section

open scoped MatrixOrder
open Polynomial
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveRawQuadraticRootReduction4D
open P0EFTJanusPositiveRawPolynomialRootReduction4D
open P0EFTJanusPositiveRawDoubleDoubleHermiteRoot4D
open P0EFTJanusPositiveRawTripleSingleHermiteRoot4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRealSquareRootSpectralObstructions4D
open P0EFTJanusRawSpectralBridgeReduction4D

abbrev Matrix4 := P0EFTJanusPositiveRawTripleSingleHermiteRoot4D.Matrix4

def doubleSingleSingleQuadraticCoefficient
    (doubleNode firstSimple : Real) : Real :=
  let displacement := firstSimple - doubleNode
  (Real.sqrt firstSimple - Real.sqrt doubleNode -
      displacement / (2 * Real.sqrt doubleNode)) /
    displacement ^ 2

def doubleSingleSingleCubicCoefficient
    (doubleNode firstSimple secondSimple : Real) : Real :=
  let displacement := secondSimple - doubleNode
  (Real.sqrt secondSimple - Real.sqrt doubleNode -
      displacement / (2 * Real.sqrt doubleNode) -
      doubleSingleSingleQuadraticCoefficient doubleNode firstSimple *
        displacement ^ 2) /
    (displacement ^ 2 * (secondSimple - firstSimple))

/-- The cubic Hermite interpolant with a double first node and two simple
nodes. -/
def positiveDoubleSingleSingleHermitePolynomial
    (doubleNode firstSimple secondSimple : Real) : Polynomial Real :=
  let centered := X - C doubleNode
  C (Real.sqrt doubleNode) +
    C (1 / (2 * Real.sqrt doubleNode)) * centered +
    C (doubleSingleSingleQuadraticCoefficient doubleNode firstSimple) *
      centered ^ 2 +
    C (doubleSingleSingleCubicCoefficient
      doubleNode firstSimple secondSimple) *
      centered ^ 2 * (X - C firstSimple)

theorem positiveDoubleSingleSingleHermitePolynomial_natDegree_le_three
    (doubleNode firstSimple secondSimple : Real) :
    (positiveDoubleSingleSingleHermitePolynomial
      doubleNode firstSimple secondSimple).natDegree ≤ 3 := by
  unfold positiveDoubleSingleSingleHermitePolynomial
  have hConstant :
      (C (Real.sqrt doubleNode) : Polynomial Real).natDegree ≤ 3 := by
    simp
  have hLinear :
      (C (1 / (2 * Real.sqrt doubleNode)) *
        (X - C doubleNode)).natDegree ≤ 3 :=
    (natDegree_C_mul_le _ _).trans
      ((natDegree_X_sub_C_le doubleNode).trans (by norm_num))
  have hQuadratic :
      (C (doubleSingleSingleQuadraticCoefficient
          doubleNode firstSimple) *
        (X - C doubleNode) ^ 2).natDegree ≤ 3 :=
    (natDegree_C_mul_le _ _).trans
      ((natDegree_pow_le_of_le 2
        (natDegree_X_sub_C_le doubleNode)).trans (by norm_num))
  have hCubicProduct :
      (((X - C doubleNode) ^ 2) *
        (X - C firstSimple)).natDegree ≤ 3 :=
    (natDegree_mul_le_of_le
      (natDegree_pow_le_of_le 2 (natDegree_X_sub_C_le doubleNode))
      (natDegree_X_sub_C_le firstSimple)).trans (by norm_num)
  have hCubic :
      (C (doubleSingleSingleCubicCoefficient
          doubleNode firstSimple secondSimple) *
        (X - C doubleNode) ^ 2 *
          (X - C firstSimple)).natDegree ≤ 3 := by
    rw [mul_assoc]
    exact (natDegree_C_mul_le _ _).trans hCubicProduct
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le hConstant hLinear) hQuadratic) hCubic

theorem positiveDoubleSingleSingleHermitePolynomial_eval_doubleNode
    (doubleNode firstSimple secondSimple : Real) :
    (positiveDoubleSingleSingleHermitePolynomial
      doubleNode firstSimple secondSimple).eval doubleNode =
      Real.sqrt doubleNode := by
  simp [positiveDoubleSingleSingleHermitePolynomial]

theorem positiveDoubleSingleSingleHermitePolynomial_derivative_eval_doubleNode
    (doubleNode firstSimple secondSimple : Real) :
    (positiveDoubleSingleSingleHermitePolynomial
      doubleNode firstSimple secondSimple).derivative.eval doubleNode =
      1 / (2 * Real.sqrt doubleNode) := by
  simp [positiveDoubleSingleSingleHermitePolynomial, derivative_pow]

theorem positiveDoubleSingleSingleHermitePolynomial_eval_firstSimple
    {doubleNode firstSimple secondSimple : Real}
    (hDoubleNode : 0 < doubleNode)
    (hDoubleFirst : doubleNode ≠ firstSimple) :
    (positiveDoubleSingleSingleHermitePolynomial
      doubleNode firstSimple secondSimple).eval firstSimple =
      Real.sqrt firstSimple := by
  have hDisplacement : firstSimple - doubleNode ≠ 0 :=
    sub_ne_zero.mpr hDoubleFirst.symm
  have hSqrtDouble : Real.sqrt doubleNode ≠ 0 :=
    (Real.sqrt_pos.2 hDoubleNode).ne'
  simp [positiveDoubleSingleSingleHermitePolynomial,
    doubleSingleSingleQuadraticCoefficient]
  field_simp [hDisplacement, hSqrtDouble]
  ring

theorem positiveDoubleSingleSingleHermitePolynomial_eval_secondSimple
    {doubleNode firstSimple secondSimple : Real}
    (hDoubleNode : 0 < doubleNode)
    (hDoubleFirst : doubleNode ≠ firstSimple)
    (hDoubleSecond : doubleNode ≠ secondSimple)
    (hFirstSecond : firstSimple ≠ secondSimple) :
    (positiveDoubleSingleSingleHermitePolynomial
      doubleNode firstSimple secondSimple).eval secondSimple =
      Real.sqrt secondSimple := by
  have hDoubleFirstDisplacement : firstSimple - doubleNode ≠ 0 :=
    sub_ne_zero.mpr hDoubleFirst.symm
  have hDoubleSecondDisplacement : secondSimple - doubleNode ≠ 0 :=
    sub_ne_zero.mpr hDoubleSecond.symm
  have hFirstSecondDisplacement : secondSimple - firstSimple ≠ 0 :=
    sub_ne_zero.mpr hFirstSecond.symm
  have hSqrtDouble : Real.sqrt doubleNode ≠ 0 :=
    (Real.sqrt_pos.2 hDoubleNode).ne'
  simp [positiveDoubleSingleSingleHermitePolynomial,
    doubleSingleSingleQuadraticCoefficient,
    doubleSingleSingleCubicCoefficient]
  field_simp [hDoubleFirstDisplacement, hDoubleSecondDisplacement,
    hFirstSecondDisplacement, hSqrtDouble]
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

def positiveDoubleSingleSingleSquareResidual
    (doubleNode firstSimple secondSimple : Real) : Polynomial Real :=
  positiveDoubleSingleSingleHermitePolynomial
      doubleNode firstSimple secondSimple *
    positiveDoubleSingleSingleHermitePolynomial
      doubleNode firstSimple secondSimple - X

theorem positiveDoubleSingleSingleSquareResidual_eval_doubleNode
    {doubleNode firstSimple secondSimple : Real}
    (hDoubleNode : 0 < doubleNode) :
    (positiveDoubleSingleSingleSquareResidual
      doubleNode firstSimple secondSimple).eval doubleNode = 0 := by
  rw [positiveDoubleSingleSingleSquareResidual, eval_sub, eval_mul,
    positiveDoubleSingleSingleHermitePolynomial_eval_doubleNode, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hDoubleNode.le)

theorem positiveDoubleSingleSingleSquareResidual_derivative_eval_doubleNode
    {doubleNode firstSimple secondSimple : Real}
    (hDoubleNode : 0 < doubleNode) :
    (positiveDoubleSingleSingleSquareResidual
      doubleNode firstSimple secondSimple).derivative.eval doubleNode = 0 := by
  have hSqrt : Real.sqrt doubleNode ≠ 0 :=
    (Real.sqrt_pos.2 hDoubleNode).ne'
  simp [positiveDoubleSingleSingleSquareResidual,
    positiveDoubleSingleSingleHermitePolynomial_eval_doubleNode,
    positiveDoubleSingleSingleHermitePolynomial_derivative_eval_doubleNode]
  field_simp [hSqrt]
  ring

theorem positiveDoubleSingleSingleSquareResidual_eval_firstSimple
    {doubleNode firstSimple secondSimple : Real}
    (hDoubleNode : 0 < doubleNode) (hFirstSimple : 0 < firstSimple)
    (hDoubleFirst : doubleNode ≠ firstSimple) :
    (positiveDoubleSingleSingleSquareResidual
      doubleNode firstSimple secondSimple).eval firstSimple = 0 := by
  rw [positiveDoubleSingleSingleSquareResidual, eval_sub, eval_mul,
    positiveDoubleSingleSingleHermitePolynomial_eval_firstSimple
      hDoubleNode hDoubleFirst, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hFirstSimple.le)

theorem positiveDoubleSingleSingleSquareResidual_eval_secondSimple
    {doubleNode firstSimple secondSimple : Real}
    (hDoubleNode : 0 < doubleNode) (hSecondSimple : 0 < secondSimple)
    (hDoubleFirst : doubleNode ≠ firstSimple)
    (hDoubleSecond : doubleNode ≠ secondSimple)
    (hFirstSecond : firstSimple ≠ secondSimple) :
    (positiveDoubleSingleSingleSquareResidual
      doubleNode firstSimple secondSimple).eval secondSimple = 0 := by
  rw [positiveDoubleSingleSingleSquareResidual, eval_sub, eval_mul,
    positiveDoubleSingleSingleHermitePolynomial_eval_secondSimple
      hDoubleNode hDoubleFirst hDoubleSecond hFirstSecond, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hSecondSimple.le)

theorem positiveDoubleSingleSingleAnnihilator_dvd_squareResidual
    {doubleNode firstSimple secondSimple : Real}
    (hDoubleNode : 0 < doubleNode) (hFirstSimple : 0 < firstSimple)
    (hSecondSimple : 0 < secondSimple)
    (hDoubleFirst : doubleNode ≠ firstSimple)
    (hDoubleSecond : doubleNode ≠ secondSimple)
    (hFirstSecond : firstSimple ≠ secondSimple) :
    (X - C doubleNode) ^ 2 * (X - C firstSimple) *
        (X - C secondSimple) ∣
      positiveDoubleSingleSingleSquareResidual
        doubleNode firstSimple secondSimple := by
  have hDoubleDvd : (X - C doubleNode) ^ 2 ∣
      positiveDoubleSingleSingleSquareResidual
        doubleNode firstSimple secondSimple :=
    X_sub_C_sq_dvd_of_eval_derivative_eq_zero
      (positiveDoubleSingleSingleSquareResidual_eval_doubleNode hDoubleNode)
      (positiveDoubleSingleSingleSquareResidual_derivative_eval_doubleNode
        hDoubleNode)
  have hFirstDvd : X - C firstSimple ∣
      positiveDoubleSingleSingleSquareResidual
        doubleNode firstSimple secondSimple :=
    (dvd_iff_isRoot).2
      (positiveDoubleSingleSingleSquareResidual_eval_firstSimple
        hDoubleNode hFirstSimple hDoubleFirst)
  have hSecondDvd : X - C secondSimple ∣
      positiveDoubleSingleSingleSquareResidual
        doubleNode firstSimple secondSimple :=
    (dvd_iff_isRoot).2
      (positiveDoubleSingleSingleSquareResidual_eval_secondSimple
        hDoubleNode hSecondSimple hDoubleFirst hDoubleSecond hFirstSecond)
  have hDoubleFirstCoprime :
      IsCoprime ((X - C doubleNode) ^ 2) (X - C firstSimple) :=
    (isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hDoubleFirst).isUnit).pow_left
  have hDoubleSecondCoprime :
      IsCoprime ((X - C doubleNode) ^ 2) (X - C secondSimple) :=
    (isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hDoubleSecond).isUnit).pow_left
  have hFirstSecondCoprime :
      IsCoprime (X - C firstSimple) (X - C secondSimple) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hFirstSecond).isUnit
  have hDoubleFirstDvd :
      (X - C doubleNode) ^ 2 * (X - C firstSimple) ∣
        positiveDoubleSingleSingleSquareResidual
          doubleNode firstSimple secondSimple :=
    hDoubleFirstCoprime.mul_dvd hDoubleDvd hFirstDvd
  exact (IsCoprime.mul_left hDoubleSecondCoprime hFirstSecondCoprime).mul_dvd
    hDoubleFirstDvd hSecondDvd

/-- A raw positive `2 + 1 + 1` annihilator with pairwise distinct nodes. -/
def HasPositiveDistinctDoubleSingleSingleRelation4 (target : Matrix4) : Prop :=
  ∃ doubleNode firstSimple secondSimple : Real,
    0 < doubleNode ∧ 0 < firstSimple ∧ 0 < secondSimple ∧
      doubleNode ≠ firstSimple ∧ doubleNode ≠ secondSimple ∧
        firstSimple ≠ secondSimple ∧
    let doubleDisplacement := target - doubleNode • (1 : Matrix4)
    let firstDisplacement := target - firstSimple • (1 : Matrix4)
    let secondDisplacement := target - secondSimple • (1 : Matrix4)
    doubleDisplacement * doubleDisplacement * firstDisplacement *
      secondDisplacement = 0

def positiveDoubleSingleSingleHermiteRoot4
    (target : Matrix4) (doubleNode firstSimple secondSimple : Real) : Matrix4 :=
  Polynomial.aeval target
    (positiveDoubleSingleSingleHermitePolynomial
      doubleNode firstSimple secondSimple)

theorem positiveDoubleSingleSingleHermitePolynomial_minpoly_congruence
    {target : Matrix4} {doubleNode firstSimple secondSimple : Real}
    (hDoubleNode : 0 < doubleNode) (hFirstSimple : 0 < firstSimple)
    (hSecondSimple : 0 < secondSimple)
    (hDoubleFirst : doubleNode ≠ firstSimple)
    (hDoubleSecond : doubleNode ≠ secondSimple)
    (hFirstSecond : firstSimple ≠ secondSimple)
    (hRelation :
      let doubleDisplacement := target - doubleNode • (1 : Matrix4)
      let firstDisplacement := target - firstSimple • (1 : Matrix4)
      let secondDisplacement := target - secondSimple • (1 : Matrix4)
      doubleDisplacement * doubleDisplacement * firstDisplacement *
        secondDisplacement = 0) :
    minpoly Real target ∣
      positiveDoubleSingleSingleSquareResidual
        doubleNode firstSimple secondSimple := by
  have hAnnihilator :
      Polynomial.aeval target
        ((X - C doubleNode) ^ 2 * (X - C firstSimple) *
          (X - C secondSimple)) = 0 := by
    simpa [pow_two, Algebra.smul_def, mul_assoc] using hRelation
  have hMinpolyAnnihilator : minpoly Real target ∣
      (X - C doubleNode) ^ 2 * (X - C firstSimple) *
        (X - C secondSimple) :=
    minpoly.dvd Real target hAnnihilator
  exact hMinpolyAnnihilator.trans
    (positiveDoubleSingleSingleAnnihilator_dvd_squareResidual
      hDoubleNode hFirstSimple hSecondSimple hDoubleFirst hDoubleSecond
      hFirstSecond)

theorem positiveDoubleSingleSingleHermiteRoot4_square
    {target : Matrix4} {doubleNode firstSimple secondSimple : Real}
    (hDoubleNode : 0 < doubleNode) (hFirstSimple : 0 < firstSimple)
    (hSecondSimple : 0 < secondSimple)
    (hDoubleFirst : doubleNode ≠ firstSimple)
    (hDoubleSecond : doubleNode ≠ secondSimple)
    (hFirstSecond : firstSimple ≠ secondSimple)
    (hRelation :
      let doubleDisplacement := target - doubleNode • (1 : Matrix4)
      let firstDisplacement := target - firstSimple • (1 : Matrix4)
      let secondDisplacement := target - secondSimple • (1 : Matrix4)
      doubleDisplacement * doubleDisplacement * firstDisplacement *
        secondDisplacement = 0) :
    positiveDoubleSingleSingleHermiteRoot4
        target doubleNode firstSimple secondSimple *
      positiveDoubleSingleSingleHermiteRoot4
        target doubleNode firstSimple secondSimple = target := by
  exact cubicMinpolyRoot4_square
    (positiveDoubleSingleSingleHermitePolynomial_minpoly_congruence
      hDoubleNode hFirstSimple hSecondSimple hDoubleFirst hDoubleSecond
      hFirstSecond hRelation)

theorem positiveDistinctDoubleSingleSingleRelation_hasCubicMinpolyRoot
    {target : Matrix4}
    (hTarget : HasPositiveDistinctDoubleSingleSingleRelation4 target) :
    HasCubicPolynomialSquareRootModuloMinpoly4 target := by
  obtain ⟨doubleNode, firstSimple, secondSimple, hDoubleNode, hFirstSimple,
    hSecondSimple, hDoubleFirst, hDoubleSecond, hFirstSecond, hRelation⟩ :=
      hTarget
  exact ⟨positiveDoubleSingleSingleHermitePolynomial
      doubleNode firstSimple secondSimple,
    positiveDoubleSingleSingleHermitePolynomial_natDegree_le_three
      doubleNode firstSimple secondSimple,
    positiveDoubleSingleSingleHermitePolynomial_minpoly_congruence
      hDoubleNode hFirstSimple hSecondSimple hDoubleFirst hDoubleSecond
      hFirstSecond hRelation⟩

theorem positiveDistinctDoubleSingleSingleRelation_hasRealSquareRoot
    {target : Matrix4}
    (hTarget : HasPositiveDistinctDoubleSingleSingleRelation4 target) :
    HasRealSquareRoot target := by
  obtain ⟨doubleNode, firstSimple, secondSimple, hDoubleNode, hFirstSimple,
    hSecondSimple, hDoubleFirst, hDoubleSecond, hFirstSecond, hRelation⟩ :=
      hTarget
  exact ⟨positiveDoubleSingleSingleHermiteRoot4
      target doubleNode firstSimple secondSimple,
    positiveDoubleSingleSingleHermiteRoot4_square
      hDoubleNode hFirstSimple hSecondSimple hDoubleFirst hDoubleSecond
      hFirstSecond hRelation⟩

/-- Exact positive raw residual after adjoining the `2 + 1 + 1` Hermite
locus.  Among positive split multiplicity patterns, only four distinct simple
nodes remain. -/
def PositiveOutsideKnownLociAndDoubleSingleSingleRootResidual4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    ¬ target.PosSemidef → ¬ HasPositiveRealQuadraticRelation4 target →
      ¬ HasPositiveSingleEigenvalueQuarticRelation4 target →
        ¬ HasPositiveDistinctDoubleDoubleRelation4 target →
          ¬ HasPositiveDistinctTripleSingleRelation4 target →
            ¬ HasPositiveDistinctDoubleSingleSingleRelation4 target →
              HasRealSquareRoot target

theorem positiveRawRootClosure_iff_outsideKnownLociAndDoubleSingleSingle :
    PositiveRawRootClosure4 ↔
      PositiveOutsideKnownLociAndDoubleSingleSingleRootResidual4 := by
  constructor
  · intro closure target hSpectrum _hNotCFC _hNotQuadratic _hNotQuartic
      _hNotDoubleDouble _hNotTripleSingle _hNotDoubleSingleSingle
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
            · by_cases hDoubleSingleSingle :
                HasPositiveDistinctDoubleSingleSingleRelation4 target
              · exact
                  positiveDistinctDoubleSingleSingleRelation_hasRealSquareRoot
                    hDoubleSingleSingle
              · exact residual target hSpectrum hPosSemidef hQuadratic hQuartic
                  hDoubleDouble hTripleSingle hDoubleSingleSingle

end

end P0EFTJanusPositiveRawDoubleSingleSingleHermiteRoot4D
end JanusFormal
