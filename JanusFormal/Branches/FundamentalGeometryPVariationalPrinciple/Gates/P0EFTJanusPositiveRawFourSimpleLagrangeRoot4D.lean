import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawTripleSingleHermiteRoot4D

/-!
# A raw positive four-simple Lagrange root

For four pairwise distinct positive nodes, the cubic Lagrange interpolant of
`sqrt` squares to the identity polynomial modulo the corresponding
annihilator.  This closes the semisimple four-eigenvalue raw locus without a
chosen eigenbasis or a Hermitian hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawFourSimpleLagrangeRoot4D

set_option autoImplicit false

noncomputable section

open scoped MatrixOrder
open Polynomial
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveRawPolynomialRootReduction4D
open P0EFTJanusPositiveRawTripleSingleHermiteRoot4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRealSquareRootSpectralObstructions4D

abbrev Matrix4 := P0EFTJanusPositiveRawTripleSingleHermiteRoot4D.Matrix4

private def positiveLagrangeTerm
    (node other₁ other₂ other₃ : Real) : Polynomial Real :=
  C (Real.sqrt node /
      ((node - other₁) * (node - other₂) * (node - other₃))) *
    (X - C other₁) * (X - C other₂) * (X - C other₃)

/-- The degree-three polynomial taking the value `sqrt node` at each of four
distinct nodes. -/
def positiveFourSimpleLagrangePolynomial
    (first second third fourth : Real) : Polynomial Real :=
  positiveLagrangeTerm first second third fourth +
    positiveLagrangeTerm second first third fourth +
    positiveLagrangeTerm third first second fourth +
    positiveLagrangeTerm fourth first second third

private theorem positiveLagrangeTerm_natDegree_le_three
    (node other₁ other₂ other₃ : Real) :
    (positiveLagrangeTerm node other₁ other₂ other₃).natDegree ≤ 3 := by
  unfold positiveLagrangeTerm
  have hFirst : ((X - C other₁) * (X - C other₂)).natDegree ≤ 2 :=
    natDegree_mul_le_of_le (natDegree_X_sub_C_le other₁)
      (natDegree_X_sub_C_le other₂)
  have hProduct :
      (((X - C other₁) * (X - C other₂)) *
        (X - C other₃)).natDegree ≤ 3 :=
    natDegree_mul_le_of_le hFirst (natDegree_X_sub_C_le other₃)
  have hGrouped := (natDegree_C_mul_le
    (Real.sqrt node /
      ((node - other₁) * (node - other₂) * (node - other₃))) _).trans hProduct
  simpa [mul_assoc] using hGrouped

theorem positiveFourSimpleLagrangePolynomial_natDegree_le_three
    (first second third fourth : Real) :
    (positiveFourSimpleLagrangePolynomial first second third fourth).natDegree ≤ 3 := by
  unfold positiveFourSimpleLagrangePolynomial
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (positiveLagrangeTerm_natDegree_le_three first second third fourth)
        (positiveLagrangeTerm_natDegree_le_three second first third fourth))
      (positiveLagrangeTerm_natDegree_le_three third first second fourth))
    (positiveLagrangeTerm_natDegree_le_three fourth first second third)

theorem positiveFourSimpleLagrangePolynomial_eval_first
    {first second third fourth : Real}
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third)
    (hFirstFourth : first ≠ fourth) :
    (positiveFourSimpleLagrangePolynomial first second third fourth).eval first =
      Real.sqrt first := by
  simp [positiveFourSimpleLagrangePolynomial, positiveLagrangeTerm]
  field_simp [sub_ne_zero.mpr hFirstSecond,
    sub_ne_zero.mpr hFirstThird, sub_ne_zero.mpr hFirstFourth]

theorem positiveFourSimpleLagrangePolynomial_eval_second
    {first second third fourth : Real}
    (hFirstSecond : first ≠ second) (hSecondThird : second ≠ third)
    (hSecondFourth : second ≠ fourth) :
    (positiveFourSimpleLagrangePolynomial first second third fourth).eval second =
      Real.sqrt second := by
  simp [positiveFourSimpleLagrangePolynomial, positiveLagrangeTerm]
  field_simp [sub_ne_zero.mpr hFirstSecond.symm,
    sub_ne_zero.mpr hSecondThird, sub_ne_zero.mpr hSecondFourth]

theorem positiveFourSimpleLagrangePolynomial_eval_third
    {first second third fourth : Real}
    (hFirstThird : first ≠ third) (hSecondThird : second ≠ third)
    (hThirdFourth : third ≠ fourth) :
    (positiveFourSimpleLagrangePolynomial first second third fourth).eval third =
      Real.sqrt third := by
  simp [positiveFourSimpleLagrangePolynomial, positiveLagrangeTerm]
  field_simp [sub_ne_zero.mpr hFirstThird.symm,
    sub_ne_zero.mpr hSecondThird.symm, sub_ne_zero.mpr hThirdFourth]

theorem positiveFourSimpleLagrangePolynomial_eval_fourth
    {first second third fourth : Real}
    (hFirstFourth : first ≠ fourth) (hSecondFourth : second ≠ fourth)
    (hThirdFourth : third ≠ fourth) :
    (positiveFourSimpleLagrangePolynomial first second third fourth).eval fourth =
      Real.sqrt fourth := by
  simp [positiveFourSimpleLagrangePolynomial, positiveLagrangeTerm]
  field_simp [sub_ne_zero.mpr hFirstFourth.symm,
    sub_ne_zero.mpr hSecondFourth.symm,
    sub_ne_zero.mpr hThirdFourth.symm]

def positiveFourSimpleSquareResidual
    (first second third fourth : Real) : Polynomial Real :=
  positiveFourSimpleLagrangePolynomial first second third fourth *
      positiveFourSimpleLagrangePolynomial first second third fourth - X

private theorem positiveFourSimpleSquareResidual_eval_first
    {first second third fourth : Real} (hFirst : 0 < first)
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third)
    (hFirstFourth : first ≠ fourth) :
    (positiveFourSimpleSquareResidual first second third fourth).eval first = 0 := by
  rw [positiveFourSimpleSquareResidual, eval_sub, eval_mul,
    positiveFourSimpleLagrangePolynomial_eval_first hFirstSecond hFirstThird
      hFirstFourth, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hFirst.le)

private theorem positiveFourSimpleSquareResidual_eval_second
    {first second third fourth : Real} (hSecond : 0 < second)
    (hFirstSecond : first ≠ second) (hSecondThird : second ≠ third)
    (hSecondFourth : second ≠ fourth) :
    (positiveFourSimpleSquareResidual first second third fourth).eval second = 0 := by
  rw [positiveFourSimpleSquareResidual, eval_sub, eval_mul,
    positiveFourSimpleLagrangePolynomial_eval_second hFirstSecond hSecondThird
      hSecondFourth, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hSecond.le)

private theorem positiveFourSimpleSquareResidual_eval_third
    {first second third fourth : Real} (hThird : 0 < third)
    (hFirstThird : first ≠ third) (hSecondThird : second ≠ third)
    (hThirdFourth : third ≠ fourth) :
    (positiveFourSimpleSquareResidual first second third fourth).eval third = 0 := by
  rw [positiveFourSimpleSquareResidual, eval_sub, eval_mul,
    positiveFourSimpleLagrangePolynomial_eval_third hFirstThird hSecondThird
      hThirdFourth, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hThird.le)

private theorem positiveFourSimpleSquareResidual_eval_fourth
    {first second third fourth : Real} (hFourth : 0 < fourth)
    (hFirstFourth : first ≠ fourth) (hSecondFourth : second ≠ fourth)
    (hThirdFourth : third ≠ fourth) :
    (positiveFourSimpleSquareResidual first second third fourth).eval fourth = 0 := by
  rw [positiveFourSimpleSquareResidual, eval_sub, eval_mul,
    positiveFourSimpleLagrangePolynomial_eval_fourth hFirstFourth hSecondFourth
      hThirdFourth, eval_X]
  exact sub_eq_zero.mpr (Real.mul_self_sqrt hFourth.le)

theorem positiveFourSimpleAnnihilator_dvd_squareResidual
    {first second third fourth : Real}
    (hFirst : 0 < first) (hSecond : 0 < second)
    (hThird : 0 < third) (hFourth : 0 < fourth)
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third)
    (hFirstFourth : first ≠ fourth) (hSecondThird : second ≠ third)
    (hSecondFourth : second ≠ fourth) (hThirdFourth : third ≠ fourth) :
    (X - C first) * (X - C second) * (X - C third) * (X - C fourth) ∣
      positiveFourSimpleSquareResidual first second third fourth := by
  have hFirstDvd : X - C first ∣
      positiveFourSimpleSquareResidual first second third fourth :=
    (dvd_iff_isRoot).2 (positiveFourSimpleSquareResidual_eval_first hFirst
      hFirstSecond hFirstThird hFirstFourth)
  have hSecondDvd : X - C second ∣
      positiveFourSimpleSquareResidual first second third fourth :=
    (dvd_iff_isRoot).2 (positiveFourSimpleSquareResidual_eval_second hSecond
      hFirstSecond hSecondThird hSecondFourth)
  have hThirdDvd : X - C third ∣
      positiveFourSimpleSquareResidual first second third fourth :=
    (dvd_iff_isRoot).2 (positiveFourSimpleSquareResidual_eval_third hThird
      hFirstThird hSecondThird hThirdFourth)
  have hFourthDvd : X - C fourth ∣
      positiveFourSimpleSquareResidual first second third fourth :=
    (dvd_iff_isRoot).2 (positiveFourSimpleSquareResidual_eval_fourth hFourth
      hFirstFourth hSecondFourth hThirdFourth)
  have hFirstSecondCoprime : IsCoprime (X - C first) (X - C second) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hFirstSecond).isUnit
  have hFirstThirdCoprime : IsCoprime (X - C first) (X - C third) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hFirstThird).isUnit
  have hSecondThirdCoprime : IsCoprime (X - C second) (X - C third) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hSecondThird).isUnit
  have hFirstFourthCoprime : IsCoprime (X - C first) (X - C fourth) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hFirstFourth).isUnit
  have hSecondFourthCoprime : IsCoprime (X - C second) (X - C fourth) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hSecondFourth).isUnit
  have hThirdFourthCoprime : IsCoprime (X - C third) (X - C fourth) :=
    isCoprime_X_sub_C_of_isUnit_sub
      (sub_ne_zero.mpr hThirdFourth).isUnit
  have hFirstSecondDvd : (X - C first) * (X - C second) ∣
      positiveFourSimpleSquareResidual first second third fourth :=
    hFirstSecondCoprime.mul_dvd hFirstDvd hSecondDvd
  have hFirstSecondThirdDvd :
      (X - C first) * (X - C second) * (X - C third) ∣
        positiveFourSimpleSquareResidual first second third fourth :=
    (hFirstThirdCoprime.mul_left hSecondThirdCoprime).mul_dvd
      hFirstSecondDvd hThirdDvd
  exact ((hFirstFourthCoprime.mul_left hSecondFourthCoprime).mul_left
    hThirdFourthCoprime).mul_dvd hFirstSecondThirdDvd hFourthDvd

/-- A raw annihilator with four distinct positive scalar nodes. -/
def HasPositiveFourSimpleRelation4 (target : Matrix4) : Prop :=
  ∃ first second third fourth : Real,
    0 < first ∧ 0 < second ∧ 0 < third ∧ 0 < fourth ∧
    first ≠ second ∧ first ≠ third ∧ first ≠ fourth ∧
    second ≠ third ∧ second ≠ fourth ∧ third ≠ fourth ∧
    let firstDisplacement := target - first • (1 : Matrix4)
    let secondDisplacement := target - second • (1 : Matrix4)
    let thirdDisplacement := target - third • (1 : Matrix4)
    let fourthDisplacement := target - fourth • (1 : Matrix4)
    firstDisplacement * secondDisplacement * thirdDisplacement *
        fourthDisplacement = 0

def positiveFourSimpleLagrangeRoot4
    (target : Matrix4) (first second third fourth : Real) : Matrix4 :=
  Polynomial.aeval target
    (positiveFourSimpleLagrangePolynomial first second third fourth)

theorem positiveFourSimpleLagrangePolynomial_minpoly_congruence
    {target : Matrix4} {first second third fourth : Real}
    (hFirst : 0 < first) (hSecond : 0 < second)
    (hThird : 0 < third) (hFourth : 0 < fourth)
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third)
    (hFirstFourth : first ≠ fourth) (hSecondThird : second ≠ third)
    (hSecondFourth : second ≠ fourth) (hThirdFourth : third ≠ fourth)
    (hRelation :
      let firstDisplacement := target - first • (1 : Matrix4)
      let secondDisplacement := target - second • (1 : Matrix4)
      let thirdDisplacement := target - third • (1 : Matrix4)
      let fourthDisplacement := target - fourth • (1 : Matrix4)
      firstDisplacement * secondDisplacement * thirdDisplacement *
          fourthDisplacement = 0) :
    minpoly Real target ∣
      positiveFourSimpleSquareResidual first second third fourth := by
  have hAnnihilator :
      Polynomial.aeval target
        ((X - C first) * (X - C second) * (X - C third) *
          (X - C fourth)) = 0 := by
    simpa [Algebra.smul_def, mul_assoc] using hRelation
  have hMinpolyAnnihilator : minpoly Real target ∣
      (X - C first) * (X - C second) * (X - C third) *
        (X - C fourth) :=
    minpoly.dvd Real target hAnnihilator
  exact hMinpolyAnnihilator.trans
    (positiveFourSimpleAnnihilator_dvd_squareResidual
      hFirst hSecond hThird hFourth hFirstSecond hFirstThird hFirstFourth
      hSecondThird hSecondFourth hThirdFourth)

theorem positiveFourSimpleLagrangeRoot4_square
    {target : Matrix4} {first second third fourth : Real}
    (hFirst : 0 < first) (hSecond : 0 < second)
    (hThird : 0 < third) (hFourth : 0 < fourth)
    (hFirstSecond : first ≠ second) (hFirstThird : first ≠ third)
    (hFirstFourth : first ≠ fourth) (hSecondThird : second ≠ third)
    (hSecondFourth : second ≠ fourth) (hThirdFourth : third ≠ fourth)
    (hRelation :
      let firstDisplacement := target - first • (1 : Matrix4)
      let secondDisplacement := target - second • (1 : Matrix4)
      let thirdDisplacement := target - third • (1 : Matrix4)
      let fourthDisplacement := target - fourth • (1 : Matrix4)
      firstDisplacement * secondDisplacement * thirdDisplacement *
          fourthDisplacement = 0) :
    positiveFourSimpleLagrangeRoot4 target first second third fourth *
        positiveFourSimpleLagrangeRoot4 target first second third fourth = target := by
  exact cubicMinpolyRoot4_square
    (positiveFourSimpleLagrangePolynomial_minpoly_congruence hFirst hSecond
      hThird hFourth hFirstSecond hFirstThird hFirstFourth hSecondThird
      hSecondFourth hThirdFourth hRelation)

theorem positiveFourSimpleRelation_hasCubicMinpolyRoot
    {target : Matrix4} (hTarget : HasPositiveFourSimpleRelation4 target) :
    HasCubicPolynomialSquareRootModuloMinpoly4 target := by
  obtain ⟨first, second, third, fourth, hFirst, hSecond, hThird, hFourth,
    hFirstSecond, hFirstThird, hFirstFourth, hSecondThird, hSecondFourth,
    hThirdFourth, hRelation⟩ := hTarget
  exact ⟨positiveFourSimpleLagrangePolynomial first second third fourth,
    positiveFourSimpleLagrangePolynomial_natDegree_le_three
      first second third fourth,
    positiveFourSimpleLagrangePolynomial_minpoly_congruence hFirst hSecond
      hThird hFourth hFirstSecond hFirstThird hFirstFourth hSecondThird
      hSecondFourth hThirdFourth hRelation⟩

theorem positiveFourSimpleRelation_hasRealSquareRoot
    {target : Matrix4} (hTarget : HasPositiveFourSimpleRelation4 target) :
    HasRealSquareRoot target := by
  exact cubicPolynomialSquareRootModuloMinpoly_hasRealSquareRoot
    (positiveFourSimpleRelation_hasCubicMinpolyRoot hTarget)

end

end P0EFTJanusPositiveRawFourSimpleLagrangeRoot4D
end JanusFormal
