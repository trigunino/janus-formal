import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRawSpectralBridgeReduction4D

/-!
# A raw positive quadratic root without Jordan presentation

If a real matrix is annihilated by `(X-lambda)(X-mu)` for two strictly
positive real numbers, its square root is the affine polynomial

`(A + sqrt(lambda) sqrt(mu) I) / (sqrt(lambda) + sqrt(mu))`.

This includes repeated roots and hence non-semisimple Jordan blocks of size
two.  It strictly enlarges the unconditional positive raw locus beyond
positive-semidefinite matrices and isolates only its complement.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawQuadraticRootReduction4D

set_option autoImplicit false

noncomputable section

open scoped MatrixOrder
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
open P0EFTJanusPositiveJordanTwoPlusOnePlusOneRoot4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRealSquareRootSpectralObstructions4D
open P0EFTJanusRawSpectralBridgeReduction4D

abbrev Matrix4 := P0EFTJanusRawSpectralBridgeReduction4D.Matrix4

/-- A raw positive real quadratic annihilator.  The two roots may coincide,
so this also covers a size-two Jordan nilpotent. -/
def HasPositiveRealQuadraticRelation4 (target : Matrix4) : Prop :=
  ∃ first second : Real,
    0 < first ∧ 0 < second ∧
      (target - first • (1 : Matrix4)) *
        (target - second • (1 : Matrix4)) = 0

/-- Affine principal root attached directly to the quadratic relation. -/
def positiveRealQuadraticRoot4
    (target : Matrix4) (first second : Real) : Matrix4 :=
  let firstRoot := Real.sqrt first
  let secondRoot := Real.sqrt second
  (firstRoot + secondRoot)⁻¹ •
    (target + (firstRoot * secondRoot) • (1 : Matrix4))

theorem positiveRealQuadraticRoot4_square
    {target : Matrix4} {first second : Real}
    (hFirst : 0 < first) (hSecond : 0 < second)
    (hRelation :
      (target - first • (1 : Matrix4)) *
        (target - second • (1 : Matrix4)) = 0) :
    positiveRealQuadraticRoot4 target first second *
        positiveRealQuadraticRoot4 target first second = target := by
  let firstRoot := Real.sqrt first
  let secondRoot := Real.sqrt second
  let denominator := firstRoot + secondRoot
  let productRoot := firstRoot * secondRoot
  have hFirstRoot : 0 < firstRoot := Real.sqrt_pos.2 hFirst
  have hSecondRoot : 0 < secondRoot := Real.sqrt_pos.2 hSecond
  have hDenominator : denominator ≠ 0 := by
    dsimp [denominator]
    positivity
  have hFirstSquare : firstRoot * firstRoot = first := by
    exact Real.mul_self_sqrt hFirst.le
  have hSecondSquare : secondRoot * secondRoot = second := by
    exact Real.mul_self_sqrt hSecond.le
  have hTargetSquare :
      target * target =
        (first + second) • target -
          (first * second) • (1 : Matrix4) := by
    have hExpanded :
        target * target - (first + second) • target +
            (first * second) • (1 : Matrix4) = 0 := by
      calc
        target * target - (first + second) • target +
            (first * second) • (1 : Matrix4) =
          (target - first • (1 : Matrix4)) *
            (target - second • (1 : Matrix4)) := by
              simp only [sub_mul, mul_sub, Matrix.smul_mul,
                Matrix.mul_smul, one_mul, mul_one, smul_smul]
              module
        _ = 0 := hRelation
    apply (eq_sub_iff_add_eq).2
    apply sub_eq_zero.mp
    calc
      (target * target + (first * second) • (1 : Matrix4)) -
          (first + second) • target =
        target * target - (first + second) • target +
          (first * second) • (1 : Matrix4) := by abel
      _ = 0 := hExpanded
  have hProductSquare : productRoot * productRoot = first * second := by
    dsimp [productRoot]
    nlinarith
  have hCoefficient :
      first + second + 2 * productRoot = denominator ^ 2 := by
    dsimp [denominator, productRoot]
    nlinarith
  have hNumeratorSquare :
      (target + productRoot • (1 : Matrix4)) *
          (target + productRoot • (1 : Matrix4)) =
        denominator ^ 2 • target := by
    calc
      (target + productRoot • (1 : Matrix4)) *
          (target + productRoot • (1 : Matrix4)) =
        target * target + (2 * productRoot) • target +
          (productRoot * productRoot) • (1 : Matrix4) := by
            simp only [add_mul, mul_add, Matrix.smul_mul,
              Matrix.mul_smul, one_mul, mul_one, smul_smul]
            module
      _ = (first + second + 2 * productRoot) • target +
          (productRoot * productRoot - first * second) •
            (1 : Matrix4) := by
              rw [hTargetSquare]
              module
      _ = denominator ^ 2 • target := by
        rw [hProductSquare, hCoefficient]
        simp
  change
    (denominator⁻¹ •
        (target + productRoot • (1 : Matrix4))) *
      (denominator⁻¹ •
        (target + productRoot • (1 : Matrix4))) = target
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hNumeratorSquare,
    smul_smul]
  have hScalar : denominator⁻¹ * denominator⁻¹ * denominator ^ 2 = 1 := by
    field_simp [hDenominator]
  rw [hScalar, one_smul]

theorem positiveRealQuadraticRelation_hasRealSquareRoot
    {target : Matrix4} (hTarget : HasPositiveRealQuadraticRelation4 target) :
    HasRealSquareRoot target := by
  obtain ⟨first, second, hFirst, hSecond, hRelation⟩ := hTarget
  exact ⟨positiveRealQuadraticRoot4 target first second,
    positiveRealQuadraticRoot4_square hFirst hSecond hRelation⟩

/-- A strict non-Hermitian, hence non-PSD, raw family covered by the new
quadratic theorem. -/
theorem canonicalJordan211Repeated_hasPositiveRealQuadraticRelation
    (eigenvalue : PositiveEigenvalue) :
    HasPositiveRealQuadraticRelation4
      (canonicalJordan211Target eigenvalue eigenvalue eigenvalue) := by
  refine ⟨eigenvalue.1, eigenvalue.1, eigenvalue.2, eigenvalue.2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalJordan211Target, jordan211DiagonalTarget,
      jordan211TargetSpectrum, jordan211TargetNilpotent,
      Matrix.mul_apply, Fin.sum_univ_four]

theorem canonicalJordan211Repeated_not_isHermitian
    (eigenvalue : PositiveEigenvalue) :
    ¬ (canonicalJordan211Target eigenvalue eigenvalue eigenvalue).IsHermitian := by
  intro hHermitian
  have hEntry := hHermitian.apply (0 : Fin 4) (1 : Fin 4)
  simp [canonicalJordan211Target, jordan211DiagonalTarget,
    jordan211TargetSpectrum, jordan211TargetNilpotent] at hEntry

theorem canonicalJordan211Repeated_not_posSemidef
    (eigenvalue : PositiveEigenvalue) :
    ¬ (canonicalJordan211Target eigenvalue eigenvalue eigenvalue).PosSemidef := by
  intro hPosSemidef
  exact canonicalJordan211Repeated_not_isHermitian eigenvalue
    hPosSemidef.isHermitian

/-- The positive raw locus now closed without presentation. -/
def PositiveRawCFCOrQuadraticLocus4 (target : Matrix4) : Prop :=
  target.PosSemidef ∨ HasPositiveRealQuadraticRelation4 target

theorem positiveRawCFCOrQuadraticLocus_hasRealSquareRoot
    {target : Matrix4} (hTarget : PositiveRawCFCOrQuadraticLocus4 target) :
    HasRealSquareRoot target := by
  rcases hTarget with hPosSemidef | hQuadratic
  · exact posSemidef_hasRealSquareRoot hPosSemidef
  · exact positiveRealQuadraticRelation_hasRealSquareRoot hQuadratic

/-- Exact positive residual after removing both CFC and the raw positive
quadratic locus. -/
def PositiveOutsideCFCAndQuadraticRootResidual4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    ¬ target.PosSemidef → ¬ HasPositiveRealQuadraticRelation4 target →
      HasRealSquareRoot target

theorem positiveRawRootClosure_iff_outsideCFCAndQuadraticResidual :
    PositiveRawRootClosure4 ↔
      PositiveOutsideCFCAndQuadraticRootResidual4 := by
  constructor
  · intro closure target hSpectrum _hNotCFC _hNotQuadratic
    exact closure target hSpectrum
  · intro residual target hSpectrum
    by_cases hPosSemidef : target.PosSemidef
    · exact posSemidef_hasRealSquareRoot hPosSemidef
    · by_cases hQuadratic : HasPositiveRealQuadraticRelation4 target
      · exact positiveRealQuadraticRelation_hasRealSquareRoot hQuadratic
      · exact residual target hSpectrum hPosSemidef hQuadratic

end

end P0EFTJanusPositiveRawQuadraticRootReduction4D
end JanusFormal
