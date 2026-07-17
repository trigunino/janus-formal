import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawQuadraticRootReduction4D

/-!
# Quartic and polynomial closure of the positive raw root locus

The single-positive-eigenvalue relation `(A-lambda I)^4=0` already carries a
universal third-order binomial root.  This gate promotes that construction to
the raw spectral closure, proves it strictly extends the quadratic locus by a
size-four Jordan block, and isolates the remaining multi-eigenvalue problem as
a degree-at-most-three polynomial congruence modulo the minimal polynomial.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawPolynomialRootReduction4D

set_option autoImplicit false

noncomputable section

open scoped MatrixOrder
open Polynomial
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusLorentzJordanIndexFourStratifiedRootGluing4D
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRealSquareRootSpectralObstructions4D
open P0EFTJanusRawSpectralBridgeReduction4D
open P0EFTJanusPositiveRawQuadraticRootReduction4D

abbrev Matrix4 := P0EFTJanusPositiveRawQuadraticRootReduction4D.Matrix4

/-- A raw positive single-eigenvalue annihilator of maximal possible order in
dimension four. -/
def HasPositiveSingleEigenvalueQuarticRelation4 (target : Matrix4) : Prop :=
  ∃ eigenvalue : PositiveEigenvalue,
    scaledJordanDisplacementFourth eigenvalue.1 target = 0

def positiveSingleEigenvalueQuarticData4
    (target : Matrix4) (eigenvalue : PositiveEigenvalue)
    (hFourth : scaledJordanDisplacementFourth eigenvalue.1 target = 0) :
    PositiveSingleEigenvalueJordanData :=
  ⟨(eigenvalue, target), hFourth⟩

/-- The third-order Taylor polynomial of `sqrt` around the positive
eigenvalue, evaluated on the raw matrix. -/
def positiveSingleEigenvalueQuarticRoot4
    (target : Matrix4) (eigenvalue : PositiveEigenvalue)
    (hFourth : scaledJordanDisplacementFourth eigenvalue.1 target = 0) :
    Matrix4 :=
  positiveSingleEigenvalueJordanRoot
    (positiveSingleEigenvalueQuarticData4 target eigenvalue hFourth)

theorem positiveSingleEigenvalueQuarticRoot4_square
    (target : Matrix4) (eigenvalue : PositiveEigenvalue)
    (hFourth : scaledJordanDisplacementFourth eigenvalue.1 target = 0) :
    positiveSingleEigenvalueQuarticRoot4 target eigenvalue hFourth *
        positiveSingleEigenvalueQuarticRoot4 target eigenvalue hFourth =
      target := by
  exact positiveSingleEigenvalueJordanRoot_square
    (positiveSingleEigenvalueQuarticData4 target eigenvalue hFourth)

theorem positiveSingleEigenvalueQuarticRelation_hasRealSquareRoot
    {target : Matrix4}
    (hTarget : HasPositiveSingleEigenvalueQuarticRelation4 target) :
    HasRealSquareRoot target := by
  obtain ⟨eigenvalue, hFourth⟩ := hTarget
  exact ⟨positiveSingleEigenvalueQuarticRoot4 target eigenvalue hFourth,
    positiveSingleEigenvalueQuarticRoot4_square target eigenvalue hFourth⟩

/-- The strict size-four block belongs to the quartic positive locus. -/
theorem strictIndexFourTarget4_hasPositiveSingleEigenvalueQuarticRelation :
    HasPositiveSingleEigenvalueQuarticRelation4 strictIndexFourTarget4 := by
  refine ⟨unitPositiveEigenvalue, ?_⟩
  change scaledJordanDisplacementFourth 1 strictIndexFourTarget4 = 0
  rw [scaledJordanDisplacementFourth, one_smul,
    strictIndexFourTarget4_displacement,
    strictIndexFourNilpotent4_fourth]

/-- The same strict block cannot satisfy any quadratic annihilator; its
`(0,2)` entry after multiplying the two factors is always one. -/
theorem strictIndexFourTarget4_not_positiveRealQuadraticRelation :
    ¬ HasPositiveRealQuadraticRelation4 strictIndexFourTarget4 := by
  rintro ⟨first, second, _hFirst, _hSecond, hRelation⟩
  have hEntry := congrArg
    (fun matrix : Matrix4 => matrix (0 : Fin 4) (2 : Fin 4)) hRelation
  have hFirstRow : (![(0 : Real), 1, 0, 0] : Fin 4 → Real) 2 = 0 := by
    rfl
  have hSecondRow : (![(0 : Real), 0, 1, 0] : Fin 4 → Real) 2 = 1 := by
    rfl
  have hThirdRow : (![(0 : Real), 0, 0, 1] : Fin 4 → Real) 2 = 0 := by
    rfl
  have hFourthRow : (![(0 : Real), 0, 0, 0] : Fin 4 → Real) 2 = 0 := by
    rfl
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h0s2 : (0 : Fin 4) ≠ Fin.succ (2 : Fin 3) := by decide
  have hs22 : Fin.succ (2 : Fin 3) ≠ (2 : Fin 4) := by decide
  norm_num [strictIndexFourTarget4, strictIndexFourNilpotent4,
    Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ,
    hFirstRow, hSecondRow, hThirdRow, hFourthRow,
    h02, h12, h0s2, hs22] at hEntry

theorem strictIndexFourTarget4_not_isHermitian :
    ¬ strictIndexFourTarget4.IsHermitian := by
  intro hHermitian
  have hEntry := hHermitian.apply (0 : Fin 4) (1 : Fin 4)
  norm_num [strictIndexFourTarget4, strictIndexFourNilpotent4] at hEntry

theorem strictIndexFourTarget4_not_posSemidef :
    ¬ strictIndexFourTarget4.PosSemidef := by
  intro hPosSemidef
  exact strictIndexFourTarget4_not_isHermitian hPosSemidef.isHermitian

/-- The unconditional positive raw locus after adjoining the entire
single-eigenvalue quartic family. -/
def PositiveRawCFCQuadraticOrSingleQuarticLocus4 (target : Matrix4) : Prop :=
  target.PosSemidef ∨ HasPositiveRealQuadraticRelation4 target ∨
    HasPositiveSingleEigenvalueQuarticRelation4 target

theorem positiveRawCFCQuadraticOrSingleQuarticLocus_hasRealSquareRoot
    {target : Matrix4}
    (hTarget : PositiveRawCFCQuadraticOrSingleQuarticLocus4 target) :
    HasRealSquareRoot target := by
  rcases hTarget with hPosSemidef | hQuadratic | hQuartic
  · exact posSemidef_hasRealSquareRoot hPosSemidef
  · exact positiveRealQuadraticRelation_hasRealSquareRoot hQuadratic
  · exact positiveSingleEigenvalueQuarticRelation_hasRealSquareRoot hQuartic

/-- Exact root residual after removing CFC, the positive quadratic locus and
the complete positive single-eigenvalue quartic locus. -/
def PositiveOutsideCFCQuadraticAndSingleQuarticRootResidual4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    ¬ target.PosSemidef → ¬ HasPositiveRealQuadraticRelation4 target →
      ¬ HasPositiveSingleEigenvalueQuarticRelation4 target →
        HasRealSquareRoot target

theorem positiveRawRootClosure_iff_outsideCFCQuadraticAndSingleQuartic :
    PositiveRawRootClosure4 ↔
      PositiveOutsideCFCQuadraticAndSingleQuarticRootResidual4 := by
  constructor
  · intro closure target hSpectrum _hNotCFC _hNotQuadratic _hNotQuartic
    exact closure target hSpectrum
  · intro residual target hSpectrum
    by_cases hPosSemidef : target.PosSemidef
    · exact posSemidef_hasRealSquareRoot hPosSemidef
    · by_cases hQuadratic : HasPositiveRealQuadraticRelation4 target
      · exact positiveRealQuadraticRelation_hasRealSquareRoot hQuadratic
      · by_cases hQuartic :
          HasPositiveSingleEigenvalueQuarticRelation4 target
        · exact positiveSingleEigenvalueQuarticRelation_hasRealSquareRoot
            hQuartic
        · exact residual target hSpectrum hPosSemidef hQuadratic hQuartic

/-! ## The remaining finite-dimensional Hermite interpolation contract -/

/-- A degree-at-most-three polynomial representative whose square is `X`
modulo the minimal polynomial.  Four real coefficients are enough in dimension
four; constructing them from the positive split minpoly is precisely the
remaining Hermite-interpolation step. -/
def HasCubicPolynomialSquareRootModuloMinpoly4 (target : Matrix4) : Prop :=
  ∃ rootPolynomial : Polynomial Real,
    rootPolynomial.natDegree ≤ 3 ∧
      minpoly Real target ∣
        rootPolynomial * rootPolynomial - Polynomial.X

def cubicMinpolyRoot4
    (target : Matrix4) (rootPolynomial : Polynomial Real) : Matrix4 :=
  Polynomial.aeval target rootPolynomial

theorem cubicMinpolyRoot4_square
    {target : Matrix4} {rootPolynomial : Polynomial Real}
    (hCongruence : minpoly Real target ∣
      rootPolynomial * rootPolynomial - Polynomial.X) :
    cubicMinpolyRoot4 target rootPolynomial *
        cubicMinpolyRoot4 target rootPolynomial = target := by
  obtain ⟨factor, hFactor⟩ := hCongruence
  apply sub_eq_zero.mp
  calc
    cubicMinpolyRoot4 target rootPolynomial *
          cubicMinpolyRoot4 target rootPolynomial - target =
        Polynomial.aeval target
          (rootPolynomial * rootPolynomial - Polynomial.X) := by
            simp [cubicMinpolyRoot4]
    _ = Polynomial.aeval target ((minpoly Real target) * factor) := by
      rw [hFactor]
    _ = 0 := by
      rw [map_mul, minpoly.aeval, zero_mul]

theorem cubicPolynomialSquareRootModuloMinpoly_hasRealSquareRoot
    {target : Matrix4}
    (hTarget : HasCubicPolynomialSquareRootModuloMinpoly4 target) :
    HasRealSquareRoot target := by
  obtain ⟨rootPolynomial, _hDegree, hCongruence⟩ := hTarget
  exact ⟨cubicMinpolyRoot4 target rootPolynomial,
    cubicMinpolyRoot4_square hCongruence⟩

/-- The remaining positive raw problem is reduced to four scalar polynomial
coefficients on the complement of all already closed raw loci. -/
def PositiveOutsideKnownLociCubicMinpolyResidual4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    ¬ target.PosSemidef → ¬ HasPositiveRealQuadraticRelation4 target →
      ¬ HasPositiveSingleEigenvalueQuarticRelation4 target →
        HasCubicPolynomialSquareRootModuloMinpoly4 target

theorem positiveRawRootClosure_of_cubicMinpolyResidual
    (residual : PositiveOutsideKnownLociCubicMinpolyResidual4) :
    PositiveRawRootClosure4 := by
  apply positiveRawRootClosure_iff_outsideCFCQuadraticAndSingleQuartic.2
  intro target hSpectrum hNotCFC hNotQuadratic hNotQuartic
  exact cubicPolynomialSquareRootModuloMinpoly_hasRealSquareRoot
    (residual target hSpectrum hNotCFC hNotQuadratic hNotQuartic)

end

end P0EFTJanusPositiveRawPolynomialRootReduction4D
end JanusFormal
