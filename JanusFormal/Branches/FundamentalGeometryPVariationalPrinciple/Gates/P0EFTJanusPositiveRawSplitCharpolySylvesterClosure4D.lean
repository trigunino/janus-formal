import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawSplitCharpolyRootClosure4D
import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Sylvester closure of the positive split raw locus

The raw polynomial roots from the five multiplicity profiles are already
enough for Sylvester regularity.  If `R = p(A)`, `R^2 = A`, and
`R X + X R = 0`, then `X` commutes with `A = R^2`, hence with `p(A) = R`.
Thus `2 X R = 0`; strict positivity makes `A`, and therefore `R`, a unit.
The single-eigenvalue quartic profile reuses its existing explicit Sylvester
inverse.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawSplitCharpolySylvesterClosure4D

set_option autoImplicit false

noncomputable section

open scoped MatrixOrder
open Polynomial
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
open P0EFTJanusPositiveRawPolynomialRootReduction4D
open P0EFTJanusPositiveRawDoubleDoubleHermiteRoot4D
open P0EFTJanusPositiveRawTripleSingleHermiteRoot4D
open P0EFTJanusPositiveRawDoubleSingleSingleHermiteRoot4D
open P0EFTJanusPositiveRawFourSimpleLagrangeRoot4D
open P0EFTJanusPositiveRawSplitCharpolyRootClosure4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRealSquareRootSpectralObstructions4D
open P0EFTJanusRawSpectralBridgeReduction4D

abbrev Matrix4 := P0EFTJanusRawSpectralBridgeReduction4D.Matrix4

private theorem positiveRealSplitCharpoly_isUnit
    {target : Matrix4} (hSpectrum : PositiveRealSplitCharpoly4 target) :
    IsUnit target := by
  apply (Matrix.isUnit_iff_isUnit_det target).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_eq_prod_roots_charpoly_of_splits hSpectrum.1]
  apply Multiset.prod_ne_zero
  intro hZeroMem
  have hPositive : 0 < (0 : Real) :=
    hSpectrum.2 0 (isRoot_of_mem_roots hZeroMem)
  exact (lt_irrefl 0) hPositive

/-- Basis-free Sylvester regularity for any polynomial square root of an
invertible matrix. -/
theorem polynomialSquareRoot_sylvester_bijective
    {target : Matrix4} (rootPolynomial : Polynomial Real)
    (hSquare :
      Polynomial.aeval target rootPolynomial *
          Polynomial.aeval target rootPolynomial = target)
    (hTargetUnit : IsUnit target) :
    Function.Bijective
      (sylvesterOperator (Polynomial.aeval target rootPolynomial)) := by
  let root := Polynomial.aeval target rootPolynomial
  change root * root = target at hSquare
  have hRootUnit : IsUnit root := by
    apply isUnit_mul_self_iff.mp
    rw [hSquare]
    exact hTargetUnit
  have hKernel : ∀ variation, sylvesterOperator root variation = 0 →
      variation = 0 := by
    intro variation hVariation
    have hSum : root * variation + variation * root = 0 := by
      simpa [sylvesterOperator_apply] using hVariation
    have hAnti : root * variation = -(variation * root) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hSum
    have hTargetCommutes : Commute target variation := by
      apply (commute_iff_eq target variation).2
      rw [← hSquare]
      calc
        (root * root) * variation = root * (root * variation) := by
          rw [mul_assoc]
        _ = root * (-(variation * root)) := by rw [hAnti]
        _ = -(root * variation) * root := by simp [mul_assoc]
        _ = -(-(variation * root)) * root := by rw [hAnti]
        _ = variation * (root * root) := by simp [mul_assoc]
    have hRootCommutes : Commute root variation := by
      simpa [root, Polynomial.aeval_eq_smeval] using
        (Polynomial.smeval_commute_left Real rootPolynomial hTargetCommutes)
    rw [hRootCommutes.eq] at hSum
    have hTwiceVariationRoot :
        (2 : Real) • (variation * root) = 0 := by
      simpa [two_smul] using hSum
    have hVariationRoot : variation * root = 0 :=
      (smul_eq_zero.mp hTwiceVariationRoot).resolve_left (by norm_num)
    apply hRootUnit.mul_right_cancel
    simpa using hVariationRoot
  have hInjective : Function.Injective (sylvesterOperator root) := by
    intro first second hEqual
    apply sub_eq_zero.mp
    apply hKernel (first - second)
    rw [map_sub, hEqual, sub_self]
  have hSurjective : Function.Surjective (sylvesterOperator root) := by
    have hInjectiveLinear : Function.Injective
        (sylvesterOperator root).toLinearMap := hInjective
    exact LinearMap.injective_iff_surjective.mp hInjectiveLinear
  exact ⟨hInjective, hSurjective⟩

/-- A selected raw root together with its square and Sylvester certificates. -/
structure PositiveRawRegularRootCertificate4 (target : Matrix4) where
  root : Matrix4
  square : root * root = target
  sylvesterBijective : Function.Bijective (sylvesterOperator root)

private theorem cubicMinpolyRegularRootCertificate_nonempty
    {target : Matrix4} (hSpectrum : PositiveRealSplitCharpoly4 target)
    (hCubic : HasCubicPolynomialSquareRootModuloMinpoly4 target) :
    Nonempty (PositiveRawRegularRootCertificate4 target) := by
  obtain ⟨rootPolynomial, _hDegree, hCongruence⟩ := hCubic
  have hSquare :
      cubicMinpolyRoot4 target rootPolynomial *
        cubicMinpolyRoot4 target rootPolynomial = target :=
    cubicMinpolyRoot4_square hCongruence
  refine ⟨⟨cubicMinpolyRoot4 target rootPolynomial, hSquare, ?_⟩⟩
  unfold cubicMinpolyRoot4
  exact polynomialSquareRoot_sylvester_bijective rootPolynomial hSquare
    (positiveRealSplitCharpoly_isUnit hSpectrum)

private theorem singleQuarticRegularRootCertificate_nonempty
    {target : Matrix4}
    (hQuartic : HasPositiveSingleEigenvalueQuarticRelation4 target) :
    Nonempty (PositiveRawRegularRootCertificate4 target) := by
  obtain ⟨eigenvalue, hFourth⟩ := hQuartic
  let data := positiveSingleEigenvalueQuarticData4 target eigenvalue hFourth
  refine ⟨⟨positiveSingleEigenvalueQuarticRoot4 target eigenvalue hFourth,
    positiveSingleEigenvalueQuarticRoot4_square target eigenvalue hFourth, ?_⟩⟩
  change Function.Bijective (fun variation =>
    sylvesterOperator (positiveSingleEigenvalueJordanRoot data) variation)
  have hFunctions :
      (fun variation =>
        sylvesterOperator (positiveSingleEigenvalueJordanRoot data) variation) =
        positiveSingleEigenvalueSylvester data := by
    funext variation
    rfl
  rw [hFunctions]
  exact positiveSingleEigenvalueSylvester_bijective data

/-- The five-way raw relation partition supplies a regular-root certificate. -/
theorem positiveRawRegularRootCertificate_nonempty
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Nonempty (PositiveRawRegularRootCertificate4 target) := by
  rcases positiveRealSplitCharpoly_relationPartition hSpectrum with
    hQuartic | hDoubleDouble | hTripleSingle | hDoubleSingleSingle | hFourSimple
  · exact singleQuarticRegularRootCertificate_nonempty hQuartic
  · exact cubicMinpolyRegularRootCertificate_nonempty hSpectrum
      (positiveDistinctDoubleDoubleRelation_hasCubicMinpolyRoot hDoubleDouble)
  · exact cubicMinpolyRegularRootCertificate_nonempty hSpectrum
      (positiveDistinctTripleSingleRelation_hasCubicMinpolyRoot hTripleSingle)
  · exact cubicMinpolyRegularRootCertificate_nonempty hSpectrum
      (positiveDistinctDoubleSingleSingleRelation_hasCubicMinpolyRoot
        hDoubleSingleSingle)
  · exact cubicMinpolyRegularRootCertificate_nonempty hSpectrum
      (positiveFourSimpleRelation_hasCubicMinpolyRoot hFourSimple)

/-- The root selected directly from the five-way raw relation partition. -/
def positiveRawRegularRootCertificate
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    PositiveRawRegularRootCertificate4 target :=
  Classical.choice
    (positiveRawRegularRootCertificate_nonempty target hSpectrum)

def positiveRawRegularRoot
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) : Matrix4 :=
  (positiveRawRegularRootCertificate target hSpectrum).root

theorem positiveRawRegularRoot_square
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    positiveRawRegularRoot target hSpectrum *
        positiveRawRegularRoot target hSpectrum = target :=
  (positiveRawRegularRootCertificate target hSpectrum).square

theorem positiveRawRegularRoot_sylvester_bijective
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Function.Bijective
      (sylvesterOperator (positiveRawRegularRoot target hSpectrum)) :=
  (positiveRawRegularRootCertificate target hSpectrum).sylvesterBijective

/-- Unconditional Sylvester-regular square-root closure of the positive real
split raw locus. -/
theorem positiveRealSplitCharpoly_hasSylvesterRegularRealSquareRoot
    {target : Matrix4} (hSpectrum : PositiveRealSplitCharpoly4 target) :
    HasSylvesterRegularRealSquareRoot target :=
  ⟨positiveRawRegularRoot target hSpectrum,
    positiveRawRegularRoot_square target hSpectrum,
    positiveRawRegularRoot_sylvester_bijective target hSpectrum⟩

/-- Universal regular-root closure, with no Jordan-basis residual. -/
theorem positiveRawSylvesterRegularRootClosure :
    ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
      HasSylvesterRegularRealSquareRoot target := by
  intro target hSpectrum
  exact positiveRealSplitCharpoly_hasSylvesterRegularRealSquareRoot hSpectrum

end

end P0EFTJanusPositiveRawSplitCharpolySylvesterClosure4D
end JanusFormal
