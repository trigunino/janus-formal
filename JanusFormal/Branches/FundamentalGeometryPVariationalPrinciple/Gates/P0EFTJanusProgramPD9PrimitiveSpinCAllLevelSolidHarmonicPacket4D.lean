import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCThirdPositiveSphereDirac4D
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# All-level solid harmonic packet for the primitive SpinC tower

The concrete levels `p = 1, 2, 3` exhibit the same trace-free mechanism.
This file replaces further level-by-level expansions by one algebraic
construction.  For every complex parameter `t`, the vector

`(1 - t², I(1 + t²), 2t)`

is null for the complexified Euclidean quadratic form.  Consequently every
power of its linear form is a homogeneous solid harmonic, at arbitrary
degree.  The remaining bridge restricts a basis of these polynomials to the
physical sphere and transports the spherical Laplacian identity through the
already proved scalar Lichnerowicz interface.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D

set_option autoImplicit false

noncomputable section

open Complex
open Finset
open MvPolynomial
open P0EFTJanusPrimitiveMonopoleZ4Spectrum

/-- Complex homogeneous polynomials in the three ambient sphere
coordinates. -/
abbrev PrimitiveSpinCSolidPolynomial :=
  MvPolynomial (Fin 3) Complex

/-- The rational null curve generating all complex spherical harmonics. -/
def primitiveSpinCSolidNullVector (parameter : Complex) : Fin 3 → Complex :=
  ![1 - parameter ^ 2, Complex.I * (1 + parameter ^ 2), 2 * parameter]

/-- The generating vector is null for every complex parameter. -/
theorem primitiveSpinCSolidNullVector_sq_sum
    (parameter : Complex) :
    ∑ coordinate : Fin 3,
        primitiveSpinCSolidNullVector parameter coordinate ^ 2 = 0 := by
  simp [primitiveSpinCSolidNullVector, Fin.sum_univ_succ]
  ring_nf
  simp [Complex.I_sq]

/-- Linear solid-harmonic generator attached to one point of the null
curve. -/
def primitiveSpinCSolidNullLinearForm (parameter : Complex) :
    PrimitiveSpinCSolidPolynomial :=
  ∑ coordinate : Fin 3,
    C (primitiveSpinCSolidNullVector parameter coordinate) * X coordinate

@[simp]
theorem primitiveSpinCSolidNullLinearForm_pderiv
    (parameter : Complex) (coordinate : Fin 3) :
    pderiv coordinate
        (primitiveSpinCSolidNullLinearForm parameter) =
      C (primitiveSpinCSolidNullVector parameter coordinate) := by
  classical
  simp [primitiveSpinCSolidNullLinearForm, Pi.single_apply]

/-- The null linear generator is homogeneous of degree one. -/
theorem primitiveSpinCSolidNullLinearForm_isHomogeneous
    (parameter : Complex) :
    (primitiveSpinCSolidNullLinearForm parameter).IsHomogeneous 1 := by
  classical
  unfold primitiveSpinCSolidNullLinearForm
  apply MvPolynomial.IsHomogeneous.sum
  intro coordinate _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- Ambient complex Laplacian on three-variable solid polynomials. -/
def primitiveSpinCSolidLaplacian
    (polynomial : PrimitiveSpinCSolidPolynomial) :
    PrimitiveSpinCSolidPolynomial :=
  ∑ coordinate : Fin 3,
    pderiv coordinate (pderiv coordinate polynomial)

private theorem primitiveSpinCSolidNullLinearForm_pderiv_sq_pow
    (degree : Nat) (parameter : Complex) (coordinate : Fin 3) :
    pderiv coordinate
        (pderiv coordinate
          (primitiveSpinCSolidNullLinearForm parameter ^ degree)) =
      C ((degree * (degree - 1) : Nat) : Complex) *
          primitiveSpinCSolidNullLinearForm parameter ^ (degree - 2) *
        C (primitiveSpinCSolidNullVector parameter coordinate ^ 2) := by
  rcases degree with _ | _ | degree
  · simp
  · simp
  · simp [primitiveSpinCSolidNullLinearForm_pderiv]
    ring_nf

/-- Every degree of the null generating family is a solid harmonic. -/
theorem primitiveSpinCSolidNullLinearForm_pow_laplacian
    (degree : Nat) (parameter : Complex) :
    primitiveSpinCSolidLaplacian
        (primitiveSpinCSolidNullLinearForm parameter ^ degree) = 0 := by
  classical
  unfold primitiveSpinCSolidLaplacian
  simp_rw [primitiveSpinCSolidNullLinearForm_pderiv_sq_pow]
  rw [← Finset.mul_sum]
  simp_rw [← map_sum]
  rw [primitiveSpinCSolidNullVector_sq_sum]
  simp

/-- Evaluation in the complex null coordinates `u = 1`, `v = 0`,
`z = X`.  It exposes the powers `parameter^r` for `r ≤ degree`. -/
def primitiveSpinCSolidLowMomentEvaluation :
    PrimitiveSpinCSolidPolynomial →+* Polynomial Complex :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.C (1 / 2),
      Polynomial.C (-Complex.I / 2),
      Polynomial.X]

/-- Evaluation in the complementary null coordinates `u = 0`, `v = -1`,
`z = X`.  It exposes the remaining powers up to `2 * degree`. -/
def primitiveSpinCSolidHighMomentEvaluation :
    PrimitiveSpinCSolidPolynomial →+* Polynomial Complex :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![Polynomial.C (-1 / 2),
      Polynomial.C (-Complex.I / 2),
      Polynomial.X]

@[simp]
theorem primitiveSpinCSolidLowMomentEvaluation_linearForm
    (parameter : Complex) :
    primitiveSpinCSolidLowMomentEvaluation
        (primitiveSpinCSolidNullLinearForm parameter) =
      1 + Polynomial.C (2 * parameter) * Polynomial.X := by
  simp [primitiveSpinCSolidLowMomentEvaluation,
    primitiveSpinCSolidNullLinearForm,
    primitiveSpinCSolidNullVector, Fin.sum_univ_succ]
  ext coefficient
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

@[simp]
theorem primitiveSpinCSolidHighMomentEvaluation_linearForm
    (parameter : Complex) :
    primitiveSpinCSolidHighMomentEvaluation
        (primitiveSpinCSolidNullLinearForm parameter) =
      Polynomial.C (parameter ^ 2) +
        Polynomial.C (2 * parameter) * Polynomial.X := by
  simp [primitiveSpinCSolidHighMomentEvaluation,
    primitiveSpinCSolidNullLinearForm,
    primitiveSpinCSolidNullVector, Fin.sum_univ_succ]
  ext coefficient
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem polynomial_coeff_const_add_linear_pow
    (constant linear : Complex) (degree coefficient : Nat)
    (hCoefficient : coefficient ≤ degree) :
    ((Polynomial.C constant +
          Polynomial.C linear * Polynomial.X) ^ degree).coeff coefficient =
      degree.choose coefficient *
        constant ^ (degree - coefficient) * linear ^ coefficient := by
  have hTerm (other : Nat) :
      (Polynomial.C linear * Polynomial.X) ^ other *
            Polynomial.C constant ^ (degree - other) *
          (degree.choose other : Polynomial Complex) =
        Polynomial.C
            ((degree.choose other : Complex) *
              constant ^ (degree - other) * linear ^ other) *
          Polynomial.X ^ other := by
    rw [mul_pow, ← Polynomial.C_pow, ← Polynomial.C_pow]
    rw [← Polynomial.C_eq_natCast]
    simp only [map_mul]
    ring
  rw [add_comm, (Commute.all _ _).add_pow]
  simp_rw [hTerm]
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  rw [Finset.sum_eq_single coefficient]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro other hOtherRange hOther
    rw [Polynomial.coeff_C_mul_X_pow]
    simp [Ne.symm hOther]
  · simp [hCoefficient]

/-- The `2p + 1` distinct rational parameters used at degree `p`. -/
def primitiveSpinCSolidPacketParameter (degree : Nat)
    (multiplicity : Fin (2 * degree + 1)) : Complex :=
  multiplicity.val

theorem primitiveSpinCSolidPacketParameter_injective (degree : Nat) :
    Function.Injective (primitiveSpinCSolidPacketParameter degree) := by
  intro first second hEqual
  apply Fin.ext
  change (first.val : Complex) = second.val at hEqual
  exact_mod_cast hEqual

/-- Uniform degree-`p` packet generated by the rational null curve. -/
def primitiveSpinCSolidHarmonicPacket (degree : Nat)
    (multiplicity : Fin (2 * degree + 1)) :
    PrimitiveSpinCSolidPolynomial :=
  primitiveSpinCSolidNullLinearForm
      (primitiveSpinCSolidPacketParameter degree multiplicity) ^ degree

/-- Every member of the uniform packet is ambient harmonic. -/
@[simp]
theorem primitiveSpinCSolidHarmonicPacket_laplacian
    (degree : Nat) (multiplicity : Fin (2 * degree + 1)) :
    primitiveSpinCSolidLaplacian
        (primitiveSpinCSolidHarmonicPacket degree multiplicity) = 0 :=
  primitiveSpinCSolidNullLinearForm_pow_laplacian degree
    (primitiveSpinCSolidPacketParameter degree multiplicity)

/-- Every packet member is homogeneous of the claimed arbitrary degree. -/
theorem primitiveSpinCSolidHarmonicPacket_isHomogeneous
    (degree : Nat) (multiplicity : Fin (2 * degree + 1)) :
    (primitiveSpinCSolidHarmonicPacket degree multiplicity).IsHomogeneous
      degree := by
  unfold primitiveSpinCSolidHarmonicPacket
  simpa using
    (primitiveSpinCSolidNullLinearForm_isHomogeneous
      (primitiveSpinCSolidPacketParameter degree multiplicity)).pow degree

/-- Euler operator on ambient solid polynomials. -/
def primitiveSpinCSolidEuler
    (polynomial : PrimitiveSpinCSolidPolynomial) :
    PrimitiveSpinCSolidPolynomial :=
  ∑ coordinate : Fin 3,
    X coordinate * pderiv coordinate polynomial

theorem primitiveSpinCSolidEuler_smul
    (scalar : Complex) (polynomial : PrimitiveSpinCSolidPolynomial) :
    primitiveSpinCSolidEuler (scalar • polynomial) =
      scalar • primitiveSpinCSolidEuler polynomial := by
  classical
  unfold primitiveSpinCSolidEuler
  calc
    ∑ coordinate : Fin 3,
        X coordinate * pderiv coordinate (scalar • polynomial) =
        ∑ coordinate : Fin 3,
          scalar • (X coordinate * pderiv coordinate polynomial) := by
            apply Finset.sum_congr rfl
            intro coordinate _
            rw [(pderiv coordinate).map_smul]
            simp [MvPolynomial.smul_eq_C_mul]
            ring
    _ = _ := by
      exact (Finset.smul_sum
        (r := scalar)
        (f := fun coordinate : Fin 3 =>
          X coordinate * pderiv coordinate polynomial)
        (s := Finset.univ)).symm

/-- Euler's identity on every member of the arbitrary-degree packet. -/
theorem primitiveSpinCSolidEuler_packet
    (degree : Nat) (multiplicity : Fin (2 * degree + 1)) :
    primitiveSpinCSolidEuler
        (primitiveSpinCSolidHarmonicPacket degree multiplicity) =
      (degree : Complex) •
        primitiveSpinCSolidHarmonicPacket degree multiplicity := by
  unfold primitiveSpinCSolidEuler
  have hEuler :=
    (primitiveSpinCSolidHarmonicPacket_isHomogeneous
      degree multiplicity).sum_X_mul_pderiv
  rw [hEuler, nsmul_eq_mul, ← MvPolynomial.C_eq_coe_nat,
    MvPolynomial.C_mul']

/-- Squared ambient radius polynomial. -/
def primitiveSpinCSolidRadiusSquared :
    PrimitiveSpinCSolidPolynomial :=
  ∑ coordinate : Fin 3, X coordinate ^ 2

/-- Algebraic positive spherical Laplacian written in ambient polar form:
`E(E+1) - r² Δ`. -/
def primitiveSpinCSolidSpherePositiveLaplacian
    (polynomial : PrimitiveSpinCSolidPolynomial) :
    PrimitiveSpinCSolidPolynomial :=
  primitiveSpinCSolidEuler (primitiveSpinCSolidEuler polynomial) +
    primitiveSpinCSolidEuler polynomial -
      primitiveSpinCSolidRadiusSquared *
        primitiveSpinCSolidLaplacian polynomial

/-- Every degree-`p` member has the exact spherical energy `p(p+1)`.
This is the all-level algebraic solid-to-sphere spectral identity. -/
theorem primitiveSpinCSolidSpherePositiveLaplacian_packet
    (degree : Nat) (multiplicity : Fin (2 * degree + 1)) :
    primitiveSpinCSolidSpherePositiveLaplacian
        (primitiveSpinCSolidHarmonicPacket degree multiplicity) =
      ((degree : Complex) * ((degree : Complex) + 1)) •
        primitiveSpinCSolidHarmonicPacket degree multiplicity := by
  unfold primitiveSpinCSolidSpherePositiveLaplacian
  rw [primitiveSpinCSolidEuler_packet,
    primitiveSpinCSolidEuler_smul,
    primitiveSpinCSolidEuler_packet,
    primitiveSpinCSolidHarmonicPacket_laplacian]
  simp only [mul_zero, sub_zero, smul_smul]
  rw [← add_smul]
  congr 1
  ring

/-- Evaluate an ambient polynomial on the same rational null curve, with
the curve parameter promoted to the polynomial variable. -/
def primitiveSpinCSolidNullCurveEvaluation :
    PrimitiveSpinCSolidPolynomial →+* Polynomial Complex :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![1 - Polynomial.X ^ 2,
      Polynomial.C Complex.I * (1 + Polynomial.X ^ 2),
      2 * Polynomial.X]

@[simp]
theorem primitiveSpinCSolidNullCurveEvaluation_smul
    (scalar : Complex) (polynomial : PrimitiveSpinCSolidPolynomial) :
    primitiveSpinCSolidNullCurveEvaluation (scalar • polynomial) =
      Polynomial.C scalar *
        primitiveSpinCSolidNullCurveEvaluation polynomial := by
  unfold primitiveSpinCSolidNullCurveEvaluation
  rw [MvPolynomial.eval₂Hom_smul]
  simp [smul_eq_mul]

@[simp]
theorem primitiveSpinCSolidNullCurveEvaluation_linearForm
    (parameter : Complex) :
    primitiveSpinCSolidNullCurveEvaluation
        (primitiveSpinCSolidNullLinearForm parameter) =
      Polynomial.C (-2) *
        (Polynomial.C parameter - Polynomial.X) ^ 2 := by
  have hI :
      Polynomial.C Complex.I ^ 2 =
        (-1 : Polynomial Complex) := by
    rw [← Polynomial.C_pow, Complex.I_sq]
    simp
  have hTwo :
      Polynomial.C (2 : Complex) =
        (2 : Polynomial Complex) :=
    Polynomial.C_eq_natCast 2
  simp [primitiveSpinCSolidNullCurveEvaluation,
    primitiveSpinCSolidNullLinearForm,
    primitiveSpinCSolidNullVector, Fin.sum_univ_succ]
  ring_nf
  rw [hI, hTwo]
  ring

/-- Evaluation turns the degree-`p` packet into translated powers of one
variable of degree `2p`. -/
@[simp]
theorem primitiveSpinCSolidNullCurveEvaluation_packet
    (degree : Nat) (multiplicity : Fin (2 * degree + 1)) :
    primitiveSpinCSolidNullCurveEvaluation
        (primitiveSpinCSolidHarmonicPacket degree multiplicity) =
      Polynomial.C ((-2 : Complex) ^ degree) *
        (Polynomial.C
            (primitiveSpinCSolidPacketParameter degree multiplicity) -
          Polynomial.X) ^ (2 * degree) := by
  rw [primitiveSpinCSolidHarmonicPacket, map_pow,
    primitiveSpinCSolidNullCurveEvaluation_linearForm, mul_pow,
    ← Polynomial.C_pow, pow_mul]

/-- The nonzero scalar multiplying the `r`-th Vandermonde moment. -/
def primitiveSpinCSolidMomentFactor (degree : Nat)
    (moment : Fin (2 * degree + 1)) : Complex :=
  (-2 : Complex) ^ degree *
    (2 * degree).choose (2 * degree - moment.val) *
      (-1 : Complex) ^ (2 * degree - moment.val)

theorem primitiveSpinCSolidMomentFactor_ne_zero (degree : Nat)
    (moment : Fin (2 * degree + 1)) :
    primitiveSpinCSolidMomentFactor degree moment ≠ 0 := by
  unfold primitiveSpinCSolidMomentFactor
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact_mod_cast
        (Nat.choose_pos (Nat.sub_le (2 * degree) moment.val)).ne'
  · exact pow_ne_zero _ (by norm_num)

/-- Coefficient extraction on the null curve recovers every moment from
`0` through `2p`. -/
theorem primitiveSpinCSolidNullCurveEvaluation_packet_coeff
    (degree : Nat) (multiplicity moment : Fin (2 * degree + 1)) :
    (primitiveSpinCSolidNullCurveEvaluation
        (primitiveSpinCSolidHarmonicPacket degree multiplicity)).coeff
          (2 * degree - moment.val) =
      primitiveSpinCSolidMomentFactor degree moment *
        primitiveSpinCSolidPacketParameter degree multiplicity ^
          moment.val := by
  have hMoment : moment.val ≤ 2 * degree := by omega
  rw [primitiveSpinCSolidNullCurveEvaluation_packet,
    Polynomial.coeff_C_mul]
  have hLinear :
      Polynomial.C
          (primitiveSpinCSolidPacketParameter degree multiplicity) -
          Polynomial.X =
          Polynomial.C
            (primitiveSpinCSolidPacketParameter degree multiplicity) +
          Polynomial.C (-1) * Polynomial.X := by
    rw [show Polynomial.C (-1 : Complex) =
        (-1 : Polynomial Complex) by simp]
    ring
  rw [hLinear,
    polynomial_coeff_const_add_linear_pow _ _ _ _
      (Nat.sub_le (2 * degree) moment.val)]
  unfold primitiveSpinCSolidMomentFactor
  rw [Nat.sub_sub_self hMoment]
  ring

/-- The uniform degree-`p` packet has the exact complex multiplicity
`2p + 1`.  The proof is a Vandermonde argument on all moments exposed by
the rational null curve. -/
theorem primitiveSpinCSolidHarmonicPacket_linearIndependent
    (degree : Nat) :
    LinearIndependent Complex
      (primitiveSpinCSolidHarmonicPacket degree) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients hSum multiplicity
  have hMoments (moment : Fin (2 * degree + 1)) :
      ∑ basis : Fin (2 * degree + 1),
          coefficients basis *
            primitiveSpinCSolidPacketParameter degree basis ^
              moment.val = 0 := by
    have hCoefficient :=
      congrArg
        (fun polynomial : PrimitiveSpinCSolidPolynomial =>
          (primitiveSpinCSolidNullCurveEvaluation polynomial).coeff
            (2 * degree - moment.val))
        hSum
    simp only [map_sum, map_zero, Polynomial.coeff_zero] at hCoefficient
    rw [← Polynomial.lcoeff_apply, map_sum] at hCoefficient
    simp only [Polynomial.lcoeff_apply,
      primitiveSpinCSolidNullCurveEvaluation_smul,
      Polynomial.coeff_C_mul,
      primitiveSpinCSolidNullCurveEvaluation_packet_coeff] at hCoefficient
    have hFactored :
        primitiveSpinCSolidMomentFactor degree moment *
            (∑ basis : Fin (2 * degree + 1),
              coefficients basis *
                primitiveSpinCSolidPacketParameter degree basis ^
                  moment.val) = 0 := by
      rw [Finset.mul_sum]
      calc
        ∑ basis : Fin (2 * degree + 1),
            primitiveSpinCSolidMomentFactor degree moment *
              (coefficients basis *
                primitiveSpinCSolidPacketParameter degree basis ^
                  moment.val) =
            ∑ basis : Fin (2 * degree + 1),
              coefficients basis *
                (primitiveSpinCSolidMomentFactor degree moment *
                  primitiveSpinCSolidPacketParameter degree basis ^
                    moment.val) := by
              apply Finset.sum_congr rfl
              intro basis _
              ring
        _ = 0 := hCoefficient
    exact (mul_eq_zero.mp hFactored).resolve_left
      (primitiveSpinCSolidMomentFactor_ne_zero degree moment)
  have hCoefficients : coefficients = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (primitiveSpinCSolidPacketParameter_injective degree) hMoments
  exact congrFun hCoefficients multiplicity

/-- The physical primitive-monopole multiplicity is definitionally the
same cardinal `2p + 1` used by the solid packet. -/
theorem primitiveSpinCSolidPacket_degeneracy_eq (degree : Nat) :
    primitiveSphereModeDegeneracy degree = 2 * degree + 1 := by
  unfold primitiveSphereModeDegeneracy
  omega

/-- Reindex the solid packet by the repository's physical multiplicity. -/
def primitiveSpinCSolidHarmonicGeometricPacket (degree : Nat)
    (multiplicity : Fin (primitiveSphereModeDegeneracy degree)) :
    PrimitiveSpinCSolidPolynomial :=
  primitiveSpinCSolidHarmonicPacket degree
    (Fin.cast (primitiveSpinCSolidPacket_degeneracy_eq degree) multiplicity)

theorem primitiveSpinCSolidHarmonicGeometricPacket_linearIndependent
    (degree : Nat) :
    LinearIndependent Complex
      (primitiveSpinCSolidHarmonicGeometricPacket degree) := by
  exact
    (primitiveSpinCSolidHarmonicPacket_linearIndependent degree).comp
      (Fin.cast (primitiveSpinCSolidPacket_degeneracy_eq degree))
      (Fin.cast_injective _)

/-- Consolidated all-level algebraic certificate: exact physical
multiplicity, homogeneity, ambient harmonicity and spherical energy. -/
structure PrimitiveSpinCAllLevelSolidHarmonicPacketCertificate4D
    (degree : Nat) where
  homogeneous :
    ∀ multiplicity : Fin (primitiveSphereModeDegeneracy degree),
      (primitiveSpinCSolidHarmonicGeometricPacket
        degree multiplicity).IsHomogeneous degree
  ambientHarmonic :
    ∀ multiplicity : Fin (primitiveSphereModeDegeneracy degree),
      primitiveSpinCSolidLaplacian
        (primitiveSpinCSolidHarmonicGeometricPacket
          degree multiplicity) = 0
  sphereEnergy :
    ∀ multiplicity : Fin (primitiveSphereModeDegeneracy degree),
      primitiveSpinCSolidSpherePositiveLaplacian
          (primitiveSpinCSolidHarmonicGeometricPacket
            degree multiplicity) =
        ((degree : Complex) * ((degree : Complex) + 1)) •
          primitiveSpinCSolidHarmonicGeometricPacket
            degree multiplicity
  linearIndependent :
    LinearIndependent Complex
      (primitiveSpinCSolidHarmonicGeometricPacket degree)

/-- Canonical certificate at every degree, with no level-by-level input. -/
def primitiveSpinCAllLevelSolidHarmonicPacketCertificate4D
    (degree : Nat) :
    PrimitiveSpinCAllLevelSolidHarmonicPacketCertificate4D degree where
  homogeneous := fun multiplicity =>
    primitiveSpinCSolidHarmonicPacket_isHomogeneous degree
      (Fin.cast
        (primitiveSpinCSolidPacket_degeneracy_eq degree) multiplicity)
  ambientHarmonic := fun multiplicity =>
    primitiveSpinCSolidHarmonicPacket_laplacian degree
      (Fin.cast
        (primitiveSpinCSolidPacket_degeneracy_eq degree) multiplicity)
  sphereEnergy := fun multiplicity =>
    primitiveSpinCSolidSpherePositiveLaplacian_packet degree
      (Fin.cast
        (primitiveSpinCSolidPacket_degeneracy_eq degree) multiplicity)
  linearIndependent :=
    primitiveSpinCSolidHarmonicGeometricPacket_linearIndependent degree

end
end P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
end JanusFormal
