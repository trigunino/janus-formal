import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRankTwoSpinCHermitianPairing4D

/-! # Classification of rank-two SpinC Hermitian pairings -/

namespace JanusFormal
namespace P0EFTJanusProgramPRankTwoSpinCHermitianClassification4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPRankTwoSpinCHermitianPairing4D
open P0EFTJanusCliffordSpin2DoubleCover

variable (period : Real) (hPeriod : period ≠ 0)

/-- An honest sesquilinear form on the one-dimensional complex spinor
representation. -/
structure ComplexLineSesquilinearForm where
  toFun : Complex → Complex → Complex
  map_add_left : ∀ first second third,
    toFun (first + second) third = toFun first third + toFun second third
  map_add_right : ∀ first second third,
    toFun first (second + third) = toFun first second + toFun first third
  map_smul_left : ∀ scalar first second,
    toFun (scalar * first) second =
      (starRingEnd Complex) scalar * toFun first second
  map_smul_right : ∀ scalar first second,
    toFun first (scalar * second) = scalar * toFun first second

def complexLineSesquilinearNormalForm
    (coefficient first second : Complex) : Complex :=
  (starRingEnd Complex) first * coefficient * second

def canonicalComplexLineSesquilinearForm
    (coefficient : Complex) : ComplexLineSesquilinearForm where
  toFun := complexLineSesquilinearNormalForm coefficient
  map_add_left := by
    intro first second third
    simp [complexLineSesquilinearNormalForm]
    ring
  map_add_right := by
    intro first second third
    simp [complexLineSesquilinearNormalForm]
    ring
  map_smul_left := by
    intro scalar first second
    simp [complexLineSesquilinearNormalForm]
    ring
  map_smul_right := by
    intro scalar first second
    simp [complexLineSesquilinearNormalForm]
    ring

/-- One complex coefficient is the complete classification of sesquilinear
forms on a complex line. -/
theorem complexLineSesquilinearForm_classified
    (form : ComplexLineSesquilinearForm)
    (first second : Complex) :
    form.toFun first second =
      complexLineSesquilinearNormalForm (form.toFun 1 1) first second := by
  calc
    form.toFun first second = form.toFun (first * 1) second := by rw [mul_one]
    _ = (starRingEnd Complex) first * form.toFun 1 second :=
      form.map_smul_left first 1 second
    _ = (starRingEnd Complex) first * form.toFun 1 (second * 1) := by
      rw [mul_one]
    _ = (starRingEnd Complex) first * (second * form.toFun 1 1) := by
      rw [form.map_smul_right second 1 1]
    _ = complexLineSesquilinearNormalForm (form.toFun 1 1) first second := by
      unfold complexLineSesquilinearNormalForm
      ring

theorem complexLineSesquilinearForm_unique_coefficient
    (form : ComplexLineSesquilinearForm) :
    ∃! coefficient : Complex, ∀ first second,
      form.toFun first second =
        complexLineSesquilinearNormalForm coefficient first second := by
  refine ⟨form.toFun 1 1, complexLineSesquilinearForm_classified form, ?_⟩
  intro coefficient hCoefficient
  simpa [complexLineSesquilinearNormalForm] using (hCoefficient 1 1).symm

theorem complexLineSesquilinearNormalForm_eq_coefficient_mul_hermitian
    (coefficient first second : Complex) :
    complexLineSesquilinearNormalForm coefficient first second =
      coefficient * rankTwoSpinorHermitianPairing first second := by
  unfold complexLineSesquilinearNormalForm rankTwoSpinorHermitianPairing
  ring

/-- Every classified form is invariant under the rank-two Clifford SpinC
character; invariance introduces no additional coefficient. -/
theorem complexLineSesquilinearNormalForm_spinC_invariant
    (coefficient : Complex) (element : CliffordSpinC2)
    (first second : Complex) :
    complexLineSesquilinearNormalForm coefficient
        (rankTwoSpinCSpinorAction element first)
        (rankTwoSpinCSpinorAction element second) =
      complexLineSesquilinearNormalForm coefficient first second := by
  rw [complexLineSesquilinearNormalForm_eq_coefficient_mul_hermitian,
    rankTwoSpinorHermitianPairing_invariant,
    complexLineSesquilinearNormalForm_eq_coefficient_mul_hermitian]

structure ProgramPRankTwoSpinCHermitianClassificationCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) where
  pairingCertificate :
    ProgramPRankTwoSpinCHermitianPairingCertificate4D period hPeriod domain
  allFormsClassified :
    ∀ form : ComplexLineSesquilinearForm,
      ∃! coefficient : Complex, ∀ first second,
        form.toFun first second =
          complexLineSesquilinearNormalForm coefficient first second
  allNormalFormsInvariant :
    ∀ coefficient element first second,
      complexLineSesquilinearNormalForm coefficient
          (rankTwoSpinCSpinorAction element first)
          (rankTwoSpinCSpinorAction element second) =
        complexLineSesquilinearNormalForm coefficient first second

def programPRankTwoSpinCHermitianClassificationCertificate4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    ProgramPRankTwoSpinCHermitianClassificationCertificate4D
      period hPeriod domain where
  pairingCertificate :=
    programPRankTwoSpinCHermitianPairingCertificate4D period hPeriod domain
  allFormsClassified := complexLineSesquilinearForm_unique_coefficient
  allNormalFormsInvariant :=
    complexLineSesquilinearNormalForm_spinC_invariant

theorem canonicalProgramPRankTwoSpinCHermitianClassificationCertificate4D_nonempty :
    Nonempty
      (ProgramPRankTwoSpinCHermitianClassificationCertificate4D period hPeriod
        (canonicalProgramPCommonGeometricDomain4D period hPeriod)) :=
  ⟨programPRankTwoSpinCHermitianClassificationCertificate4D period hPeriod _⟩

end
end P0EFTJanusProgramPRankTwoSpinCHermitianClassification4D
end JanusFormal
