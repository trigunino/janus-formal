import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D

/-!
# All-level signed geometric SpinC realization

The null-harmonic tower already supplies the two genuine first-order Dirac
eigensections at every positive sphere level.  This module identifies them
with the independent signed labels of the completed coefficient spectrum and
orientation-corrects the undoubled zero tower for either sign of the period.
It also specializes the existing block theorem saying that the two signed
branches are disjoint and exhaust the scalar/gradient seed block.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSignedGeometricRealization4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

/-- The already constructed all-level first-order seed attached to a signed
nonzero coefficient label. -/
def primitiveSpinCAllLevelSignedGeometricSeed
    (mode : PrimitiveSpinCGeometricSignedNonzeroMode) :
    PrimitiveSpinCHarmonicDiracSeed4D
      period hPeriod mode.2.level mode.1 mode.2.circleMode :=
  (primitiveSpinCAllLevelNullHarmonicDiracSeedTower period hPeriod).seed
    mode.2.level mode.2.multiplicity mode.1 mode.2.circleMode

/-- Genuine smooth eigensection selected by the internal Dirac branch. -/
def primitiveSpinCAllLevelSignedGeometricSection
    (mode : PrimitiveSpinCGeometricSignedNonzeroMode) :
    SmoothSection period hPeriod :=
  match mode.2.branch with
  | .positive =>
      (primitiveSpinCAllLevelSignedGeometricSeed
        period hPeriod mode).positiveSection
  | .negative =>
      (primitiveSpinCAllLevelSignedGeometricSeed
        period hPeriod mode).negativeSection

/-- The positive frequency used by the signed coefficient model is exactly
the frequency of the geometric harmonic diagonalization at every level. -/
theorem primitiveSpinCAllLevelSignedGeometricFrequency_eq
    (mode : PrimitiveSpinCGeometricSignedNonzeroMode) :
    primitiveSpinCGeometricSignedNonzeroFrequency period hPeriod mode =
      primitiveSpinCHarmonicDiracFrequency
        period mode.2.level mode.1 mode.2.circleMode := by
  rcases mode with ⟨sector, ⟨branch, level, multiplicity, circleMode⟩⟩
  unfold primitiveSpinCGeometricSignedNonzeroFrequency
    primitiveSpinCGeometricSignedNonzeroModeToFullMode
    primitiveSpinCSignedNonzeroModeToFullMode
  change
    Real.sqrt
        (primitiveSpinCGeometricSquaredEigenvalue period hPeriod
          (primitiveSpinCHarmonicGeometricMode
            level multiplicity sector circleMode)) =
      primitiveSpinCHarmonicDiracFrequency
        period level sector circleMode
  rw [← primitiveSpinCHarmonicDiracFrequency_sq_eq_geometricSpectrum
    period hPeriod level multiplicity sector circleMode]
  exact Real.sqrt_sq
    (le_of_lt
      (primitiveSpinCHarmonicDiracFrequency_pos
        period level sector circleMode))

/-- Every positive-level signed coefficient label is realized by a genuine
smooth eigensection of the intrinsic geometric Dirac operator. -/
theorem primitiveSpinCAllLevelSignedGeometricSection_eigen
    (mode : PrimitiveSpinCGeometricSignedNonzeroMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCAllLevelSignedGeometricSection
          period hPeriod mode) =
      primitiveSpinCGeometricSignedNonzeroEigenvalue
          period hPeriod mode •
        primitiveSpinCAllLevelSignedGeometricSection
          period hPeriod mode := by
  rcases mode with ⟨sector, ⟨branch, level, multiplicity, circleMode⟩⟩
  cases branch with
  | positive =>
      simpa [primitiveSpinCAllLevelSignedGeometricSection,
        primitiveSpinCAllLevelSignedGeometricSeed,
        primitiveSpinCGeometricSignedNonzeroEigenvalue,
        primitiveSpinCDiracBranchSign,
        primitiveSpinCAllLevelSignedGeometricFrequency_eq] using
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            level multiplicity sector circleMode).positiveSection_eigen
  | negative =>
      simpa [primitiveSpinCAllLevelSignedGeometricSection,
        primitiveSpinCAllLevelSignedGeometricSeed,
        primitiveSpinCGeometricSignedNonzeroEigenvalue,
        primitiveSpinCDiracBranchSign,
        primitiveSpinCAllLevelSignedGeometricFrequency_eq] using
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            level multiplicity sector circleMode).negativeSection_eigen

/-! ## The undoubled zero tower -/

/-- Zero-sphere signed labels, retaining the external normal-root sector. -/
abbrev PrimitiveSpinCGeometricSignedZeroMode :=
  NormalRootChoice × PrimitiveSpinCUnsignedZeroMode

/-- The geometric zero mode which realizes a coefficient label.  Reversing
the oriented period reverses the Fourier sign; for positive period the PT
mode involution compensates the sign in the geometric zero-mode equation. -/
def primitiveSpinCGeometricSignedZeroSource
    (mode : PrimitiveSpinCGeometricSignedZeroMode) :
    NormalRootChoice × Int :=
  if 0 < period then
    (oppositeRoot mode.1, -mode.2.2)
  else
    (mode.1, mode.2.2)

/-- Genuine smooth geometric representative of one undoubled signed zero
mode. -/
def primitiveSpinCGeometricSignedZeroSection
    (mode : PrimitiveSpinCGeometricSignedZeroMode) :
    SmoothSection period hPeriod :=
  primitiveSpinCHopfZeroModeSection
    period hPeriod
    (primitiveSpinCGeometricSignedZeroSource period mode).1
    (primitiveSpinCGeometricSignedZeroSource period mode).2

private theorem normalRootModeNumerator_opposite_neg
    (sector : NormalRootChoice) (circleMode : Int) :
    normalRootModeNumerator (oppositeRoot sector) (-circleMode) =
      -normalRootModeNumerator sector circleMode := by
  cases sector <;>
    simp [oppositeRoot, normalRootModeNumerator] <;> ring

/-- The orientation-corrected geometric zero frequency is exactly the
coefficient eigenvalue, for either sign of the nonzero period. -/
theorem primitiveSpinCGeometricSignedZeroActualEigenvalue_eq
    (mode : PrimitiveSpinCGeometricSignedZeroMode) :
    -normalRootLeviCivitaCorrectedFrequency period
        (primitiveSpinCGeometricSignedZeroSource period mode).1
        (primitiveSpinCGeometricSignedZeroSource period mode).2 =
      primitiveSpinCGeometricSignedEigenvalue period hPeriod
        (mode.1, Sum.inl mode.2) := by
  rcases mode with ⟨sector, ⟨multiplicity, circleMode⟩⟩
  rw [normalRootLeviCivitaCorrectedFrequency_eq period hPeriod]
  unfold primitiveSpinCGeometricSignedEigenvalue circleEigenvalue
  change
    -(Real.pi *
          (normalRootModeNumerator
            (primitiveSpinCGeometricSignedZeroSource
              period (sector, (multiplicity, circleMode))).1
            (primitiveSpinCGeometricSignedZeroSource
              period (sector, (multiplicity, circleMode))).2 : Real) /
        (2 * period)) =
      Real.pi * (normalRootModeNumerator sector circleMode : Real) /
        (2 * |period|)
  by_cases hPositive : 0 < period
  · simp only [primitiveSpinCGeometricSignedZeroSource, if_pos hPositive,
      normalRootModeNumerator_opposite_neg, Int.cast_neg]
    rw [abs_of_pos hPositive]
    ring
  · have hNegative : period < 0 := lt_of_le_of_ne
      (le_of_not_gt hPositive) hPeriod
    simp only [primitiveSpinCGeometricSignedZeroSource, if_neg hPositive]
    rw [abs_of_neg hNegative]
    ring

/-- Every signed zero label is realized by a genuine smooth eigensection of
the same intrinsic first-order Dirac operator. -/
theorem primitiveSpinCGeometricSignedZeroSection_eigen
    (mode : PrimitiveSpinCGeometricSignedZeroMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedZeroSection
          period hPeriod mode) =
      primitiveSpinCGeometricSignedEigenvalue period hPeriod
          (mode.1, Sum.inl mode.2) •
        primitiveSpinCGeometricSignedZeroSection
          period hPeriod mode := by
  rw [primitiveSpinCGeometricSignedZeroSection,
    primitiveSpinCHopfZeroModeGeometricDiracOperator_eigen,
    primitiveSpinCGeometricSignedZeroActualEigenvalue_eq]

/-! ## Complete zero-plus-positive signed realization -/

/-- One genuine smooth first-order eigensection for every coefficient label:
the undoubled zero tower and both branches at every positive level. -/
def primitiveSpinCAllLevelSignedGeometricFullSection :
    PrimitiveSpinCGeometricSignedMode →
      SmoothSection period hPeriod
  | (sector, Sum.inl zeroMode) =>
      primitiveSpinCGeometricSignedZeroSection
        period hPeriod (sector, zeroMode)
  | (sector, Sum.inr nonzeroMode) =>
      primitiveSpinCAllLevelSignedGeometricSection
        period hPeriod (sector, nonzeroMode)

/-- The complete geometric family realizes the exact signed coefficient
eigenvalue at every zero and positive label. -/
theorem primitiveSpinCAllLevelSignedGeometricFullSection_eigen
    (mode : PrimitiveSpinCGeometricSignedMode) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCAllLevelSignedGeometricFullSection
          period hPeriod mode) =
      primitiveSpinCGeometricSignedEigenvalue period hPeriod mode •
        primitiveSpinCAllLevelSignedGeometricFullSection
          period hPeriod mode := by
  rcases mode with ⟨sector, mode⟩
  cases mode with
  | inl zeroMode =>
      exact primitiveSpinCGeometricSignedZeroSection_eigen
        period hPeriod (sector, zeroMode)
  | inr nonzeroMode =>
      simpa [primitiveSpinCAllLevelSignedGeometricFullSection,
        primitiveSpinCGeometricSignedEigenvalue,
        primitiveSpinCGeometricSignedNonzeroEigenvalue,
        primitiveSpinCGeometricSignedNonzeroFrequency,
        primitiveSpinCGeometricSignedModeToFullMode,
        primitiveSpinCGeometricSignedNonzeroModeToFullMode,
        primitiveSpinCSignedModeToFullMode] using
        primitiveSpinCAllLevelSignedGeometricSection_eigen
          period hPeriod (sector, nonzeroMode)

/-- The two signed eigenspaces at one complete positive block are disjoint. -/
theorem primitiveSpinCAllLevelSignedGeometricBlocks_disjoint
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    Disjoint
      ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).positiveHarmonicEigenblock
        period hPeriod positiveLevel sector circleMode)
      ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).negativeHarmonicEigenblock
        period hPeriod positiveLevel sector circleMode) :=
  (primitiveSpinCAllLevelNullHarmonicDiracSeedTower period hPeriod
    ).positive_negativeHarmonicEigenblocks_disjoint
      period hPeriod positiveLevel sector circleMode

/-- At one complete positive block the two signed branches exhaust exactly
the scalar and Clifford-gradient seed packet. -/
theorem primitiveSpinCAllLevelSignedGeometricBlocks_exhaust
    (positiveLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int) :
    (primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).positiveHarmonicEigenblock
          period hPeriod positiveLevel sector circleMode ⊔
        (primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).negativeHarmonicEigenblock
          period hPeriod positiveLevel sector circleMode =
      (primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).geometricHarmonicSeedBlock
          period hPeriod positiveLevel sector circleMode :=
  (primitiveSpinCAllLevelNullHarmonicDiracSeedTower period hPeriod
    ).harmonicEigenblocks_sup_eq_seed
      period hPeriod positiveLevel sector circleMode

/-- Assumption-free certificate for the complete positive-level signed
geometric realization. -/
structure ProgramPD9PrimitiveSpinCAllLevelSignedGeometricCertificate4D where
  realizesCompleteSignedSpectrum :
    ∀ mode : PrimitiveSpinCGeometricSignedMode,
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCAllLevelSignedGeometricFullSection
            period hPeriod mode) =
        primitiveSpinCGeometricSignedEigenvalue
            period hPeriod mode •
          primitiveSpinCAllLevelSignedGeometricFullSection
            period hPeriod mode
  realizesSignedSpectrum :
    ∀ mode : PrimitiveSpinCGeometricSignedNonzeroMode,
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCAllLevelSignedGeometricSection
            period hPeriod mode) =
        primitiveSpinCGeometricSignedNonzeroEigenvalue
            period hPeriod mode •
          primitiveSpinCAllLevelSignedGeometricSection
            period hPeriod mode
  signedBlocksDisjoint :
    ∀ positiveLevel sector circleMode,
      Disjoint
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).positiveHarmonicEigenblock
          period hPeriod positiveLevel sector circleMode)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).negativeHarmonicEigenblock
          period hPeriod positiveLevel sector circleMode)
  signedBlocksExhaust :
    ∀ positiveLevel sector circleMode,
      (primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).positiveHarmonicEigenblock
            period hPeriod positiveLevel sector circleMode ⊔
          (primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).negativeHarmonicEigenblock
            period hPeriod positiveLevel sector circleMode =
        (primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).geometricHarmonicSeedBlock
            period hPeriod positiveLevel sector circleMode

def programPD9PrimitiveSpinCAllLevelSignedGeometricCertificate4D :
    ProgramPD9PrimitiveSpinCAllLevelSignedGeometricCertificate4D
      period hPeriod where
  realizesCompleteSignedSpectrum :=
    primitiveSpinCAllLevelSignedGeometricFullSection_eigen period hPeriod
  realizesSignedSpectrum :=
    primitiveSpinCAllLevelSignedGeometricSection_eigen period hPeriod
  signedBlocksDisjoint :=
    primitiveSpinCAllLevelSignedGeometricBlocks_disjoint period hPeriod
  signedBlocksExhaust :=
    primitiveSpinCAllLevelSignedGeometricBlocks_exhaust period hPeriod

theorem primitiveSpinCAllLevelSignedGeometric_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCAllLevelSignedGeometricCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCAllLevelSignedGeometricCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSignedGeometricRealization4D
end JanusFormal
