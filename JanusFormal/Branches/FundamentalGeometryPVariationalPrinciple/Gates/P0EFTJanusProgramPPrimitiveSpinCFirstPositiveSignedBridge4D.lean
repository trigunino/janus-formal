import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingWitnessLocal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexWitnessNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeFourierCoordinates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeMovingLocal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeGeometricFourier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D

/-!
# First geometric realization of the signed primitive SpinC spectrum

The corrected abstract spectrum has an internal Dirac branch independent of
the external PT/root sector.  This gate identifies its first nonzero sphere
level with the six geometric eigensections already constructed on the Hopf
model: three multiplicities for each of the two internal signs.

No exhaustion beyond the constructed first-level seed block is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD7CircleHeatRegulatorBridge
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- A signed nonzero primitive mode together with its genuine normal-root
sector. -/
abbrev PrimitiveSpinCGeometricSignedNonzeroMode :=
  NormalRootChoice × PrimitiveSpinCSignedNonzeroMode

/-- Forget only the internal sign and recover the geometric squared-spectrum
label. -/
def primitiveSpinCGeometricSignedNonzeroModeToFullMode
    (mode : PrimitiveSpinCGeometricSignedNonzeroMode) :
    PrimitiveSpinCGeometricFullMode :=
  (mode.1, primitiveSpinCSignedNonzeroModeToFullMode mode.2)

/-- Positive frequency of a nonzero geometric signed mode. -/
def primitiveSpinCGeometricSignedNonzeroFrequency
    (mode : PrimitiveSpinCGeometricSignedNonzeroMode) : Real :=
  Real.sqrt
    (primitiveSpinCGeometricSquaredEigenvalue period hPeriod
      (primitiveSpinCGeometricSignedNonzeroModeToFullMode mode))

theorem primitiveSpinCGeometricSignedNonzeroFrequency_sq
    (mode : PrimitiveSpinCGeometricSignedNonzeroMode) :
    primitiveSpinCGeometricSignedNonzeroFrequency period hPeriod mode ^ 2 =
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod
        (primitiveSpinCGeometricSignedNonzeroModeToFullMode mode) := by
  exact Real.sq_sqrt
    (primitiveSpinCGeometricSquaredEigenvalue_nonnegative period hPeriod
      (primitiveSpinCGeometricSignedNonzeroModeToFullMode mode))

/-- Corrected first-order geometric value: the root sector and the internal
Dirac sign are independent labels. -/
def primitiveSpinCGeometricSignedNonzeroEigenvalue
    (mode : PrimitiveSpinCGeometricSignedNonzeroMode) : Real :=
  primitiveSpinCDiracBranchSign mode.2.branch *
    primitiveSpinCGeometricSignedNonzeroFrequency period hPeriod mode

theorem primitiveSpinCGeometricSignedNonzeroEigenvalue_sq
    (mode : PrimitiveSpinCGeometricSignedNonzeroMode) :
    primitiveSpinCGeometricSignedNonzeroEigenvalue period hPeriod mode ^ 2 =
      primitiveSpinCGeometricSquaredEigenvalue period hPeriod
        (primitiveSpinCGeometricSignedNonzeroModeToFullMode mode) := by
  rw [primitiveSpinCGeometricSignedNonzeroEigenvalue, mul_pow,
    primitiveSpinCDiracBranchSign_sq, one_mul,
    primitiveSpinCGeometricSignedNonzeroFrequency_sq]

/-- The first nonzero sphere level has exactly the three geometric coordinate
labels already constructed in the Hopf model. -/
def primitiveSpinCFirstSphereSignedNonzeroMode
    (branch : PrimitiveSpinCDiracBranch)
    (coordinate : Fin 3) (circleMode : Int) :
    PrimitiveSpinCSignedNonzeroMode where
  branch := branch
  level := 0
  multiplicity :=
    Fin.cast (by
      norm_num [PrimitiveSpinCSignedNonzeroMultiplicity,
        primitiveSphereModeDegeneracy]) coordinate
  circleMode := circleMode

/-- The corresponding genuinely rooted geometric mode. -/
def primitiveSpinCFirstSphereGeometricSignedMode
    (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice)
    (coordinate : Fin 3) (circleMode : Int) :
    PrimitiveSpinCGeometricSignedNonzeroMode :=
  (sector,
    primitiveSpinCFirstSphereSignedNonzeroMode branch coordinate circleMode)

theorem primitiveSpinCFirstSphereGeometricSignedMode_squaredEigenvalue
    (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice)
    (coordinate : Fin 3) (circleMode : Int) :
    primitiveSpinCGeometricSquaredEigenvalue period hPeriod
        (primitiveSpinCGeometricSignedNonzeroModeToFullMode
          (primitiveSpinCFirstSphereGeometricSignedMode
            branch sector coordinate circleMode)) =
      normalRootLeviCivitaCorrectedFrequency period sector circleMode ^ 2 +
        2 := by
  rw [normalRootLeviCivitaCorrectedFrequency_sq_eq_circle
    period hPeriod sector circleMode]
  norm_num [primitiveSpinCFirstSphereGeometricSignedMode,
    primitiveSpinCFirstSphereSignedNonzeroMode,
    primitiveSpinCGeometricSignedNonzeroModeToFullMode,
    primitiveSpinCSignedNonzeroModeToFullMode,
    primitiveSpinCGeometricSquaredEigenvalue,
    primitiveSpinCFullSphereEigenvalueSquared]
  ring

theorem primitiveSpinCFirstSphereGeometricSignedFrequency_eq
    (branch : PrimitiveSpinCDiracBranch)
    (sector : NormalRootChoice)
    (coordinate : Fin 3) (circleMode : Int) :
    primitiveSpinCGeometricSignedNonzeroFrequency period hPeriod
        (primitiveSpinCFirstSphereGeometricSignedMode
          branch sector coordinate circleMode) =
      primitiveSpinCHopfFirstSphereDiracFrequency
        period sector circleMode := by
  unfold primitiveSpinCGeometricSignedNonzeroFrequency
    primitiveSpinCHopfFirstSphereDiracFrequency
  rw [primitiveSpinCFirstSphereGeometricSignedMode_squaredEigenvalue]

@[simp]
theorem primitiveSpinCFirstSphereGeometricSignedEigenvalue_positive
    (sector : NormalRootChoice)
    (coordinate : Fin 3) (circleMode : Int) :
    primitiveSpinCGeometricSignedNonzeroEigenvalue period hPeriod
        (primitiveSpinCFirstSphereGeometricSignedMode
          .positive sector coordinate circleMode) =
      primitiveSpinCHopfFirstSphereDiracFrequency
        period sector circleMode := by
  rw [primitiveSpinCGeometricSignedNonzeroEigenvalue,
    primitiveSpinCFirstSphereGeometricSignedFrequency_eq]
  norm_num [primitiveSpinCFirstSphereGeometricSignedMode,
    primitiveSpinCFirstSphereSignedNonzeroMode,
    primitiveSpinCDiracBranchSign]

@[simp]
theorem primitiveSpinCFirstSphereGeometricSignedEigenvalue_negative
    (sector : NormalRootChoice)
    (coordinate : Fin 3) (circleMode : Int) :
    primitiveSpinCGeometricSignedNonzeroEigenvalue period hPeriod
        (primitiveSpinCFirstSphereGeometricSignedMode
          .negative sector coordinate circleMode) =
      -primitiveSpinCHopfFirstSphereDiracFrequency
        period sector circleMode := by
  rw [primitiveSpinCGeometricSignedNonzeroEigenvalue,
    primitiveSpinCFirstSphereGeometricSignedFrequency_eq]
  norm_num [primitiveSpinCFirstSphereGeometricSignedMode,
    primitiveSpinCFirstSphereSignedNonzeroMode,
    primitiveSpinCDiracBranchSign]

/-- The positive geometric eigensection realizes the corrected positive
internal branch at the first sphere level. -/
theorem primitiveSpinCHopfFirstSpherePositive_realizes_signedSpectrum
    (sector : NormalRootChoice)
    (coordinate : Fin 3) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector circleMode) =
      primitiveSpinCGeometricSignedNonzeroEigenvalue period hPeriod
          (primitiveSpinCFirstSphereGeometricSignedMode
            .positive sector coordinate circleMode) •
        primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector circleMode := by
  rw [primitiveSpinCHopfFirstSpherePositiveGeometricDiracOperator_eigen,
    primitiveSpinCFirstSphereGeometricSignedEigenvalue_positive]

/-- The companion eigensection realizes the corrected negative internal
branch at the same rooted first sphere level. -/
theorem primitiveSpinCHopfFirstSphereNegative_realizes_signedSpectrum
    (sector : NormalRootChoice)
    (coordinate : Fin 3) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector circleMode) =
      primitiveSpinCGeometricSignedNonzeroEigenvalue period hPeriod
          (primitiveSpinCFirstSphereGeometricSignedMode
            .negative sector coordinate circleMode) •
        primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector circleMode := by
  rw [primitiveSpinCHopfFirstSphereNegativeGeometricDiracOperator_eigen,
    primitiveSpinCFirstSphereGeometricSignedEigenvalue_negative]

end
end P0EFTJanusProgramPPrimitiveSpinCFirstPositiveSignedBridge4D
end JanusFormal
