import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

/-!
# One-point obstruction for complex first-sphere multiplicity

The equatorial witness at sphere point `(1, 0, 0)` separates the three
constructed first-sphere eigensections over `ℝ`.  It cannot, by itself,
separate the two tangential coordinates over `ℂ`.

Indeed, on the transported Hopf zero-mode witness one has the exact fiber
identity

`Γ₁ ψ = i Γ₂ ψ`.

Consequently the local coordinates of the first and second tangential
first-sphere sections are complex collinear at this witness, for both internal
Dirac signs.  A proof of joint complex independence must therefore use at
least one additional point, derivative, pairing, or other global observable;
the existing one-point real multiplicity argument cannot simply be reused
with complex coefficients.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexWitnessNoGo4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod

/-- Public name for the equatorial cover witness used by the existing real
multiplicity proof. -/
abbrev firstSphereComplexWitnessCover :=
  primitiveSpinCGeometricZeroModeWitnessCover period hPeriod 0

/-- Public name for the corresponding quotient point. -/
abbrev firstSphereComplexWitnessBase :=
  primitiveSpinCGeometricZeroModeWitnessBase period hPeriod 0

/-- Public name for the local SpinC chart selected at the witness. -/
abbrev firstSphereComplexWitnessIndex :=
  primitiveSpinCGeometricZeroModeWitnessIndex period hPeriod 0

/-- The transported normal-root Hopf mode at the one-point witness. -/
def firstSphereComplexWitnessMode
    (sector : NormalRootChoice) (mode : Int) : D9DoubledMatterFiber :=
  primitiveSpinCNormalModeDoubledLift
    period hPeriod sector mode
    (firstSphereComplexWitnessCover period hPeriod)

/-- Explicit half-spinor value of the public witness mode. -/
theorem firstSphereComplexWitnessMode_halfSpinor
    (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (firstSphereComplexWitnessMode period hPeriod sector mode) =
      match sector with
      | .positiveQuarter => (ambientHalfGammaPositiveEigenvector, 0)
      | .negativeQuarter => (0, ambientHalfGammaPositiveEigenvector) := by
  exact witnessMode_halfSpinor period hPeriod sector mode

/-- At the one-point witness the two tangential Clifford directions are
exactly complex collinear. -/
theorem firstSphereComplexWitness_gamma_one_eq_I_gamma_two
    (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberCliffordGamma 1
        ((2 : Real) •
          firstSphereComplexWitnessMode period hPeriod sector mode) =
      d9PrimitiveSpinCComplexActionCLM Complex.I
        (d9DoubledMatterFiberCliffordGamma 2
          ((2 : Real) •
            firstSphereComplexWitnessMode period hPeriod sector mode)) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction, map_smul,
    firstSphereComplexWitnessMode_halfSpinor]
  cases sector <;>
    apply Prod.ext <;> funext index <;> fin_cases index <;>
    norm_num [d9DoubledMatterSpinorCliffordGamma_one,
      d9DoubledMatterSpinorCliffordGamma_two,
      ambientHalfGammaPositiveEigenvector, Complex.real_smul]

/-- Public form of the first tangential positive local-coordinate formula. -/
theorem firstSpherePositiveComplexWitnessLocalCoordinate_one
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (firstSphereComplexWitnessIndex period hPeriod)
        (firstSphereComplexWitnessBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 1 sector mode) =
      d9DoubledMatterFiberCliffordGamma 1
        ((2 : Real) •
          firstSphereComplexWitnessMode period hPeriod sector mode) := by
  simpa [firstSphereComplexWitnessIndex,
    firstSphereComplexWitnessBase, firstSphereComplexWitnessMode,
    firstSphereComplexWitnessCover] using
    (firstSpherePositiveLocalCoordinate_one
      period hPeriod sector mode)

/-- Public form of the second tangential positive local-coordinate formula. -/
theorem firstSpherePositiveComplexWitnessLocalCoordinate_two
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (firstSphereComplexWitnessIndex period hPeriod)
        (firstSphereComplexWitnessBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 2 sector mode) =
      d9DoubledMatterFiberCliffordGamma 2
        ((2 : Real) •
          firstSphereComplexWitnessMode period hPeriod sector mode) := by
  simpa [firstSphereComplexWitnessIndex,
    firstSphereComplexWitnessBase, firstSphereComplexWitnessMode,
    firstSphereComplexWitnessCover] using
    (firstSpherePositiveLocalCoordinate_two
      period hPeriod sector mode)

/-- Public form of the first tangential negative local-coordinate formula. -/
theorem firstSphereNegativeComplexWitnessLocalCoordinate_one
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (firstSphereComplexWitnessIndex period hPeriod)
        (firstSphereComplexWitnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 1 sector mode) =
      d9DoubledMatterFiberCliffordGamma 1
        ((2 : Real) •
          firstSphereComplexWitnessMode period hPeriod sector mode) := by
  simpa [firstSphereComplexWitnessIndex,
    firstSphereComplexWitnessBase, firstSphereComplexWitnessMode,
    firstSphereComplexWitnessCover] using
    (firstSphereNegativeLocalCoordinate_one
      period hPeriod sector mode)

/-- Public form of the second tangential negative local-coordinate formula. -/
theorem firstSphereNegativeComplexWitnessLocalCoordinate_two
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (firstSphereComplexWitnessIndex period hPeriod)
        (firstSphereComplexWitnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 2 sector mode) =
      d9DoubledMatterFiberCliffordGamma 2
        ((2 : Real) •
          firstSphereComplexWitnessMode period hPeriod sector mode) := by
  simpa [firstSphereComplexWitnessIndex,
    firstSphereComplexWitnessBase, firstSphereComplexWitnessMode,
    firstSphereComplexWitnessCover] using
    (firstSphereNegativeLocalCoordinate_two
      period hPeriod sector mode)

/-- The two positive tangential eigensections are complex collinear after
local evaluation at the existing equatorial witness. -/
theorem firstSpherePositiveComplexWitness_tangential_collinear
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (firstSphereComplexWitnessIndex period hPeriod)
        (firstSphereComplexWitnessBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 1 sector mode) =
      d9PrimitiveSpinCComplexActionCLM Complex.I
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (firstSphereComplexWitnessIndex period hPeriod)
          (firstSphereComplexWitnessBase period hPeriod)
          (primitiveSpinCHopfFirstSpherePositiveSection
            period hPeriod 2 sector mode)) := by
  rw [firstSpherePositiveComplexWitnessLocalCoordinate_one,
    firstSpherePositiveComplexWitnessLocalCoordinate_two]
  exact firstSphereComplexWitness_gamma_one_eq_I_gamma_two
    period hPeriod sector mode

/-- The same one-point complex collinearity occurs on the negative internal
Dirac branch. -/
theorem firstSphereNegativeComplexWitness_tangential_collinear
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (firstSphereComplexWitnessIndex period hPeriod)
        (firstSphereComplexWitnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 1 sector mode) =
      d9PrimitiveSpinCComplexActionCLM Complex.I
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (firstSphereComplexWitnessIndex period hPeriod)
          (firstSphereComplexWitnessBase period hPeriod)
          (primitiveSpinCHopfFirstSphereNegativeSection
            period hPeriod 2 sector mode)) := by
  rw [firstSphereNegativeComplexWitnessLocalCoordinate_one,
    firstSphereNegativeComplexWitnessLocalCoordinate_two]
  exact firstSphereComplexWitness_gamma_one_eq_I_gamma_two
    period hPeriod sector mode

/-- Consolidated no-go: the current one-point witness is intrinsically
insufficient for joint complex multiplicity, on both signed branches. -/
theorem firstSphereComplexWitness_onePointNoGo_closed
    (sector : NormalRootChoice) (mode : Int) :
    (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (firstSphereComplexWitnessIndex period hPeriod)
        (firstSphereComplexWitnessBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 1 sector mode) =
      d9PrimitiveSpinCComplexActionCLM Complex.I
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (firstSphereComplexWitnessIndex period hPeriod)
          (firstSphereComplexWitnessBase period hPeriod)
          (primitiveSpinCHopfFirstSpherePositiveSection
            period hPeriod 2 sector mode))) ∧
      (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (firstSphereComplexWitnessIndex period hPeriod)
        (firstSphereComplexWitnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 1 sector mode) =
      d9PrimitiveSpinCComplexActionCLM Complex.I
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (firstSphereComplexWitnessIndex period hPeriod)
          (firstSphereComplexWitnessBase period hPeriod)
          (primitiveSpinCHopfFirstSphereNegativeSection
            period hPeriod 2 sector mode))) :=
  ⟨firstSpherePositiveComplexWitness_tangential_collinear
      period hPeriod sector mode,
    firstSphereNegativeComplexWitness_tangential_collinear
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexWitnessNoGo4D
end JanusFormal
