import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D

/-!
# Moving geometric witnesses for the first primitive SpinC sphere level

The two equatorial witnesses used by the complex multiplicity argument are
available at every normal time.  This gate packages their genuine Hopf zero
values and transports the opposite tangential Clifford relations along the
normal-root Fourier motion.

No fixed-time simplification is used: the full quarter-twisted normal phase is
retained.  These identities are the stable geometric input for identifying
finite Fourier coordinates with actual local observables.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingWitnessLocal4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereWitnessFiber4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The genuine equal-phase Hopf fiber at arbitrary normal time. -/
def primitiveSpinCHopfMovingPhaseWitnessValue
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    D9DoubledMatterFiber :=
  primitiveSpinCHopfPositiveWitnessFiber sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
      (primitiveSpinCGeometricZeroModeWitnessCover
        period hPeriod time))

/-- The genuine antipodal Hopf fiber at arbitrary normal time. -/
def primitiveSpinCHopfMovingAntipodalWitnessValue
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    D9DoubledMatterFiber :=
  primitiveSpinCHopfAntipodalWitnessFiber sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessCover
        period hPeriod time))

/-- The equal-phase moving witness remains exactly twice the normal mode. -/
theorem primitiveSpinCHopfMovingPhaseWitnessValue_eq_two_smul
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCHopfMovingPhaseWitnessValue
        period hPeriod sector mode time =
      (2 : Real) •
        primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode
          (primitiveSpinCGeometricZeroModeWitnessCover
            period hPeriod time) :=
  primitiveSpinCHopfPositiveWitnessFiber_eq_two_smul sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
      (primitiveSpinCGeometricZeroModeWitnessCover
        period hPeriod time))

/-- The antipodal moving witness is the opposite Hopf-frame difference. -/
theorem primitiveSpinCHopfMovingAntipodalWitnessValue_eq
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCHopfMovingAntipodalWitnessValue
        period hPeriod sector mode time =
      (-2 : Real) •
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode
              (primitiveSpinCHopfAntipodalWitnessCover
                period hPeriod time))) :=
  primitiveSpinCHopfAntipodalWitnessFiber_eq sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessCover
        period hPeriod time))

/-- The actual global Hopf zero section evaluates to the moving equal-phase
fiber at the phase-zero quotient witness. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingPhase
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      primitiveSpinCHopfMovingPhaseWitnessValue
        period hPeriod sector mode time := by
  rw [primitiveSpinCHopfMovingPhaseWitnessValue_eq_two_smul]
  exact primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_witness
    period hPeriod sector mode time

/-- The actual global Hopf zero section evaluates to the moving antipodal
fiber at the antipodal quotient witness. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingAntipodal
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      primitiveSpinCHopfMovingAntipodalWitnessValue
        period hPeriod sector mode time :=
  primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_antipodal
    period hPeriod sector mode time

/-- The moving equal-phase witness preserves the positive tangential complex
Clifford relation at every normal time. -/
theorem primitiveSpinCHopfMovingPhaseWitness_tangential
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time) =
      d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfMovingPhaseWitnessValue
            period hPeriod sector mode time)) :=
  primitiveSpinCHopfPositiveWitnessFiber_tangential sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
      (primitiveSpinCGeometricZeroModeWitnessCover
        period hPeriod time))
    (primitiveSpinCNormalModeDoubledLift_gamma_one
      period hPeriod sector mode
      (primitiveSpinCGeometricZeroModeWitnessCover
        period hPeriod time))

/-- The moving antipodal witness reverses the tangential complex Clifford
relation at every normal time. -/
theorem primitiveSpinCHopfMovingAntipodalWitness_tangential
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) =
      -d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time)) :=
  primitiveSpinCHopfAntipodalWitnessFiber_tangential sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessCover
        period hPeriod time))
    (primitiveSpinCNormalModeDoubledLift_gamma_one
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessCover
        period hPeriod time))

/-- Consolidated moving-witness package, including its realization by actual
local coordinates of the global smooth Hopf zero section. -/
theorem primitiveSpinCHopfFirstSphereMovingWitnessLocal_closed
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      primitiveSpinCHopfMovingPhaseWitnessValue
        period hPeriod sector mode time ∧
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      primitiveSpinCHopfMovingAntipodalWitnessValue
        period hPeriod sector mode time ∧
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time) =
      d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfMovingPhaseWitnessValue
            period hPeriod sector mode time)) ∧
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) =
      -d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time)) :=
  ⟨primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingPhase
      period hPeriod sector mode time,
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingAntipodal
      period hPeriod sector mode time,
    primitiveSpinCHopfMovingPhaseWitness_tangential
      period hPeriod sector mode time,
    primitiveSpinCHopfMovingAntipodalWitness_tangential
      period hPeriod sector mode time⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingWitnessLocal4D
end JanusFormal
