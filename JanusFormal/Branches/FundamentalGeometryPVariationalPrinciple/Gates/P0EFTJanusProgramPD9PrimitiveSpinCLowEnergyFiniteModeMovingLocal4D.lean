import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingAntipodalLocal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeCore4D

/-!
# Moving local observables of finite low-energy SpinC packets

For one fixed normal-root sector, the finite low-energy synthesis combines
finitely many circle labels, each carrying seven faithful complex geometric
coordinates.  The moving phase and antipodal witnesses are genuine quotient
points at every normal time.

This gate composes those two local-coordinate evaluations with the actual
finite smooth-section synthesis.  On a single circle label it proves the
exact geometric decomposition into the Hopf zero contribution and the signed
first-sphere contribution.  No cross-mode Fourier injectivity is asserted
here; this is the small geometric bridge needed by that subsequent theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeMovingLocal4D

set_option autoImplicit false
noncomputable section

open Bundle
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingAntipodalLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyComplexCoefficientRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Actual local-coordinate evaluation of a finite low-energy packet along
 the moving equal-phase witness. -/
def primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal
    (sector : NormalRootChoice) (time : Real) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real]
      D9DoubledMatterFiber :=
  (primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod
      (primitiveSpinCGeometricZeroModeWitnessIndex
        period hPeriod time)
      (primitiveSpinCGeometricZeroModeWitnessBase
        period hPeriod time)).comp
    (primitiveSpinCHopfLowEnergyFiniteModeSynthesis
      period hPeriod sector)

/-- Actual local-coordinate evaluation of a finite low-energy packet along
 the moving antipodal witness. -/
def primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal
    (sector : NormalRootChoice) (time : Real) :
    PrimitiveSpinCLowEnergyFiniteModeComplexCoefficients →ₗ[Real]
      D9DoubledMatterFiber :=
  (primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod
      (primitiveSpinCHopfAntipodalWitnessIndex
        period hPeriod time)
      (primitiveSpinCHopfAntipodalWitnessBase
        period hPeriod time)).comp
    (primitiveSpinCHopfLowEnergyFiniteModeSynthesis
      period hPeriod sector)

/-- On one supported circle label, moving phase evaluation is exactly local
 evaluation of the faithful seven-coordinate geometric synthesis. -/
@[simp]
theorem primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal_single
    (sector : NormalRootChoice) (time : Real) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal
        period hPeriod sector time (Finsupp.single mode coefficients) =
      primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode coefficients) := by
  rw [primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal,
    LinearMap.comp_apply,
    primitiveSpinCHopfLowEnergyFiniteModeSynthesis_single]

/-- The same single-label identity at the moving antipodal witness. -/
@[simp]
theorem primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal_single
    (sector : NormalRootChoice) (time : Real) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal
        period hPeriod sector time (Finsupp.single mode coefficients) =
      primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
          period hPeriod sector mode coefficients) := by
  rw [primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal,
    LinearMap.comp_apply,
    primitiveSpinCHopfLowEnergyFiniteModeSynthesis_single]

/-- Exact zero-plus-first-sphere decomposition of one moving phase local
 observation. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal_single_split
    (sector : NormalRootChoice) (time : Real) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal
        period hPeriod sector time (Finsupp.single mode coefficients) =
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, mode) coefficients.1) +
        primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients.2) := by
  calc
    _ = primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
            period hPeriod sector mode coefficients) :=
      primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal_single
        period hPeriod sector time mode coefficients
    _ = primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
              period hPeriod (sector, mode) coefficients.1 +
            primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
              period hPeriod sector mode coefficients.2) := by
      rw [primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply]
    _ = _ :=
      map_add
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)) _ _

/-- Exact zero-plus-first-sphere decomposition of one moving antipodal local
 observation. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal_single_split
    (sector : NormalRootChoice) (time : Real) (mode : Int)
    (coefficients : PrimitiveSpinCLowEnergyGeometricComplexCoefficients) :
    primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal
        period hPeriod sector time (Finsupp.single mode coefficients) =
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
            period hPeriod (sector, mode) coefficients.1) +
        primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
            period hPeriod sector mode coefficients.2) := by
  calc
    _ = primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis
            period hPeriod sector mode coefficients) :=
      primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal_single
        period hPeriod sector time mode coefficients
    _ = primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfZeroModeCoefficientLinearMap
              period hPeriod (sector, mode) coefficients.1 +
            primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
              period hPeriod sector mode coefficients.2) := by
      rw [primitiveSpinCHopfLowEnergyComplexCoefficientSynthesis_apply]
    _ = _ :=
      map_add
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)) _ _

/-- Consolidated moving-local bridge for one finite-mode generator. -/
theorem primitiveSpinCHopfLowEnergyFiniteModeMovingLocal_closed
    (sector : NormalRootChoice) :
    (∀ time mode coefficients,
      primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal
          period hPeriod sector time (Finsupp.single mode coefficients) =
        primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCGeometricZeroModeWitnessIndex
              period hPeriod time)
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time)
            (primitiveSpinCHopfZeroModeCoefficientLinearMap
              period hPeriod (sector, mode) coefficients.1) +
          primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCGeometricZeroModeWitnessIndex
              period hPeriod time)
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time)
            (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
              period hPeriod sector mode coefficients.2)) ∧
      (∀ time mode coefficients,
        primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal
            period hPeriod sector time (Finsupp.single mode coefficients) =
          primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod
              (primitiveSpinCHopfAntipodalWitnessIndex
                period hPeriod time)
              (primitiveSpinCHopfAntipodalWitnessBase
                period hPeriod time)
              (primitiveSpinCHopfZeroModeCoefficientLinearMap
                period hPeriod (sector, mode) coefficients.1) +
            primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod
              (primitiveSpinCHopfAntipodalWitnessIndex
                period hPeriod time)
              (primitiveSpinCHopfAntipodalWitnessBase
                period hPeriod time)
              (primitiveSpinCHopfFirstSphereSignedComplexPacketSynthesis
                period hPeriod sector mode coefficients.2)) :=
  ⟨primitiveSpinCHopfLowEnergyFiniteModeMovingPhaseLocal_single_split
      period hPeriod sector,
    primitiveSpinCHopfLowEnergyFiniteModeMovingAntipodalLocal_single_split
      period hPeriod sector⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCLowEnergyFiniteModeMovingLocal4D
end JanusFormal
