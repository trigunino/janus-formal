import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingWitnessLocal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

/-!
# First-sphere local formulas along the moving phase witness

The equal-phase equatorial witness remains over the sphere point `(1,0,0)`
while its normal coordinate varies.  The complete Hopf value therefore keeps
the full quarter-twisted Fourier phase, whereas the three ambient coordinate
functions remain exactly `(1,0,0)`.

This gate transports the coordinate, tangential, positive and negative
first-sphere local formulas to every normal time.  It is the first geometric
step toward identifying the seven abstract finite-mode Fourier observables
with evaluations of the actual smooth-section synthesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingPhaseLocal4D

set_option autoImplicit false
noncomputable section

open Bundle
open Set
open scoped Manifold ContDiff Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingWitnessLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
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

@[simp]
theorem primitiveSpinCHopfMovingPhaseCoordinate_zero
    (time : Real) :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 0
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time) = 1 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)) 0 = 1
  rw [primitiveSpinCGeometricZeroModeWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCGeometricZeroModeWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

@[simp]
theorem primitiveSpinCHopfMovingPhaseCoordinate_one
    (time : Real) :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 1
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time) = 0 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)) 1 = 0
  rw [primitiveSpinCGeometricZeroModeWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCGeometricZeroModeWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

@[simp]
theorem primitiveSpinCHopfMovingPhaseCoordinate_two
    (time : Real) :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 2
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time) = 0 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)) 2 = 0
  rw [primitiveSpinCGeometricZeroModeWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCGeometricZeroModeWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

/-- The moving phase witness is a `Gamma₀ = J` eigenspinor. -/
theorem primitiveSpinCHopfMovingPhaseWitness_gamma_zero
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    d9DoubledMatterFiberCliffordGammaCLM 0
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time) := by
  rw [primitiveSpinCHopfMovingPhaseWitnessValue_eq_two_smul]
  simpa only [map_smul] using
    congrArg (fun value : D9DoubledMatterFiber => (2 : Real) • value)
      (primitiveSpinCNormalModeDoubledLift_gamma_zero
        period hPeriod sector mode
        (primitiveSpinCGeometricZeroModeWitnessCover
          period hPeriod time))

/-- Local coordinate of a first-sphere coordinate section at the moving
phase witness. -/
theorem primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_movingPhase
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode) =
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time) •
        primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time := by
  have hMem :=
    primitiveSpinCGeometricZeroModeWitnessBase_mem
      period hPeriod time
  have hZero :=
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingPhase
      period hPeriod sector mode time
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod sector mode
      (primitiveSpinCGeometricZeroModeWitnessIndex
        period hPeriod time)
      (primitiveSpinCGeometricZeroModeWitnessBase
        period hPeriod time) hMem] at hZero
  calc
    _ =
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode).localValue
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time) := by
      unfold primitiveSpinCHopfFirstSphereCoordinateSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time) hMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time) hMem
    _ = _ := by
      change
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time) •
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (primitiveSpinCGeometricZeroModeWitnessIndex
                period hPeriod time)
              (primitiveSpinCGeometricZeroModeWitnessBase
                period hPeriod time) = _
      rw [hZero]

/-- Local coordinate of a first-sphere tangential section at the moving phase
witness. -/
theorem primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_movingPhase
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfMovingPhaseWitnessValue
            period hPeriod sector mode time) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfMovingPhaseWitnessValue
              period hPeriod sector mode time) := by
  have hMem :=
    primitiveSpinCGeometricZeroModeWitnessBase_mem
      period hPeriod time
  have hZero :=
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingPhase
      period hPeriod sector mode time
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod sector mode
      (primitiveSpinCGeometricZeroModeWitnessIndex
        period hPeriod time)
      (primitiveSpinCGeometricZeroModeWitnessBase
        period hPeriod time) hMem] at hZero
  calc
    _ =
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode).localValue
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time) := by
      unfold primitiveSpinCHopfFirstSphereTangentialSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time) hMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time) hMem
    _ = _ := by
      rw [primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily_localValue,
        hZero, d9PrimitiveSpinCBaseUnitRadialCoordinate]

/-- Positive first-sphere local-coordinate formula at every normal time. -/
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time) •
          primitiveSpinCHopfMovingPhaseWitnessValue
            period hPeriod sector mode time) +
      (d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfMovingPhaseWitnessValue
            period hPeriod sector mode time) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfMovingPhaseWitnessValue
              period hPeriod sector mode time)) := by
  unfold primitiveSpinCHopfFirstSpherePositiveSection
  rw [map_add, map_smul,
    primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_movingPhase,
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_movingPhase]

/-- Negative first-sphere local-coordinate formula at every normal time. -/
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time) •
          primitiveSpinCHopfMovingPhaseWitnessValue
            period hPeriod sector mode time) +
      (d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfMovingPhaseWitnessValue
            period hPeriod sector mode time) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCGeometricZeroModeWitnessBase
              period hPeriod time) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfMovingPhaseWitnessValue
              period hPeriod sector mode time)) := by
  unfold primitiveSpinCHopfFirstSphereNegativeSection
  rw [map_add, map_smul,
    primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_movingPhase,
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_movingPhase]

@[simp]
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase_zero
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 0 sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time := by
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase,
    primitiveSpinCHopfMovingPhaseCoordinate_zero,
    primitiveSpinCHopfMovingPhaseWitness_gamma_zero]
  simp

@[simp]
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase_zero
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 0 sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time := by
  rw [primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase,
    primitiveSpinCHopfMovingPhaseCoordinate_zero,
    primitiveSpinCHopfMovingPhaseWitness_gamma_zero]
  simp

@[simp]
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase_one
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 1 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time) := by
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase,
    primitiveSpinCHopfMovingPhaseCoordinate_one]
  simp

@[simp]
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase_two
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 2 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 2
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time) := by
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase,
    primitiveSpinCHopfMovingPhaseCoordinate_two]
  simp

@[simp]
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase_one
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 1 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time) := by
  rw [primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase,
    primitiveSpinCHopfMovingPhaseCoordinate_one]
  simp

@[simp]
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase_two
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 2 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 2
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time) := by
  rw [primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase,
    primitiveSpinCHopfMovingPhaseCoordinate_two]
  simp

/-- The two moving tangential coordinates retain the positive complex
relation, independently of the internal Dirac sign. -/
theorem primitiveSpinCHopfFirstSphereMovingPhaseTangential_closed
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 1 sector mode) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfFirstSpherePositiveSection
            period hPeriod 2 sector mode)) ∧
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 1 sector mode) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessIndex
            period hPeriod time)
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfFirstSphereNegativeSection
            period hPeriod 2 sector mode)) := by
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase_one,
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase_two,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase_one,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase_two]
  exact
    ⟨primitiveSpinCHopfMovingPhaseWitness_tangential
        period hPeriod sector mode time,
      primitiveSpinCHopfMovingPhaseWitness_tangential
        period hPeriod sector mode time⟩

/-- Consolidated moving phase-witness package for both internal signs. -/
theorem primitiveSpinCHopfFirstSphereMovingPhaseLocal_closed
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 0 sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time ∧
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCGeometricZeroModeWitnessIndex
          period hPeriod time)
        (primitiveSpinCGeometricZeroModeWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 0 sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time ∧
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time) =
      d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfMovingPhaseWitnessValue
            period hPeriod sector mode time)) :=
  ⟨primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingPhase_zero
      period hPeriod sector mode time,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingPhase_zero
      period hPeriod sector mode time,
    primitiveSpinCHopfMovingPhaseWitness_tangential
      period hPeriod sector mode time⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingPhaseLocal4D
end JanusFormal
