import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalLocal4D

/-!
# Moving local witnesses for the first primitive SpinC sphere level

The two witnesses used by the complex multiplicity argument were previously
exposed only at normal time zero.  Their underlying quotient lifts already
exist for every normal time.  This gate transports all first-sphere local
coordinate formulas along those moving lifts.

At the phase-zero equatorial witness the radial coordinate is `+1`; at the
antipodal equatorial witness it is `-1`.  The two tangential coordinates
vanish at both witnesses.  The complete Hopf zero value carries the full
quarter-twisted normal phase, so the resulting formulas are suitable for
subsequent Fourier analysis of actual geometric sections.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingWitnessLocal4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereWitnessFiber4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Complete Hopf zero value at the moving phase-zero witness. -/
def primitiveSpinCHopfMovingPhaseWitnessValue
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    D9DoubledMatterFiber :=
  (2 : Real) •
    primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
      (primitiveSpinCGeometricZeroModeWitnessCover
        period hPeriod time)

/-- Complete Hopf zero value at the moving antipodal witness. -/
def primitiveSpinCHopfMovingAntipodalWitnessValue
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    D9DoubledMatterFiber :=
  primitiveSpinCHopfAntipodalWitnessFiber sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessCover
        period hPeriod time))

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

@[simp]
theorem primitiveSpinCHopfMovingAntipodalCoordinate_zero
    (time : Real) :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 0
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time) = -1 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)) 0 = -1
  rw [primitiveSpinCHopfAntipodalWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCHopfAntipodalWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

@[simp]
theorem primitiveSpinCHopfMovingAntipodalCoordinate_one
    (time : Real) :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 1
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time) = 0 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)) 1 = 0
  rw [primitiveSpinCHopfAntipodalWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCHopfAntipodalWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

@[simp]
theorem primitiveSpinCHopfMovingAntipodalCoordinate_two
    (time : Real) :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 2
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time) = 0 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)) 2 = 0
  rw [primitiveSpinCHopfAntipodalWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCHopfAntipodalWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

/-- Moving phase-witness formula for the coordinate component. -/
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
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_witness
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
      rfl

/-- Moving phase-witness formula for the tangential component. -/
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
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_witness
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
        hZero]
      rfl

/-- Moving phase-witness formula for the positive first-order eigensection. -/
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

/-- Moving phase-witness formula for the negative first-order eigensection. -/
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

/-- The first moving witness retains the positive tangential Clifford
relation at every normal time. -/
theorem primitiveSpinCHopfMovingPhaseWitness_tangential_relation
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingPhaseWitnessValue
          period hPeriod sector mode time) =
      d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfMovingPhaseWitnessValue
            period hPeriod sector mode time)) := by
  have hRelation :=
    primitiveSpinCHopfPositiveWitnessFiber_tangential_relation sector
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode
        (primitiveSpinCGeometricZeroModeWitnessCover
          period hPeriod time))
  rw [primitiveSpinCHopfPositiveWitnessFiber_eq_two_smul] at hRelation
  simpa [primitiveSpinCHopfMovingPhaseWitnessValue] using hRelation

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
    primitiveSpinCHopfMovingPhaseCoordinate_zero, one_smul]
  change
    _ +
        (d9DoubledMatterFiberCliffordGammaCLM 0
            ((2 : Real) •
              primitiveSpinCNormalModeDoubledLift period hPeriod sector mode
                (primitiveSpinCGeometricZeroModeWitnessCover
                  period hPeriod time)) -
          d9PrimitiveSpinCImaginaryAction
            ((2 : Real) •
              primitiveSpinCNormalModeDoubledLift period hPeriod sector mode
                (primitiveSpinCGeometricZeroModeWitnessCover
                  period hPeriod time))) = _
  rw [map_smul, primitiveSpinCNormalModeDoubledLift_gamma_zero,
    map_smul, sub_self, add_zero]

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
    primitiveSpinCHopfMovingPhaseCoordinate_zero, one_smul]
  change
    _ +
        (d9DoubledMatterFiberCliffordGammaCLM 0
            ((2 : Real) •
              primitiveSpinCNormalModeDoubledLift period hPeriod sector mode
                (primitiveSpinCGeometricZeroModeWitnessCover
                  period hPeriod time)) -
          d9PrimitiveSpinCImaginaryAction
            ((2 : Real) •
              primitiveSpinCNormalModeDoubledLift period hPeriod sector mode
                (primitiveSpinCGeometricZeroModeWitnessCover
                  period hPeriod time))) = _
  rw [map_smul, primitiveSpinCNormalModeDoubledLift_gamma_zero,
    map_smul, sub_self, add_zero]

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

/-- Moving antipodal-witness formula for the coordinate component. -/
theorem primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_movingAntipodal
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode) =
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time) •
        primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time := by
  have hMem :=
    primitiveSpinCHopfAntipodalWitnessBase_mem
      period hPeriod time
  have hZero :=
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_antipodal
      period hPeriod sector mode time
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessIndex
        period hPeriod time)
      (primitiveSpinCHopfAntipodalWitnessBase
        period hPeriod time) hMem] at hZero
  calc
    _ =
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode).localValue
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time) := by
      unfold primitiveSpinCHopfFirstSphereCoordinateSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time) hMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time) hMem
    _ = _ := by
      change
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time) •
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (primitiveSpinCHopfAntipodalWitnessIndex
                period hPeriod time)
              (primitiveSpinCHopfAntipodalWitnessBase
                period hPeriod time) = _
      rw [hZero]
      rfl

/-- Moving antipodal-witness formula for the tangential component. -/
theorem primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_movingAntipodal
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfMovingAntipodalWitnessValue
              period hPeriod sector mode time) := by
  have hMem :=
    primitiveSpinCHopfAntipodalWitnessBase_mem
      period hPeriod time
  have hZero :=
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_antipodal
      period hPeriod sector mode time
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessIndex
        period hPeriod time)
      (primitiveSpinCHopfAntipodalWitnessBase
        period hPeriod time) hMem] at hZero
  calc
    _ =
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode).localValue
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time) := by
      unfold primitiveSpinCHopfFirstSphereTangentialSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time) hMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time) hMem
    _ = _ := by
      rw [primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily_localValue,
        hZero]
      rfl

/-- Moving antipodal-witness formula for the positive eigensection. -/
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time) •
          primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time) +
      (d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfMovingAntipodalWitnessValue
              period hPeriod sector mode time)) := by
  unfold primitiveSpinCHopfFirstSpherePositiveSection
  rw [map_add, map_smul,
    primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_movingAntipodal,
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_movingAntipodal]

/-- Moving antipodal-witness formula for the negative eigensection. -/
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time) •
          primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time) +
      (d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfMovingAntipodalWitnessValue
              period hPeriod sector mode time)) := by
  unfold primitiveSpinCHopfFirstSphereNegativeSection
  rw [map_add, map_smul,
    primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_movingAntipodal,
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_movingAntipodal]

/-- The moving antipodal value retains the negative tangential relation at
every normal time. -/
theorem primitiveSpinCHopfMovingAntipodalWitness_tangential_relation
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) =
      -d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time)) := by
  exact primitiveSpinCHopfAntipodalWitnessFiber_tangential_relation sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessCover
        period hPeriod time))
    (primitiveSpinCNormalModeDoubledLift_gamma_one
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessCover
        period hPeriod time))

@[simp]
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal_one
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 1 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) := by
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal,
    primitiveSpinCHopfMovingAntipodalCoordinate_one]
  simp

@[simp]
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal_two
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 2 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 2
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) := by
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal,
    primitiveSpinCHopfMovingAntipodalCoordinate_two]
  simp

@[simp]
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal_one
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 1 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) := by
  rw [primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal,
    primitiveSpinCHopfMovingAntipodalCoordinate_one]
  simp

@[simp]
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal_two
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 2 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 2
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) := by
  rw [primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal,
    primitiveSpinCHopfMovingAntipodalCoordinate_two]
  simp

/-- Consolidated moving-witness package. -/
theorem primitiveSpinCHopfFirstSphereMovingWitnessLocal_closed
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
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
  ⟨primitiveSpinCHopfMovingPhaseWitness_tangential_relation
      period hPeriod sector mode time,
    primitiveSpinCHopfMovingAntipodalWitness_tangential_relation
      period hPeriod sector mode time⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingWitnessLocal4D
end JanusFormal
