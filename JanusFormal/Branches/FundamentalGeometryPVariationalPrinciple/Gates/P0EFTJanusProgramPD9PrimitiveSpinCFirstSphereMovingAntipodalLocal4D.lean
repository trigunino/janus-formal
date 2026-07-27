import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingPhaseLocal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D

/-!
# First-sphere local formulas along the moving antipodal witness

The antipodal equatorial witness remains over the sphere point `(-1,0,0)`
while its normal coordinate varies.  The complete Hopf value retains the full
quarter-twisted Fourier phase and carries the reversed tangential complex
relation.

This gate transports the coordinate, tangential, positive and negative
first-sphere local formulas to every normal time.  Together with the moving
phase witness, it supplies the two opposite geometric observations needed to
recover the three complex multiplicity coordinates mode-by-mode.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingAntipodalLocal4D

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
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingPhaseLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingWitnessLocal4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
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

/-- The antipodal moving witness lies in the north monopole chart. -/
theorem primitiveSpinCHopfMovingAntipodalCover_mem_north
    (time : Real) :
    d9MonopoleSphereCoverProjection period hPeriod
        (primitiveSpinCHopfAntipodalWitnessCover
          period hPeriod time) ∈
      monopoleChartDomain .north := by
  rw [primitiveSpinCHopfAntipodalWitnessCover_sphere]
  simp [monopoleChartDomain, monopoleEquator, monopoleSphereCoordinate]

/-- The antipodal moving witness is a `Gamma₀ = -J` eigenspinor.  This is the
radial Clifford equation at the radial point `(-1,0,0)`. -/
theorem primitiveSpinCHopfMovingAntipodalWitness_gamma_zero
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    d9DoubledMatterFiberCliffordGammaCLM 0
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) =
      -d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) := by
  have hRadial :=
    primitiveSpinCHopfZeroModeLocalGaugeFamily_unitRadial_eigen
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalWitnessCover period hPeriod time)
      .north
      (primitiveSpinCHopfMovingAntipodalCover_mem_north
        period hPeriod time)
  change
    d9UnitRadialClifford period hPeriod
        (primitiveSpinCHopfAntipodalWitnessCover period hPeriod time)
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (primitiveSpinCHopfAntipodalWitnessIndex
              period hPeriod time)
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time)) =
      d9PrimitiveSpinCImaginaryAction
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (primitiveSpinCHopfAntipodalWitnessIndex
              period hPeriod time)
            (primitiveSpinCHopfAntipodalWitnessBase
              period hPeriod time)) at hRadial
  rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_antipodal] at hRadial
  change
    d9UnitRadialClifford period hPeriod
        (primitiveSpinCHopfAntipodalWitnessCover period hPeriod time)
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) at hRadial
  have hNegative :
      -d9DoubledMatterFiberCliffordGammaCLM 0
          (primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time) =
        d9PrimitiveSpinCImaginaryAction
          (primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time) := by
    simpa [d9UnitRadialClifford, Fin.sum_univ_succ,
      d9UnitRadialCoordinate,
      primitiveSpinCHopfAntipodalWitnessCover,
      monopoleEquator, monopoleSphereCoordinate] using hRadial
  have hNegated := congrArg
    (fun value : D9DoubledMatterFiber => -value) hNegative
  simpa using hNegated

/-- Local coordinate of a first-sphere coordinate section at the moving
antipodal witness. -/
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
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingAntipodal
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

/-- Local coordinate of a first-sphere tangential section at the moving
antipodal witness. -/
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
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_movingAntipodal
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
        hZero, d9PrimitiveSpinCBaseUnitRadialCoordinate]

/-- Positive first-sphere local-coordinate formula at every antipodal normal
time. -/
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

/-- Negative first-sphere local-coordinate formula at every antipodal normal
time. -/
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

@[simp]
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal_zero
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 0 sector mode) =
      (normalRootLeviCivitaCorrectedFrequency period sector mode -
          primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
        primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time := by
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal,
    primitiveSpinCHopfMovingAntipodalCoordinate_zero,
    primitiveSpinCHopfMovingAntipodalWitness_gamma_zero]
  module

@[simp]
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal_zero
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 0 sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode +
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time := by
  rw [primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal,
    primitiveSpinCHopfMovingAntipodalCoordinate_zero,
    primitiveSpinCHopfMovingAntipodalWitness_gamma_zero]
  module

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

/-- The two moving tangential coordinates retain the reversed complex
relation, independently of the internal Dirac sign. -/
theorem primitiveSpinCHopfFirstSphereMovingAntipodalTangential_closed
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 1 sector mode) =
      -d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfFirstSpherePositiveSection
            period hPeriod 2 sector mode)) ∧
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 1 sector mode) =
      -d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalWitnessIndex
            period hPeriod time)
          (primitiveSpinCHopfAntipodalWitnessBase
            period hPeriod time)
          (primitiveSpinCHopfFirstSphereNegativeSection
            period hPeriod 2 sector mode)) := by
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal_one,
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal_two,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal_one,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal_two]
  exact
    ⟨primitiveSpinCHopfMovingAntipodalWitness_tangential
        period hPeriod sector mode time,
      primitiveSpinCHopfMovingAntipodalWitness_tangential
        period hPeriod sector mode time⟩

/-- Consolidated moving antipodal-witness package for both internal signs. -/
theorem primitiveSpinCHopfFirstSphereMovingAntipodalLocal_closed
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 0 sector mode) =
      (normalRootLeviCivitaCorrectedFrequency period sector mode -
          primitiveSpinCHopfFirstSphereDiracFrequency period sector mode) •
        primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time ∧
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalWitnessIndex
          period hPeriod time)
        (primitiveSpinCHopfAntipodalWitnessBase
          period hPeriod time)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 0 sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode +
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time ∧
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfMovingAntipodalWitnessValue
          period hPeriod sector mode time) =
      -d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfMovingAntipodalWitnessValue
            period hPeriod sector mode time)) :=
  ⟨primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_movingAntipodal_zero
      period hPeriod sector mode time,
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_movingAntipodal_zero
      period hPeriod sector mode time,
    primitiveSpinCHopfMovingAntipodalWitness_tangential
      period hPeriod sector mode time⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstSphereMovingAntipodalLocal4D
end JanusFormal
