import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexWitnessNoGo4D

/-!
# Two orthogonal geometric witnesses for the first sphere level

The existing equatorial witness lies over the radial axis `e₀`.  This gate
constructs a second genuine quotient witness over the orthogonal radial axis
`e₁`, both at normal time zero.

For an arbitrary lifted point and monopole chart, the local coordinates of
the coordinate, tangential, positive and negative first-sphere sections are
expressed directly in terms of the complete Hopf zero-mode local value.  At a
radial axis, the aligned first-sphere coordinate is a nonzero scalar multiple
of that Hopf value, while the other two coordinates are Clifford-tangential.

These formulas are the geometric input needed for the two-axis complex
multiplicity proof; no abstract dimension argument is used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAxisWitness4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexWitnessNoGo4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
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

private abbrev throatProjectionLocalHomeomorph :
    LocalHomeomorph
      (ThroatCover period hPeriod) (ThroatBase period hPeriod) :=
  localHomeomorphFromQuotient
    (throatDeckTransformation (ThroatData period hPeriod))
    (throatDeckGroup (ThroatData period hPeriod))
    (throatDeckGroup_nonempty (ThroatData period hPeriod))
    (throatDeckGroup_id (ThroatData period hPeriod))
    (throatDeckGroup_comp (ThroatData period hPeriod))
    (throatDeckGroup_inv (ThroatData period hPeriod))
    (throatDeckAction_free (ThroatData period hPeriod))
    (throatDeckAction_proper (ThroatData period hPeriod))

/-- Generic complete Hopf zero-mode local value at a lifted point and chart. -/
def primitiveSpinCHopfAxisWitnessValue
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (sector : NormalRootChoice) (mode : Int) : D9DoubledMatterFiber :=
  (primitiveSpinCHopfZeroModeLocalGaugeFamily
    period hPeriod sector mode).localValue
      (point, chart) (mappingTorusMk (ThroatData period hPeriod) point)

/-- The quotient point determined by a lifted point belongs to its normal
chart and to every compatible monopole chart. -/
theorem primitiveSpinCHopfAxisWitnessBase_mem
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    mappingTorusMk (ThroatData period hPeriod) point ∈
      d9PrimitiveSpinCBaseSet period hPeriod (point, chart) := by
  constructor
  · exact
      (throatProjectionLocalHomeomorph period hPeriod).map_target point
  · simpa [d9ThroatMonopoleSphereProjection_mk] using hChart

/-- Generic local-coordinate formula for a first-sphere coordinate section. -/
theorem primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_at_mk
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart)
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point)
        (primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode) =
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (mappingTorusMk (ThroatData period hPeriod) point) •
        primitiveSpinCHopfAxisWitnessValue
          period hPeriod point chart sector mode := by
  have hMem :=
    primitiveSpinCHopfAxisWitnessBase_mem
      period hPeriod point chart hChart
  calc
    _ =
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode).localValue
          (point, chart)
          (mappingTorusMk (ThroatData period hPeriod) point) := by
      unfold primitiveSpinCHopfFirstSphereCoordinateSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point) hMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point) hMem
    _ = _ := by
      change
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (mappingTorusMk (ThroatData period hPeriod) point) •
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (point, chart)
              (mappingTorusMk (ThroatData period hPeriod) point) = _
      rfl

/-- Generic local-coordinate formula for a first-sphere tangential section. -/
theorem primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_at_mk
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart)
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfAxisWitnessValue
            period hPeriod point chart sector mode) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (mappingTorusMk (ThroatData period hPeriod) point) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfAxisWitnessValue
              period hPeriod point chart sector mode) := by
  have hMem :=
    primitiveSpinCHopfAxisWitnessBase_mem
      period hPeriod point chart hChart
  calc
    _ =
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode).localValue
          (point, chart)
          (mappingTorusMk (ThroatData period hPeriod) point) := by
      unfold primitiveSpinCHopfFirstSphereTangentialSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point) hMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point) hMem
    _ = _ := by
      rw [
        primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily_localValue]
      rfl

/-- Generic positive first-sphere local-coordinate formula. -/
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_at_mk
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart)
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (mappingTorusMk (ThroatData period hPeriod) point) •
          primitiveSpinCHopfAxisWitnessValue
            period hPeriod point chart sector mode) +
      (d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfAxisWitnessValue
            period hPeriod point chart sector mode) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (mappingTorusMk (ThroatData period hPeriod) point) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfAxisWitnessValue
              period hPeriod point chart sector mode)) := by
  unfold primitiveSpinCHopfFirstSpherePositiveSection
  rw [map_add, map_smul,
    primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_at_mk
      period hPeriod point chart hChart,
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_at_mk
      period hPeriod point chart hChart]

/-- Generic negative first-sphere local-coordinate formula. -/
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_at_mk
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart)
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (mappingTorusMk (ThroatData period hPeriod) point) •
          primitiveSpinCHopfAxisWitnessValue
            period hPeriod point chart sector mode) +
      (d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfAxisWitnessValue
            period hPeriod point chart sector mode) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (mappingTorusMk (ThroatData period hPeriod) point) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfAxisWitnessValue
              period hPeriod point chart sector mode)) := by
  unfold primitiveSpinCHopfFirstSphereNegativeSection
  rw [map_add, map_smul,
    primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_at_mk
      period hPeriod point chart hChart,
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_at_mk
      period hPeriod point chart hChart]

/-- The complete Hopf value is a positive radial Clifford eigenspinor at every
compatible lifted point. -/
theorem primitiveSpinCHopfAxisWitnessValue_unitRadial_eigen
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart)
    (sector : NormalRootChoice) (mode : Int) :
    d9UnitRadialClifford period hPeriod point
        (primitiveSpinCHopfAxisWitnessValue
          period hPeriod point chart sector mode) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCHopfAxisWitnessValue
          period hPeriod point chart sector mode) :=
  primitiveSpinCHopfZeroModeLocalGaugeFamily_unitRadial_eigen
    period hPeriod sector mode point chart hChart

/-- First radial-axis lift, reusing the existing geometric witness. -/
abbrev primitiveSpinCHopfFirstAxisCover : ThroatCover period hPeriod :=
  firstSphereComplexWitnessCover period hPeriod

/-- First radial-axis quotient point. -/
abbrev primitiveSpinCHopfFirstAxisBase : ThroatBase period hPeriod :=
  firstSphereComplexWitnessBase period hPeriod

/-- First radial-axis local index. -/
abbrev primitiveSpinCHopfFirstAxisIndex :
    D9PrimitiveSpinCIndex period hPeriod :=
  firstSphereComplexWitnessIndex period hPeriod

/-- Second radial-axis lift, lying over `monopoleEquator (π/2)`. -/
def primitiveSpinCHopfSecondAxisCover : ThroatCover period hPeriod :=
  ⟨equatorialTwoSphereHomeomorph.symm
      (monopoleEquator (Real.pi / 2)), 0⟩

/-- Second radial-axis quotient point. -/
def primitiveSpinCHopfSecondAxisBase : ThroatBase period hPeriod :=
  mappingTorusMk (ThroatData period hPeriod)
    (primitiveSpinCHopfSecondAxisCover period hPeriod)

/-- North-chart local index at the second radial axis. -/
def primitiveSpinCHopfSecondAxisIndex :
    D9PrimitiveSpinCIndex period hPeriod :=
  (primitiveSpinCHopfSecondAxisCover period hPeriod, .north)

/-- The second lift projects to the equatorial point `(0,1,0)`. -/
@[simp]
theorem primitiveSpinCHopfSecondAxisCover_sphere :
    d9MonopoleSphereCoverProjection period hPeriod
        (primitiveSpinCHopfSecondAxisCover period hPeriod) =
      monopoleEquator (Real.pi / 2) := by
  simp [primitiveSpinCHopfSecondAxisCover,
    d9MonopoleSphereCoverProjection]

/-- The second radial-axis point lies in the north monopole chart. -/
theorem primitiveSpinCHopfSecondAxis_mem_north :
    d9MonopoleSphereCoverProjection period hPeriod
        (primitiveSpinCHopfSecondAxisCover period hPeriod) ∈
      monopoleChartDomain .north := by
  rw [primitiveSpinCHopfSecondAxisCover_sphere]
  change
    monopoleSphereCoordinate (monopoleEquator (Real.pi / 2)) 2 ≠ -1
  simp [monopoleEquator, monopoleSphereCoordinate]

/-- The second quotient witness belongs to its full primitive SpinC chart. -/
theorem primitiveSpinCHopfSecondAxisBase_mem :
    primitiveSpinCHopfSecondAxisBase period hPeriod ∈
      d9PrimitiveSpinCBaseSet period hPeriod
        (primitiveSpinCHopfSecondAxisIndex period hPeriod) := by
  exact primitiveSpinCHopfAxisWitnessBase_mem
    period hPeriod
    (primitiveSpinCHopfSecondAxisCover period hPeriod) .north
    (primitiveSpinCHopfSecondAxis_mem_north period hPeriod)

@[simp]
theorem primitiveSpinCHopfSecondAxisCoordinate_zero :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 0
        (primitiveSpinCHopfSecondAxisBase period hPeriod) = 0 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCHopfSecondAxisBase period hPeriod)) 0 = 0
  rw [primitiveSpinCHopfSecondAxisBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCHopfSecondAxisCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

@[simp]
theorem primitiveSpinCHopfSecondAxisCoordinate_one :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 1
        (primitiveSpinCHopfSecondAxisBase period hPeriod) = 1 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCHopfSecondAxisBase period hPeriod)) 1 = 1
  rw [primitiveSpinCHopfSecondAxisBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCHopfSecondAxisCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

@[simp]
theorem primitiveSpinCHopfSecondAxisCoordinate_two :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 2
        (primitiveSpinCHopfSecondAxisBase period hPeriod) = 0 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCHopfSecondAxisBase period hPeriod)) 2 = 0
  rw [primitiveSpinCHopfSecondAxisBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCHopfSecondAxisCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

/-- Complete Hopf value at the first axis. -/
def primitiveSpinCHopfFirstAxisValue
    (sector : NormalRootChoice) (mode : Int) : D9DoubledMatterFiber :=
  primitiveSpinCHopfAxisWitnessValue period hPeriod
    (primitiveSpinCHopfFirstAxisCover period hPeriod) .north sector mode

/-- Complete Hopf value at the second axis. -/
def primitiveSpinCHopfSecondAxisValue
    (sector : NormalRootChoice) (mode : Int) : D9DoubledMatterFiber :=
  primitiveSpinCHopfAxisWitnessValue period hPeriod
    (primitiveSpinCHopfSecondAxisCover period hPeriod) .north sector mode

/-- The first-axis Hopf value is nonzero. -/
theorem primitiveSpinCHopfFirstAxisValue_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstAxisValue
        period hPeriod sector mode ≠ 0 := by
  intro hZero
  have hLocal :=
    firstSpherePositiveLocalCoordinate_zero_ne_zero
      period hPeriod sector mode
  have hFormula :=
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_at_mk
      period hPeriod
      (primitiveSpinCHopfFirstAxisCover period hPeriod) .north
      (by
        simpa [primitiveSpinCHopfFirstAxisCover,
          firstSphereComplexWitnessCover] using
          primitiveSpinCGeometricZeroModeWitnessBase_mem
            period hPeriod 0 |>.2)
      0 sector mode
  change
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfFirstAxisIndex period hPeriod)
        (primitiveSpinCHopfFirstAxisBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 0 sector mode) = _ at hFormula
  rw [firstSphereWitnessCoordinate_zero, one_smul,
    primitiveSpinCNormalModeDoubledLift_gamma_zero] at hFormula
  change
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfFirstAxisIndex period hPeriod)
        (primitiveSpinCHopfFirstAxisBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 0 sector mode) =
      _ • primitiveSpinCHopfFirstAxisValue period hPeriod sector mode +
        (_ - _) at hFormula
  rw [hZero, smul_zero, map_zero, map_zero, sub_zero, add_zero] at hFormula
  exact hLocal hFormula

/-- At the first axis, the complete Hopf value is a `Γ₀ = J` eigenspinor. -/
theorem primitiveSpinCHopfFirstAxisValue_gamma_zero
    (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberCliffordGammaCLM 0
        (primitiveSpinCHopfFirstAxisValue period hPeriod sector mode) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCHopfFirstAxisValue period hPeriod sector mode) := by
  have hRadial :=
    primitiveSpinCHopfAxisWitnessValue_unitRadial_eigen
      period hPeriod
      (primitiveSpinCHopfFirstAxisCover period hPeriod) .north
      (by
        simpa [primitiveSpinCHopfFirstAxisCover,
          firstSphereComplexWitnessCover] using
          primitiveSpinCGeometricZeroModeWitnessBase_mem
            period hPeriod 0 |>.2)
      sector mode
  simpa [primitiveSpinCHopfFirstAxisValue,
    d9UnitRadialClifford, Fin.sum_univ_succ,
    firstSphereWitnessCoordinate_zero,
    firstSphereWitnessCoordinate_one,
    firstSphereWitnessCoordinate_two] using hRadial

/-- At the second axis, the complete Hopf value is a `Γ₁ = J` eigenspinor. -/
theorem primitiveSpinCHopfSecondAxisValue_gamma_one
    (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfSecondAxisValue period hPeriod sector mode) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCHopfSecondAxisValue period hPeriod sector mode) := by
  have hRadial :=
    primitiveSpinCHopfAxisWitnessValue_unitRadial_eigen
      period hPeriod
      (primitiveSpinCHopfSecondAxisCover period hPeriod) .north
      (primitiveSpinCHopfSecondAxis_mem_north period hPeriod)
      sector mode
  simpa [primitiveSpinCHopfSecondAxisValue,
    d9UnitRadialClifford, Fin.sum_univ_succ,
    primitiveSpinCHopfSecondAxisCover,
    d9UnitRadialCoordinate,
    d9MonopoleSphereCoverProjection, monopoleEquator,
    monopoleSphereCoordinate] using hRadial

/-- The complete Hopf value at the second axis is nonzero. -/
theorem primitiveSpinCHopfSecondAxisValue_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfSecondAxisValue
        period hPeriod sector mode ≠ 0 := by
  intro hZero
  have hCoefficient := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector)
    hZero
  cases sector <;>
    simp [primitiveSpinCHopfSecondAxisValue,
      primitiveSpinCHopfAxisWitnessValue,
      primitiveSpinCHopfSecondAxisCover,
      primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
      primitiveMonopoleZeroLocalValue,
      primitiveMonopoleZeroNorthValue,
      primitiveMonopoleZeroComplementLocalValue,
      primitiveMonopoleZeroComplementNorthValue,
      monopoleEquator, monopoleSphereCoordinate, monopoleSphereXY,
      d9MonopoleSphereCoverProjection,
      d9PrimitiveSpinCHopfFirstFrameCLM,
      d9PrimitiveSpinCHopfSecondFrameCLM,
      primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      normalRootSpinFramePhase, normalRootSpinFramePhaseAngle,
      primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap,
      d9MatterGammaPositiveCoefficientLinearMap,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      ambientHalfGammaPositiveEigenvector,
      d9PrimitiveSpinCImaginaryAction,
      d9PrimitiveSpinCImaginaryPhase] at hCoefficient

/-- At the first axis, the aligned positive coordinate is purely radial. -/
theorem primitiveSpinCHopfFirstAxisPositiveAligned
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfFirstAxisIndex period hPeriod)
        (primitiveSpinCHopfFirstAxisBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 0 sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfFirstAxisValue period hPeriod sector mode := by
  have hFormula :=
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_at_mk
      period hPeriod
      (primitiveSpinCHopfFirstAxisCover period hPeriod) .north
      (by
        simpa [primitiveSpinCHopfFirstAxisCover,
          firstSphereComplexWitnessCover] using
          primitiveSpinCGeometricZeroModeWitnessBase_mem
            period hPeriod 0 |>.2)
      0 sector mode
  simpa [primitiveSpinCHopfFirstAxisValue,
    primitiveSpinCHopfFirstAxisIndex,
    primitiveSpinCHopfFirstAxisBase,
    primitiveSpinCHopfFirstAxisCover,
    firstSphereWitnessCoordinate_zero,
    primitiveSpinCHopfFirstAxisValue_gamma_zero] using hFormula

/-- At the first axis, each nonaligned positive coordinate is Clifford
tangential. -/
theorem primitiveSpinCHopfFirstAxisPositiveTangential
    (coordinate : Fin 3) (hCoordinate : coordinate ≠ 0)
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfFirstAxisIndex period hPeriod)
        (primitiveSpinCHopfFirstAxisBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
        (primitiveSpinCHopfFirstAxisValue period hPeriod sector mode) := by
  have hCoordinateZero :
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
        (primitiveSpinCHopfFirstAxisBase period hPeriod) = 0 := by
    fin_cases coordinate <;> simp_all [firstSphereWitnessCoordinate_zero,
      firstSphereWitnessCoordinate_one, firstSphereWitnessCoordinate_two]
  have hFormula :=
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_at_mk
      period hPeriod
      (primitiveSpinCHopfFirstAxisCover period hPeriod) .north
      (by
        simpa [primitiveSpinCHopfFirstAxisCover,
          firstSphereComplexWitnessCover] using
          primitiveSpinCGeometricZeroModeWitnessBase_mem
            period hPeriod 0 |>.2)
      coordinate sector mode
  simpa [primitiveSpinCHopfFirstAxisValue,
    primitiveSpinCHopfFirstAxisIndex,
    primitiveSpinCHopfFirstAxisBase,
    primitiveSpinCHopfFirstAxisCover, hCoordinateZero] using hFormula

/-- At the second axis, the aligned positive coordinate is purely radial. -/
theorem primitiveSpinCHopfSecondAxisPositiveAligned
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfSecondAxisIndex period hPeriod)
        (primitiveSpinCHopfSecondAxisBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 1 sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfSecondAxisValue period hPeriod sector mode := by
  have hFormula :=
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_at_mk
      period hPeriod
      (primitiveSpinCHopfSecondAxisCover period hPeriod) .north
      (primitiveSpinCHopfSecondAxis_mem_north period hPeriod)
      1 sector mode
  simpa [primitiveSpinCHopfSecondAxisIndex,
    primitiveSpinCHopfSecondAxisBase,
    primitiveSpinCHopfSecondAxisValue,
    primitiveSpinCHopfSecondAxisCoordinate_one,
    primitiveSpinCHopfSecondAxisValue_gamma_one] using hFormula

/-- At the second axis, each nonaligned positive coordinate is Clifford
tangential. -/
theorem primitiveSpinCHopfSecondAxisPositiveTangential
    (coordinate : Fin 3) (hCoordinate : coordinate ≠ 1)
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfSecondAxisIndex period hPeriod)
        (primitiveSpinCHopfSecondAxisBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
        (primitiveSpinCHopfSecondAxisValue period hPeriod sector mode) := by
  have hCoordinateZero :
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
        (primitiveSpinCHopfSecondAxisBase period hPeriod) = 0 := by
    fin_cases coordinate <;> simp_all [primitiveSpinCHopfSecondAxisCoordinate_zero,
      primitiveSpinCHopfSecondAxisCoordinate_one,
      primitiveSpinCHopfSecondAxisCoordinate_two]
  have hFormula :=
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_at_mk
      period hPeriod
      (primitiveSpinCHopfSecondAxisCover period hPeriod) .north
      (primitiveSpinCHopfSecondAxis_mem_north period hPeriod)
      coordinate sector mode
  simpa [primitiveSpinCHopfSecondAxisIndex,
    primitiveSpinCHopfSecondAxisBase,
    primitiveSpinCHopfSecondAxisValue, hCoordinateZero] using hFormula

/-- At the first axis, the aligned negative coordinate is purely radial. -/
theorem primitiveSpinCHopfFirstAxisNegativeAligned
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfFirstAxisIndex period hPeriod)
        (primitiveSpinCHopfFirstAxisBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 0 sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfFirstAxisValue period hPeriod sector mode := by
  have hFormula :=
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_at_mk
      period hPeriod
      (primitiveSpinCHopfFirstAxisCover period hPeriod) .north
      (by
        simpa [primitiveSpinCHopfFirstAxisCover,
          firstSphereComplexWitnessCover] using
          primitiveSpinCGeometricZeroModeWitnessBase_mem
            period hPeriod 0 |>.2)
      0 sector mode
  simpa [primitiveSpinCHopfFirstAxisValue,
    primitiveSpinCHopfFirstAxisIndex,
    primitiveSpinCHopfFirstAxisBase,
    primitiveSpinCHopfFirstAxisCover,
    firstSphereWitnessCoordinate_zero,
    primitiveSpinCHopfFirstAxisValue_gamma_zero] using hFormula

/-- At the first axis, each nonaligned negative coordinate is Clifford
tangential. -/
theorem primitiveSpinCHopfFirstAxisNegativeTangential
    (coordinate : Fin 3) (hCoordinate : coordinate ≠ 0)
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfFirstAxisIndex period hPeriod)
        (primitiveSpinCHopfFirstAxisBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
        (primitiveSpinCHopfFirstAxisValue period hPeriod sector mode) := by
  have hCoordinateZero :
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
        (primitiveSpinCHopfFirstAxisBase period hPeriod) = 0 := by
    fin_cases coordinate <;> simp_all [firstSphereWitnessCoordinate_zero,
      firstSphereWitnessCoordinate_one, firstSphereWitnessCoordinate_two]
  have hFormula :=
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_at_mk
      period hPeriod
      (primitiveSpinCHopfFirstAxisCover period hPeriod) .north
      (by
        simpa [primitiveSpinCHopfFirstAxisCover,
          firstSphereComplexWitnessCover] using
          primitiveSpinCGeometricZeroModeWitnessBase_mem
            period hPeriod 0 |>.2)
      coordinate sector mode
  simpa [primitiveSpinCHopfFirstAxisValue,
    primitiveSpinCHopfFirstAxisIndex,
    primitiveSpinCHopfFirstAxisBase,
    primitiveSpinCHopfFirstAxisCover, hCoordinateZero] using hFormula

/-- At the second axis, the aligned negative coordinate is purely radial. -/
theorem primitiveSpinCHopfSecondAxisNegativeAligned
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfSecondAxisIndex period hPeriod)
        (primitiveSpinCHopfSecondAxisBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 1 sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        primitiveSpinCHopfSecondAxisValue period hPeriod sector mode := by
  have hFormula :=
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_at_mk
      period hPeriod
      (primitiveSpinCHopfSecondAxisCover period hPeriod) .north
      (primitiveSpinCHopfSecondAxis_mem_north period hPeriod)
      1 sector mode
  simpa [primitiveSpinCHopfSecondAxisIndex,
    primitiveSpinCHopfSecondAxisBase,
    primitiveSpinCHopfSecondAxisValue,
    primitiveSpinCHopfSecondAxisCoordinate_one,
    primitiveSpinCHopfSecondAxisValue_gamma_one] using hFormula

/-- At the second axis, each nonaligned negative coordinate is Clifford
tangential. -/
theorem primitiveSpinCHopfSecondAxisNegativeTangential
    (coordinate : Fin 3) (hCoordinate : coordinate ≠ 1)
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfSecondAxisIndex period hPeriod)
        (primitiveSpinCHopfSecondAxisBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
        (primitiveSpinCHopfSecondAxisValue period hPeriod sector mode) := by
  have hCoordinateZero :
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
        (primitiveSpinCHopfSecondAxisBase period hPeriod) = 0 := by
    fin_cases coordinate <;> simp_all [primitiveSpinCHopfSecondAxisCoordinate_zero,
      primitiveSpinCHopfSecondAxisCoordinate_one,
      primitiveSpinCHopfSecondAxisCoordinate_two]
  have hFormula :=
    primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_at_mk
      period hPeriod
      (primitiveSpinCHopfSecondAxisCover period hPeriod) .north
      (primitiveSpinCHopfSecondAxis_mem_north period hPeriod)
      coordinate sector mode
  simpa [primitiveSpinCHopfSecondAxisIndex,
    primitiveSpinCHopfSecondAxisBase,
    primitiveSpinCHopfSecondAxisValue, hCoordinateZero] using hFormula

/-- Consolidated two-axis geometric witness package. -/
theorem primitiveSpinCHopfFirstSphereTwoAxisWitness_closed
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstAxisValue period hPeriod sector mode ≠ 0 ∧
      primitiveSpinCHopfSecondAxisValue period hPeriod sector mode ≠ 0 ∧
      d9DoubledMatterFiberCliffordGammaCLM 0
          (primitiveSpinCHopfFirstAxisValue period hPeriod sector mode) =
        d9PrimitiveSpinCImaginaryAction
          (primitiveSpinCHopfFirstAxisValue period hPeriod sector mode) ∧
      d9DoubledMatterFiberCliffordGammaCLM 1
          (primitiveSpinCHopfSecondAxisValue period hPeriod sector mode) =
        d9PrimitiveSpinCImaginaryAction
          (primitiveSpinCHopfSecondAxisValue period hPeriod sector mode) :=
  ⟨primitiveSpinCHopfFirstAxisValue_ne_zero
      period hPeriod sector mode,
    primitiveSpinCHopfSecondAxisValue_ne_zero
      period hPeriod sector mode,
    primitiveSpinCHopfFirstAxisValue_gamma_zero
      period hPeriod sector mode,
    primitiveSpinCHopfSecondAxisValue_gamma_one
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAxisWitness4D
end JanusFormal
