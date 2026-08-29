import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D

/-!
# Multiplicity of the first positive primitive SpinC sphere level

The equatorial Fourier witness separates the three coordinate
eigensections.  In particular, both signs give genuine nonzero states.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
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

private abbrev witnessCover :=
  primitiveSpinCGeometricZeroModeWitnessCover period hPeriod 0

private abbrev witnessBase :=
  primitiveSpinCGeometricZeroModeWitnessBase period hPeriod 0

private abbrev witnessIndex :=
  primitiveSpinCGeometricZeroModeWitnessIndex period hPeriod 0

private abbrev witnessMode
    (sector : NormalRootChoice) (mode : Int) : D9DoubledMatterFiber :=
  primitiveSpinCNormalModeDoubledLift
    period hPeriod sector mode (witnessCover period hPeriod)

@[simp]
theorem firstSphereWitnessCoordinate_zero :
    d9PrimitiveMonopoleBaseCoordinate
        period hPeriod 0 (witnessBase period hPeriod) = 1 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)) 0 = 1
  rw [primitiveSpinCGeometricZeroModeWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCGeometricZeroModeWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

@[simp]
theorem firstSphereWitnessCoordinate_one :
    d9PrimitiveMonopoleBaseCoordinate
        period hPeriod 1 (witnessBase period hPeriod) = 0 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)) 1 = 0
  rw [primitiveSpinCGeometricZeroModeWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCGeometricZeroModeWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

@[simp]
theorem firstSphereWitnessCoordinate_two :
    d9PrimitiveMonopoleBaseCoordinate
        period hPeriod 2 (witnessBase period hPeriod) = 0 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCGeometricZeroModeWitnessBase
            period hPeriod 0)) 2 = 0
  rw [primitiveSpinCGeometricZeroModeWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCGeometricZeroModeWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

theorem witnessMode_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    witnessMode period hPeriod sector mode ≠ 0 := by
  intro hZero
  have hCoefficient := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector)
    hZero
  cases sector <;>
    simp [witnessMode, witnessCover,
      primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      normalRootSpinFramePhase, normalRootSpinFramePhaseAngle,
      primitiveSpinCGeometricZeroModeWitnessCover,
      primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap,
      d9MatterGammaPositiveCoefficientLinearMap,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      ambientHalfGammaPositiveEigenvector] at hCoefficient

theorem firstSphereCoordinateLocalCoordinate_witness
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode) =
      d9PrimitiveMonopoleBaseCoordinate
          period hPeriod coordinate (witnessBase period hPeriod) •
        ((2 : Real) • witnessMode period hPeriod sector mode) := by
  have hMem :=
    primitiveSpinCGeometricZeroModeWitnessBase_mem period hPeriod 0
  have hZero :=
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_witness
      period hPeriod sector mode 0
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
    period hPeriod sector mode
    (witnessIndex period hPeriod) (witnessBase period hPeriod) hMem] at hZero
  calc
    _ =
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode).localValue
          (witnessIndex period hPeriod) (witnessBase period hPeriod) := by
      unfold primitiveSpinCHopfFirstSphereCoordinateSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod) hMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (witnessIndex period hPeriod) (witnessBase period hPeriod) hMem
    _ = _ := by
      change
        d9PrimitiveMonopoleBaseCoordinate
            period hPeriod coordinate (witnessBase period hPeriod) •
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (witnessIndex period hPeriod) (witnessBase period hPeriod) =
          _
      rw [hZero]

theorem firstSphereTangentialLocalCoordinate_witness
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          ((2 : Real) • witnessMode period hPeriod sector mode) -
        d9PrimitiveMonopoleBaseCoordinate
            period hPeriod coordinate (witnessBase period hPeriod) •
          d9PrimitiveSpinCImaginaryAction
            ((2 : Real) • witnessMode period hPeriod sector mode) := by
  have hMem :=
    primitiveSpinCGeometricZeroModeWitnessBase_mem period hPeriod 0
  have hZero :=
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode_witness
      period hPeriod sector mode 0
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
    period hPeriod sector mode
    (witnessIndex period hPeriod) (witnessBase period hPeriod) hMem] at hZero
  calc
    _ =
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode).localValue
          (witnessIndex period hPeriod) (witnessBase period hPeriod) := by
      unfold primitiveSpinCHopfFirstSphereTangentialSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod) hMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (witnessIndex period hPeriod) (witnessBase period hPeriod) hMem
    _ = _ := by
      rw [
        primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily_localValue,
        hZero]
      rfl

theorem firstSpherePositiveLocalCoordinate_witness
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        (d9PrimitiveMonopoleBaseCoordinate
            period hPeriod coordinate (witnessBase period hPeriod) •
          ((2 : Real) • witnessMode period hPeriod sector mode)) +
      (d9DoubledMatterFiberCliffordGammaCLM coordinate
          ((2 : Real) • witnessMode period hPeriod sector mode) -
        d9PrimitiveMonopoleBaseCoordinate
            period hPeriod coordinate (witnessBase period hPeriod) •
          d9PrimitiveSpinCImaginaryAction
            ((2 : Real) • witnessMode period hPeriod sector mode)) := by
  unfold primitiveSpinCHopfFirstSpherePositiveSection
  rw [map_add, map_smul,
    firstSphereCoordinateLocalCoordinate_witness,
    firstSphereTangentialLocalCoordinate_witness]

theorem firstSphereNegativeLocalCoordinate_witness
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        (d9PrimitiveMonopoleBaseCoordinate
            period hPeriod coordinate (witnessBase period hPeriod) •
          ((2 : Real) • witnessMode period hPeriod sector mode)) +
      (d9DoubledMatterFiberCliffordGammaCLM coordinate
          ((2 : Real) • witnessMode period hPeriod sector mode) -
        d9PrimitiveMonopoleBaseCoordinate
            period hPeriod coordinate (witnessBase period hPeriod) •
          d9PrimitiveSpinCImaginaryAction
            ((2 : Real) • witnessMode period hPeriod sector mode)) := by
  unfold primitiveSpinCHopfFirstSphereNegativeSection
  rw [map_add, map_smul,
    firstSphereCoordinateLocalCoordinate_witness,
    firstSphereTangentialLocalCoordinate_witness]

theorem firstSpherePositiveCoefficient_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
        normalRootLeviCivitaCorrectedFrequency period sector mode ≠ 0 := by
  intro hZero
  have hSquare :=
    primitiveSpinCHopfFirstSphereDiracFrequency_sq period sector mode
  have hEqual :
      primitiveSpinCHopfFirstSphereDiracFrequency period sector mode =
        normalRootLeviCivitaCorrectedFrequency period sector mode :=
    sub_eq_zero.mp hZero
  rw [hEqual] at hSquare
  nlinarith

theorem firstSphereNegativeCoefficient_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    -primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
        normalRootLeviCivitaCorrectedFrequency period sector mode ≠ 0 := by
  intro hZero
  have hSquare :=
    primitiveSpinCHopfFirstSphereDiracFrequency_sq period sector mode
  have hEqual :
      primitiveSpinCHopfFirstSphereDiracFrequency period sector mode =
        -normalRootLeviCivitaCorrectedFrequency period sector mode := by
    linarith
  rw [hEqual] at hSquare
  nlinarith

theorem clifford_witnessMode_ne_zero
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberCliffordGammaCLM coordinate
        ((2 : Real) • witnessMode period hPeriod sector mode) ≠ 0 := by
  intro hZero
  have hSquare :=
    d9DoubledMatterFiberCliffordGammaCLM_sq coordinate
      ((2 : Real) • witnessMode period hPeriod sector mode)
  rw [hZero, map_zero] at hSquare
  have hScaled :
      (2 : Real) • witnessMode period hPeriod sector mode ≠ 0 :=
    smul_ne_zero (by norm_num) (witnessMode_ne_zero period hPeriod sector mode)
  exact hScaled (neg_eq_zero.mp hSquare.symm)

theorem firstSpherePositiveLocalCoordinate_zero :
    ∀ (sector : NormalRootChoice) (mode : Int),
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 0 sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        ((2 : Real) • witnessMode period hPeriod sector mode) := by
  intro sector mode
  rw [firstSpherePositiveLocalCoordinate_witness,
    firstSphereWitnessCoordinate_zero]
  simp only [one_smul]
  rw [map_smul,
    primitiveSpinCNormalModeDoubledLift_gamma_zero,
    map_smul]
  simp

theorem firstSpherePositiveLocalCoordinate_one :
    ∀ (sector : NormalRootChoice) (mode : Int),
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 1 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 1
        ((2 : Real) • witnessMode period hPeriod sector mode) := by
  intro sector mode
  rw [firstSpherePositiveLocalCoordinate_witness,
    firstSphereWitnessCoordinate_one]
  simp

theorem firstSpherePositiveLocalCoordinate_two :
    ∀ (sector : NormalRootChoice) (mode : Int),
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 2 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 2
        ((2 : Real) • witnessMode period hPeriod sector mode) := by
  intro sector mode
  rw [firstSpherePositiveLocalCoordinate_witness,
    firstSphereWitnessCoordinate_two]
  simp

theorem firstSphereNegativeLocalCoordinate_zero :
    ∀ (sector : NormalRootChoice) (mode : Int),
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 0 sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        ((2 : Real) • witnessMode period hPeriod sector mode) := by
  intro sector mode
  rw [firstSphereNegativeLocalCoordinate_witness,
    firstSphereWitnessCoordinate_zero]
  simp only [one_smul]
  rw [map_smul,
    primitiveSpinCNormalModeDoubledLift_gamma_zero,
    map_smul]
  simp

theorem firstSphereNegativeLocalCoordinate_one :
    ∀ (sector : NormalRootChoice) (mode : Int),
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 1 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 1
        ((2 : Real) • witnessMode period hPeriod sector mode) := by
  intro sector mode
  rw [firstSphereNegativeLocalCoordinate_witness,
    firstSphereWitnessCoordinate_one]
  simp

theorem firstSphereNegativeLocalCoordinate_two :
    ∀ (sector : NormalRootChoice) (mode : Int),
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod (witnessIndex period hPeriod)
        (witnessBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 2 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 2
        ((2 : Real) • witnessMode period hPeriod sector mode) := by
  intro sector mode
  rw [firstSphereNegativeLocalCoordinate_witness,
    firstSphereWitnessCoordinate_two]
  simp

theorem primitiveSpinCHopfFirstSpherePositiveSection_ne_zero
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSpherePositiveSection
        period hPeriod coordinate sector mode ≠ 0 := by
  intro hZero
  have hLocal := congrArg
    (primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod (witnessIndex period hPeriod)
      (witnessBase period hPeriod)) hZero
  fin_cases coordinate
  · have hLocal' :
        primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod (witnessIndex period hPeriod)
            (witnessBase period hPeriod)
            (primitiveSpinCHopfFirstSpherePositiveSection
              period hPeriod 0 sector mode) = 0 := by
      simpa using hLocal
    rw [firstSpherePositiveLocalCoordinate_zero] at hLocal'
    exact
      (smul_ne_zero
        (firstSpherePositiveCoefficient_ne_zero period sector mode)
        (smul_ne_zero (by norm_num)
          (witnessMode_ne_zero period hPeriod sector mode))) hLocal'
  · have hLocal' :
        primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod (witnessIndex period hPeriod)
            (witnessBase period hPeriod)
            (primitiveSpinCHopfFirstSpherePositiveSection
              period hPeriod 1 sector mode) = 0 := by
      simpa using hLocal
    rw [firstSpherePositiveLocalCoordinate_one] at hLocal'
    exact clifford_witnessMode_ne_zero
      period hPeriod 1 sector mode hLocal'
  · have hLocal' :
        primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod (witnessIndex period hPeriod)
            (witnessBase period hPeriod)
            (primitiveSpinCHopfFirstSpherePositiveSection
              period hPeriod 2 sector mode) = 0 := by
      simpa using hLocal
    rw [firstSpherePositiveLocalCoordinate_two] at hLocal'
    exact clifford_witnessMode_ne_zero
      period hPeriod 2 sector mode hLocal'

theorem primitiveSpinCHopfFirstSphereNegativeSection_ne_zero
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfFirstSphereNegativeSection
        period hPeriod coordinate sector mode ≠ 0 := by
  intro hZero
  have hLocal := congrArg
    (primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod (witnessIndex period hPeriod)
      (witnessBase period hPeriod)) hZero
  fin_cases coordinate
  · have hLocal' :
        primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod (witnessIndex period hPeriod)
            (witnessBase period hPeriod)
            (primitiveSpinCHopfFirstSphereNegativeSection
              period hPeriod 0 sector mode) = 0 := by
      simpa using hLocal
    rw [firstSphereNegativeLocalCoordinate_zero] at hLocal'
    exact
      (smul_ne_zero
        (firstSphereNegativeCoefficient_ne_zero period sector mode)
        (smul_ne_zero (by norm_num)
          (witnessMode_ne_zero period hPeriod sector mode))) hLocal'
  · have hLocal' :
        primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod (witnessIndex period hPeriod)
            (witnessBase period hPeriod)
            (primitiveSpinCHopfFirstSphereNegativeSection
              period hPeriod 1 sector mode) = 0 := by
      simpa using hLocal
    rw [firstSphereNegativeLocalCoordinate_one] at hLocal'
    exact clifford_witnessMode_ne_zero
      period hPeriod 1 sector mode hLocal'
  · have hLocal' :
        primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod (witnessIndex period hPeriod)
            (witnessBase period hPeriod)
            (primitiveSpinCHopfFirstSphereNegativeSection
              period hPeriod 2 sector mode) = 0 := by
      simpa using hLocal
    rw [firstSphereNegativeLocalCoordinate_two] at hLocal'
    exact clifford_witnessMode_ne_zero
      period hPeriod 2 sector mode hLocal'

theorem witnessMode_halfSpinor
    (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (witnessMode period hPeriod sector mode) =
      match sector with
      | .positiveQuarter => (ambientHalfGammaPositiveEigenvector, 0)
      | .negativeQuarter => (0, ambientHalfGammaPositiveEigenvector) := by
  have zero_apply (choice : NormalRootChoice)
      (point : MappingTorusCover (ThroatData period hPeriod)) :
      (0 : SmoothThroatMatterSpinorLift period hPeriod choice)
          point = 0 := rfl
  cases sector <;>
    apply Prod.ext <;>
    funext index <;>
    fin_cases index <;>
    simp [witnessMode, witnessCover,
      primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      normalRootSpinFramePhase, normalRootSpinFramePhaseAngle,
      primitiveSpinCGeometricZeroModeWitnessCover,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      ambientHalfGammaPositiveEigenvector, zero_apply]

@[simp]
theorem witnessMode_sectorCoefficient
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (witnessMode period hPeriod sector mode) = 1 := by
  cases sector
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (witnessMode period hPeriod .positiveQuarter mode)).1 0 = 1
    rw [witnessMode_halfSpinor]
    rfl
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (witnessMode period hPeriod .negativeQuarter mode)).2 0 = 1
    rw [witnessMode_halfSpinor]
    rfl

@[simp]
theorem witnessMode_oppositeCoefficient
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap
        (oppositeRoot sector)
        (witnessMode period hPeriod sector mode) = 0 := by
  cases sector
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (witnessMode period hPeriod .positiveQuarter mode)).2 0 = 0
    rw [witnessMode_halfSpinor]
    rfl
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (witnessMode period hPeriod .negativeQuarter mode)).1 0 = 0
    rw [witnessMode_halfSpinor]
    rfl

@[simp]
theorem witnessMode_gamma_one_sectorCoefficient
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (d9DoubledMatterFiberCliffordGammaCLM 1
          (witnessMode period hPeriod sector mode)) = 0 := by
  cases sector
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 1
          (witnessMode period hPeriod .positiveQuarter mode))).1 0 = 0
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_one,
      witnessMode_halfSpinor]
    simp
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 1
          (witnessMode period hPeriod .negativeQuarter mode))).2 0 = 0
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_one,
      witnessMode_halfSpinor]
    simp

@[simp]
theorem witnessMode_gamma_two_sectorCoefficient
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (witnessMode period hPeriod sector mode)) = 0 := by
  cases sector
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (witnessMode period hPeriod .positiveQuarter mode))).1 0 = 0
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_two,
      witnessMode_halfSpinor]
    simp
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (witnessMode period hPeriod .negativeQuarter mode))).2 0 = 0
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_two,
      witnessMode_halfSpinor]
    simp

theorem witnessMode_gamma_one_oppositeCoefficient
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap
        (oppositeRoot sector)
        (d9DoubledMatterFiberCliffordGammaCLM 1
          (witnessMode period hPeriod sector mode)) =
      match sector with
      | .positiveQuarter => -Complex.I
      | .negativeQuarter => Complex.I := by
  cases sector
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 1
          (witnessMode period hPeriod .positiveQuarter mode))).2 0 =
        -Complex.I
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_one,
      witnessMode_halfSpinor]
    simp [ambientHalfGammaPositiveEigenvector]
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 1
          (witnessMode period hPeriod .negativeQuarter mode))).1 0 =
        Complex.I
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_one,
      witnessMode_halfSpinor]
    simp [ambientHalfGammaPositiveEigenvector]

theorem witnessMode_gamma_two_oppositeCoefficient
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap
        (oppositeRoot sector)
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (witnessMode period hPeriod sector mode)) =
      match sector with
      | .positiveQuarter => -1
      | .negativeQuarter => 1 := by
  cases sector
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (witnessMode period hPeriod .positiveQuarter mode))).2 0 = -1
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_two,
      witnessMode_halfSpinor]
    simp [ambientHalfGammaPositiveEigenvector]
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (witnessMode period hPeriod .negativeQuarter mode))).1 0 = 1
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_two,
      witnessMode_halfSpinor]
    simp [ambientHalfGammaPositiveEigenvector]

private theorem firstSphereWitnessFamily_linearIndependent
    (sector : NormalRootChoice) (mode : Int) (zeroCoefficient : Real)
    (hZeroCoefficient : zeroCoefficient ≠ 0)
    (family :
      Fin 3 →
        D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter)
    (hZero :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod (witnessIndex period hPeriod)
          (witnessBase period hPeriod) (family 0) =
        zeroCoefficient •
          ((2 : Real) • witnessMode period hPeriod sector mode))
    (hOne :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod (witnessIndex period hPeriod)
          (witnessBase period hPeriod) (family 1) =
        d9DoubledMatterFiberCliffordGammaCLM 1
          ((2 : Real) • witnessMode period hPeriod sector mode))
    (hTwo :
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod (witnessIndex period hPeriod)
          (witnessBase period hPeriod) (family 2) =
        d9DoubledMatterFiberCliffordGammaCLM 2
          ((2 : Real) • witnessMode period hPeriod sector mode)) :
    LinearIndependent Real family := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients hSum coordinate
  let localCoordinate :=
    primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod (witnessIndex period hPeriod)
      (witnessBase period hPeriod)
  have hLocal := congrArg localCoordinate hSum
  simp only [map_sum, map_smul, map_zero] at hLocal
  have hExpand :
      (∑ index : Fin 3, coefficients index • localCoordinate (family index)) =
        coefficients 0 • localCoordinate (family 0) +
          coefficients 1 • localCoordinate (family 1) +
          coefficients 2 • localCoordinate (family 2) := by
    simp [Fin.sum_univ_succ]
    abel
  rw [hExpand, hZero, hOne, hTwo] at hLocal
  have hSame := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector)
    hLocal
  have hSame' :
      coefficients 0 •
          (zeroCoefficient • ((2 : Real) • (1 : Complex))) = 0 := by
    simpa only [map_add, map_smul, map_zero,
      witnessMode_sectorCoefficient,
      witnessMode_gamma_one_sectorCoefficient,
      witnessMode_gamma_two_sectorCoefficient,
      smul_zero, add_zero] using hSame
  have hCoefficientZero : coefficients 0 = 0 := by
    by_contra hCoefficient
    exact
      (smul_ne_zero hCoefficient
        (smul_ne_zero hZeroCoefficient
          (smul_ne_zero (by norm_num) one_ne_zero))) hSame'
  have hOpposite := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap
      (oppositeRoot sector)) hLocal
  have hOpposite' :
      coefficients 1 •
          ((2 : Real) •
            (match sector with
            | .positiveQuarter => -Complex.I
            | .negativeQuarter => Complex.I)) +
        coefficients 2 •
          ((2 : Real) •
            (match sector with
            | .positiveQuarter => (-1 : Complex)
            | .negativeQuarter => 1)) = 0 := by
    simpa only [map_add, map_smul, map_zero,
      witnessMode_oppositeCoefficient,
      witnessMode_gamma_one_oppositeCoefficient,
      witnessMode_gamma_two_oppositeCoefficient,
      smul_zero, zero_smul, zero_add] using hOpposite
  have hReal := congrArg Complex.re hOpposite'
  have hImaginary := congrArg Complex.im hOpposite'
  have hCoefficientOne : coefficients 1 = 0 := by
    cases sector <;>
      norm_num [Complex.real_smul] at hImaginary <;>
      linarith
  have hCoefficientTwo : coefficients 2 = 0 := by
    cases sector <;>
      norm_num [Complex.real_smul] at hReal <;>
      linarith
  fin_cases coordinate
  · exact hCoefficientZero
  · exact hCoefficientOne
  · exact hCoefficientTwo

theorem primitiveSpinCHopfFirstSpherePositiveSections_linearIndependent
    (sector : NormalRootChoice) (mode : Int) :
    LinearIndependent Real
      (fun coordinate : Fin 3 =>
        primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) := by
  apply firstSphereWitnessFamily_linearIndependent
    period hPeriod sector mode
    (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
      normalRootLeviCivitaCorrectedFrequency period sector mode)
    (firstSpherePositiveCoefficient_ne_zero period sector mode)
  · exact firstSpherePositiveLocalCoordinate_zero
      period hPeriod sector mode
  · exact firstSpherePositiveLocalCoordinate_one
      period hPeriod sector mode
  · exact firstSpherePositiveLocalCoordinate_two
      period hPeriod sector mode

theorem primitiveSpinCHopfFirstSphereNegativeSections_linearIndependent
    (sector : NormalRootChoice) (mode : Int) :
    LinearIndependent Real
      (fun coordinate : Fin 3 =>
        primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) := by
  apply firstSphereWitnessFamily_linearIndependent
    period hPeriod sector mode
    (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
      normalRootLeviCivitaCorrectedFrequency period sector mode)
    (firstSphereNegativeCoefficient_ne_zero period sector mode)
  · exact firstSphereNegativeLocalCoordinate_zero
      period hPeriod sector mode
  · exact firstSphereNegativeLocalCoordinate_one
      period hPeriod sector mode
  · exact firstSphereNegativeLocalCoordinate_two
      period hPeriod sector mode

@[simp]
theorem primitiveSphereModeDegeneracy_one :
    primitiveSphereModeDegeneracy 1 = 3 := by
  norm_num [primitiveSphereModeDegeneracy]

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
end JanusFormal
