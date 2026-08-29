import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
import Mathlib.Tactic

/-!
# First-sphere eigensections at the antipodal witness

The geometric antipodal Hopf value is now available as an actual local
coordinate of the global zero mode.  This gate evaluates the coordinate and
tangential first-sphere constructions at that point.

The antipodal sphere coordinates are `(-1,0,0)`.  Consequently the two
coordinates tangent to the equator reduce exactly to `Γ₁ ψ₋` and `Γ₂ ψ₋`,
where `ψ₋` is the nonzero opposite-frame Hopf value.  The preceding gate gives
`Γ₁ ψ₋ = -J Γ₂ ψ₋`; these are the geometric representatives of the second
complex witness.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalLocal4D

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
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalWitness4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereWitnessFiber4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
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

/-- Time-zero antipodal lift. -/
abbrev primitiveSpinCHopfAntipodalZeroCover :
    ThroatCover period hPeriod :=
  primitiveSpinCHopfAntipodalWitnessCover period hPeriod 0

/-- Time-zero antipodal quotient point. -/
abbrev primitiveSpinCHopfAntipodalZeroBase :
    ThroatBase period hPeriod :=
  primitiveSpinCHopfAntipodalWitnessBase period hPeriod 0

/-- Time-zero antipodal joint chart. -/
abbrev primitiveSpinCHopfAntipodalZeroIndex :
    D9PrimitiveSpinCIndex period hPeriod :=
  primitiveSpinCHopfAntipodalWitnessIndex period hPeriod 0

/-- Normal-mode fiber at the time-zero antipodal lift. -/
def primitiveSpinCHopfAntipodalNormalMode
    (sector : NormalRootChoice) (mode : Int) : D9DoubledMatterFiber :=
  primitiveSpinCNormalModeDoubledLift
    period hPeriod sector mode
    (primitiveSpinCHopfAntipodalZeroCover period hPeriod)

/-- Complete opposite-frame Hopf value at the antipodal witness. -/
def primitiveSpinCHopfAntipodalValue
    (sector : NormalRootChoice) (mode : Int) : D9DoubledMatterFiber :=
  primitiveSpinCHopfAntipodalWitnessFiber sector
    (primitiveSpinCHopfAntipodalNormalMode
      period hPeriod sector mode)

@[simp]
theorem primitiveSpinCHopfAntipodalCoordinate_zero :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 0
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod) = -1 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod)) 0 = -1
  rw [primitiveSpinCHopfAntipodalZeroBase,
    primitiveSpinCHopfAntipodalWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCHopfAntipodalWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

@[simp]
theorem primitiveSpinCHopfAntipodalCoordinate_one :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 1
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod) = 0 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod)) 1 = 0
  rw [primitiveSpinCHopfAntipodalZeroBase,
    primitiveSpinCHopfAntipodalWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCHopfAntipodalWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

@[simp]
theorem primitiveSpinCHopfAntipodalCoordinate_two :
    d9PrimitiveMonopoleBaseCoordinate period hPeriod 2
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod) = 0 := by
  change
    monopoleSphereCoordinate
        (d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod)) 2 = 0
  rw [primitiveSpinCHopfAntipodalZeroBase,
    primitiveSpinCHopfAntipodalWitnessBase,
    d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCHopfAntipodalWitnessCover_sphere]
  simp [monopoleEquator, monopoleSphereCoordinate]

/-- Explicit time-zero half-spinor value of the antipodal normal mode. -/
theorem primitiveSpinCHopfAntipodalNormalMode_halfSpinor
    (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (primitiveSpinCHopfAntipodalNormalMode
          period hPeriod sector mode) =
      match sector with
      | .positiveQuarter => (ambientHalfGammaPositiveEigenvector, 0)
      | .negativeQuarter => (0, ambientHalfGammaPositiveEigenvector) := by
  have zero_apply (choice : NormalRootChoice)
      (point : ThroatCover period hPeriod) :
      (0 : SmoothThroatMatterSpinorLift period hPeriod choice)
          point = 0 := rfl
  cases sector <;>
    apply Prod.ext <;>
    funext index <;>
    fin_cases index <;>
    simp [primitiveSpinCHopfAntipodalNormalMode,
      primitiveSpinCHopfAntipodalZeroCover,
      primitiveSpinCHopfAntipodalWitnessCover,
      primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      normalRootSpinFramePhase, normalRootSpinFramePhaseAngle,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      ambientHalfGammaPositiveEigenvector, zero_apply]

/-- The antipodal normal-mode fiber is nonzero. -/
theorem primitiveSpinCHopfAntipodalNormalMode_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfAntipodalNormalMode
        period hPeriod sector mode ≠ 0 := by
  intro hZero
  have hHalf := congrArg
    d9DoubledMatterFiberHalfSpinorLinearEquiv hZero
  rw [primitiveSpinCHopfAntipodalNormalMode_halfSpinor] at hHalf
  cases sector with
  | positiveQuarter =>
      have hCoordinate := congrArg
        (fun pair : AmbientHalfSpinor2 × AmbientHalfSpinor2 => pair.1 0)
        hHalf
      simp [ambientHalfGammaPositiveEigenvector] at hCoordinate
  | negativeQuarter =>
      have hCoordinate := congrArg
        (fun pair : AmbientHalfSpinor2 × AmbientHalfSpinor2 => pair.2 0)
        hHalf
      simp [ambientHalfGammaPositiveEigenvector] at hCoordinate

/-- Clifford multiplication by `Γ₂` preserves nonvanishing. -/
theorem primitiveSpinCHopfAntipodalNormalMode_gammaTwo_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberCliffordGammaCLM 2
        (primitiveSpinCHopfAntipodalNormalMode
          period hPeriod sector mode) ≠ 0 := by
  intro hZero
  have hSquare :=
    d9DoubledMatterFiberCliffordGammaCLM_sq 2
      (primitiveSpinCHopfAntipodalNormalMode
        period hPeriod sector mode)
  rw [hZero, map_zero] at hSquare
  exact primitiveSpinCHopfAntipodalNormalMode_ne_zero
    period hPeriod sector mode (neg_eq_zero.mp hSquare.symm)

/-- The imaginary action preserves nonvanishing. -/
theorem d9PrimitiveSpinCImaginaryAction_ne_zero
    (matter : D9DoubledMatterFiber) (hMatter : matter ≠ 0) :
    d9PrimitiveSpinCImaginaryAction matter ≠ 0 := by
  intro hZero
  have hApplied := congrArg d9PrimitiveSpinCImaginaryAction hZero
  rw [d9PrimitiveSpinCImaginaryAction_sq, map_zero] at hApplied
  exact hMatter (neg_eq_zero.mp hApplied)

/-- The complete opposite-frame antipodal Hopf value is nonzero. -/
theorem primitiveSpinCHopfAntipodalValue_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfAntipodalValue
        period hPeriod sector mode ≠ 0 := by
  rw [primitiveSpinCHopfAntipodalValue,
    primitiveSpinCHopfAntipodalWitnessFiber_eq]
  exact smul_ne_zero (by norm_num)
    (d9PrimitiveSpinCImaginaryAction_ne_zero
      (d9DoubledMatterFiberCliffordGammaCLM 2
        (primitiveSpinCHopfAntipodalNormalMode
          period hPeriod sector mode))
      (primitiveSpinCHopfAntipodalNormalMode_gammaTwo_ne_zero
        period hPeriod sector mode))

/-- Its `Γ₂` tangential image is also nonzero. -/
theorem primitiveSpinCHopfAntipodalValue_gammaTwo_ne_zero
    (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberCliffordGammaCLM 2
        (primitiveSpinCHopfAntipodalValue
          period hPeriod sector mode) ≠ 0 := by
  intro hZero
  have hSquare :=
    d9DoubledMatterFiberCliffordGammaCLM_sq 2
      (primitiveSpinCHopfAntipodalValue
        period hPeriod sector mode)
  rw [hZero, map_zero] at hSquare
  exact primitiveSpinCHopfAntipodalValue_ne_zero
    period hPeriod sector mode (neg_eq_zero.mp hSquare.symm)

/-- Local coordinate of a coordinate first-sphere section at the antipodal
witness. -/
theorem primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_antipodal
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
        (primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod coordinate sector mode) =
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod) •
        primitiveSpinCHopfAntipodalValue
          period hPeriod sector mode := by
  have hMem :=
    primitiveSpinCHopfAntipodalWitnessBase_mem period hPeriod 0
  calc
    _ =
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode).localValue
          (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod) := by
      unfold primitiveSpinCHopfFirstSphereCoordinateSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod) hMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereCoordinateLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod) hMem
    _ = _ := by
      change
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalZeroBase period hPeriod) •
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
              (primitiveSpinCHopfAntipodalZeroBase period hPeriod) = _
      rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_antipodal]
      rfl

/-- Local coordinate of a tangential first-sphere section at the antipodal
witness. -/
theorem primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_antipodal
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfAntipodalValue
            period hPeriod sector mode) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalZeroBase period hPeriod) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfAntipodalValue
              period hPeriod sector mode) := by
  have hMem :=
    primitiveSpinCHopfAntipodalWitnessBase_mem period hPeriod 0
  calc
    _ =
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode).localValue
          (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod) := by
      unfold primitiveSpinCHopfFirstSphereTangentialSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod) hMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector mode)
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod) hMem
    _ = _ := by
      rw [primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily_localValue,
        primitiveSpinCHopfZeroModeLocalGaugeFamily_antipodal]
      rfl

/-- Positive first-sphere local-coordinate formula at the antipodal point. -/
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_antipodal
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod coordinate sector mode) =
      (primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalZeroBase period hPeriod) •
          primitiveSpinCHopfAntipodalValue period hPeriod sector mode) +
      (d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfAntipodalValue period hPeriod sector mode) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalZeroBase period hPeriod) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfAntipodalValue
              period hPeriod sector mode)) := by
  unfold primitiveSpinCHopfFirstSpherePositiveSection
  rw [map_add, map_smul,
    primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_antipodal,
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_antipodal]

/-- Negative first-sphere local-coordinate formula at the antipodal point. -/
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_antipodal
    (coordinate : Fin 3) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod coordinate sector mode) =
      (-primitiveSpinCHopfFirstSphereDiracFrequency period sector mode -
          normalRootLeviCivitaCorrectedFrequency period sector mode) •
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalZeroBase period hPeriod) •
          primitiveSpinCHopfAntipodalValue period hPeriod sector mode) +
      (d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCHopfAntipodalValue period hPeriod sector mode) -
        d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate
            (primitiveSpinCHopfAntipodalZeroBase period hPeriod) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCHopfAntipodalValue
              period hPeriod sector mode)) := by
  unfold primitiveSpinCHopfFirstSphereNegativeSection
  rw [map_add, map_smul,
    primitiveSpinCHopfFirstSphereCoordinateLocalCoordinate_antipodal,
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_antipodal]

/-- First tangential positive eigensection at the antipodal witness. -/
@[simp]
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_one_antipodal
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 1 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfAntipodalValue
          period hPeriod sector mode) := by
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_antipodal,
    primitiveSpinCHopfAntipodalCoordinate_one]
  simp

/-- Second tangential positive eigensection at the antipodal witness. -/
@[simp]
theorem primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_two_antipodal
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
        (primitiveSpinCHopfFirstSpherePositiveSection
          period hPeriod 2 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 2
        (primitiveSpinCHopfAntipodalValue
          period hPeriod sector mode) := by
  rw [primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_antipodal,
    primitiveSpinCHopfAntipodalCoordinate_two]
  simp

/-- First tangential negative eigensection at the antipodal witness. -/
@[simp]
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_one_antipodal
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 1 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfAntipodalValue
          period hPeriod sector mode) := by
  rw [primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_antipodal,
    primitiveSpinCHopfAntipodalCoordinate_one]
  simp

/-- Second tangential negative eigensection at the antipodal witness. -/
@[simp]
theorem primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_two_antipodal
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
        (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
        (primitiveSpinCHopfFirstSphereNegativeSection
          period hPeriod 2 sector mode) =
      d9DoubledMatterFiberCliffordGammaCLM 2
        (primitiveSpinCHopfAntipodalValue
          period hPeriod sector mode) := by
  rw [primitiveSpinCHopfFirstSphereNegativeLocalCoordinate_antipodal,
    primitiveSpinCHopfAntipodalCoordinate_two]
  simp

/-- Antipodal tangential coordinates carry the reversed complex relation. -/
theorem primitiveSpinCHopfFirstSphereAntipodalTangential_relation
    (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberCliffordGammaCLM 1
        (primitiveSpinCHopfAntipodalValue
          period hPeriod sector mode) =
      -d9PrimitiveSpinCImaginaryAction
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfAntipodalValue
            period hPeriod sector mode)) :=
  primitiveSpinCHopfAntipodalWitnessFiber_tangential
    sector
    (primitiveSpinCHopfAntipodalNormalMode
      period hPeriod sector mode)
    (primitiveSpinCNormalModeDoubledLift_gamma_one
      period hPeriod sector mode
      (primitiveSpinCHopfAntipodalZeroCover period hPeriod))

/-- Consolidated antipodal first-sphere local package. -/
theorem primitiveSpinCHopfFirstSphereAntipodalLocal_closed
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCHopfAntipodalValue period hPeriod sector mode ≠ 0 ∧
      d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfAntipodalValue
            period hPeriod sector mode) ≠ 0 ∧
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
          (primitiveSpinCHopfFirstSpherePositiveSection
            period hPeriod 1 sector mode) =
        d9DoubledMatterFiberCliffordGammaCLM 1
          (primitiveSpinCHopfAntipodalValue
            period hPeriod sector mode) ∧
      primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCHopfAntipodalZeroIndex period hPeriod)
          (primitiveSpinCHopfAntipodalZeroBase period hPeriod)
          (primitiveSpinCHopfFirstSpherePositiveSection
            period hPeriod 2 sector mode) =
        d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCHopfAntipodalValue
            period hPeriod sector mode) :=
  ⟨primitiveSpinCHopfAntipodalValue_ne_zero
      period hPeriod sector mode,
    primitiveSpinCHopfAntipodalValue_gammaTwo_ne_zero
      period hPeriod sector mode,
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_one_antipodal
      period hPeriod sector mode,
    primitiveSpinCHopfFirstSpherePositiveLocalCoordinate_two_antipodal
      period hPeriod sector mode⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereAntipodalLocal4D
end JanusFormal
