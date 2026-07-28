import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D

/-!
# The third positive primitive SpinC sphere level

This gate constructs the seven real trace-free cubic harmonics on the
quotient two-sphere.  The raw cubic Dirac block is derived recursively from
the already established first- and second-level blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCThirdPositiveSphereDirac4D

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
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D

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

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

/-- Smooth scalar multiplication distributes over section subtraction. -/
theorem d9PrimitiveSpinCRealScalarMulSection_sub
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCRealScalarMulSection
        period hPeriod choice scalar hScalar (first - second) =
      d9PrimitiveSpinCRealScalarMulSection
          period hPeriod choice scalar hScalar first -
        d9PrimitiveSpinCRealScalarMulSection
          period hPeriod choice scalar hScalar second := by
  ext base
  rw [d9PrimitiveSpinCRealScalarMulSection_apply]
  have hState :
      (first - second) base = first base - second base := rfl
  have hResult :
      (d9PrimitiveSpinCRealScalarMulSection
            period hPeriod choice scalar hScalar first -
          d9PrimitiveSpinCRealScalarMulSection
            period hPeriod choice scalar hScalar second) base =
        d9PrimitiveSpinCRealScalarMulSection
              period hPeriod choice scalar hScalar first base -
          d9PrimitiveSpinCRealScalarMulSection
            period hPeriod choice scalar hScalar second base := rfl
  rw [hState, hResult,
    d9PrimitiveSpinCRealScalarMulSection_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply]
  exact smul_sub _ _ _

/-- Clifford multiplication by a fixed scalar differential is additive in
the spinor section. -/
theorem d9PrimitiveSpinCScalarCliffordGradientSection_add
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (first second : SmoothSection period hPeriod) :
    d9PrimitiveSpinCScalarCliffordGradientSection
        period hPeriod .positiveQuarter scalar hScalar (first + second) =
      d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod .positiveQuarter scalar hScalar first +
        d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod .positiveQuarter scalar hScalar second := by
  unfold d9PrimitiveSpinCScalarCliffordGradientSection
  rw [d9PrimitiveSpinCRealScalarMulSection_add,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCRealScalarMulSection_add]
  module

/-- Product of three quotient-sphere coordinates. -/
def primitiveSpinCThirdSphereProductScalar
    (first second third : Fin 3) :
    ThroatBase period hPeriod → Real :=
  fun base =>
    d9PrimitiveMonopoleBaseCoordinate period hPeriod first base *
      d9PrimitiveMonopoleBaseCoordinate period hPeriod second base *
        d9PrimitiveMonopoleBaseCoordinate period hPeriod third base

theorem primitiveSpinCThirdSphereProductScalar_contMDiff
    (first second third : Fin 3) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (primitiveSpinCThirdSphereProductScalar
        period hPeriod first second third) :=
  ((d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod first).mul
    (d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod second)).mul
    (d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod third)

/-- Raw cubic section `nᵢ nⱼ nₖ ψ`. -/
def primitiveSpinCHopfThirdSphereProductSection
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  primitiveSpinCScalarHarmonicSection
    period hPeriod
    (primitiveSpinCThirdSphereProductScalar
      period hPeriod first second third)
    (primitiveSpinCThirdSphereProductScalar_contMDiff
      period hPeriod first second third)
    sector circleMode

/-- Multiplying a raw quadratic section by one coordinate gives the raw
cubic section. -/
theorem primitiveSpinCHopfThirdSphereProductSection_eq_nested
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCRealScalarMulSection
        period hPeriod .positiveQuarter
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
        (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod first)
        (primitiveSpinCHopfSecondSphereProductSection
          period hPeriod second third sector circleMode) =
      primitiveSpinCHopfThirdSphereProductSection
        period hPeriod first second third sector circleMode := by
  ext base
  rw [d9PrimitiveSpinCRealScalarMulSection_apply,
    primitiveSpinCHopfSecondSphereProductSection_apply]
  unfold primitiveSpinCHopfThirdSphereProductSection
    primitiveSpinCScalarHarmonicSection
  rw [d9PrimitiveSpinCRealScalarMulSection_apply]
  unfold primitiveSpinCThirdSphereProductScalar
    primitiveSpinCSecondSphereProductScalar
  module

theorem primitiveSpinCHopfThirdSphereProductSection_swap_first_second
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCHopfThirdSphereProductSection
        period hPeriod first second third sector circleMode =
      primitiveSpinCHopfThirdSphereProductSection
        period hPeriod second first third sector circleMode := by
  ext base
  unfold primitiveSpinCHopfThirdSphereProductSection
    primitiveSpinCScalarHarmonicSection
    primitiveSpinCThirdSphereProductScalar
  rw [d9PrimitiveSpinCRealScalarMulSection_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply]
  ring

theorem primitiveSpinCHopfThirdSphereProductSection_swap_second_third
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCHopfThirdSphereProductSection
        period hPeriod first second third sector circleMode =
      primitiveSpinCHopfThirdSphereProductSection
        period hPeriod first third second sector circleMode := by
  ext base
  unfold primitiveSpinCHopfThirdSphereProductSection
    primitiveSpinCScalarHarmonicSection
    primitiveSpinCThirdSphereProductScalar
  rw [d9PrimitiveSpinCRealScalarMulSection_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply]
  ring

/-- Nested term `nᵢ nⱼ Tₖ` used in the cubic tangential partner. -/
def primitiveSpinCHopfThirdSphereNestedTangentialSection
    (first second tangential : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  d9PrimitiveSpinCRealScalarMulSection
    period hPeriod .positiveQuarter
    (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
    (d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod first)
    (d9PrimitiveSpinCRealScalarMulSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod second)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod second)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod tangential sector circleMode))

/-- Fully symmetrized first-order partner of a raw cubic section. -/
def primitiveSpinCHopfThirdSphereTangentialSection
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  d9PrimitiveSpinCRealScalarMulSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod first)
      (primitiveSpinCHopfSecondSphereTangentialSection
        period hPeriod second third sector circleMode) +
    primitiveSpinCHopfThirdSphereNestedTangentialSection
      period hPeriod second third first sector circleMode

/-- Clifford differentiation of `nⱼnₖψ` by `nᵢ` factors into the remaining
two scalar coordinates times `Tᵢ`. -/
theorem primitiveSpinCHopfSecondSphereProduct_crossGradientFactor
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCScalarCliffordGradientSection
        period hPeriod .positiveQuarter
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
        (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod first)
        (primitiveSpinCHopfSecondSphereProductSection
          period hPeriod second third sector circleMode) =
      primitiveSpinCHopfThirdSphereNestedTangentialSection
        period hPeriod second third first sector circleMode := by
  unfold primitiveSpinCHopfSecondSphereProductSection
  rw [d9PrimitiveSpinCScalarCliffordGradientSection_realScalarMul,
    primitiveSpinCHopfFirstSphereCoordinate_crossGradientFactor]
  rfl

/-- First raw cubic Dirac equation: `D Qᵢⱼₖ = -k Qᵢⱼₖ + Uᵢⱼₖ`. -/
theorem primitiveSpinCHopfThirdSphereProductGeometricDiracOperator_eq
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfThirdSphereProductSection
          period hPeriod first second third sector circleMode) =
      (-normalRootLeviCivitaCorrectedFrequency
          period sector circleMode) •
          primitiveSpinCHopfThirdSphereProductSection
            period hPeriod first second third sector circleMode +
        primitiveSpinCHopfThirdSphereTangentialSection
          period hPeriod first second third sector circleMode := by
  rw [← primitiveSpinCHopfThirdSphereProductSection_eq_nested]
  rw [d9PrimitiveSpinCGeometricDiracOperator_realScalarMul,
    primitiveSpinCHopfSecondSphereProductGeometricDiracOperator_eq,
    d9PrimitiveSpinCRealScalarMulSection_add,
    d9PrimitiveSpinCRealScalarMulSection_real_smul,
    primitiveSpinCHopfSecondSphereProduct_crossGradientFactor,
    primitiveSpinCHopfThirdSphereProductSection_eq_nested]
  unfold primitiveSpinCHopfThirdSphereTangentialSection
  module

/-- Multiplying the Hopf zero mode by one coordinate recovers the installed
first-level coordinate section. -/
theorem primitiveSpinCHopfCoordinateMulZeroMode_eq_firstSphere
    (coordinate : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCRealScalarMulSection
        period hPeriod .positiveQuarter
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate)
        (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod coordinate)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode) =
      primitiveSpinCHopfFirstSphereCoordinateSection
        period hPeriod coordinate sector circleMode := by
  rw [← primitiveSpinCFirstPositiveScalarHarmonicSection_eq]
  rfl

/-- A doubly nested coordinate multiplier of a first-level coordinate
section is the corresponding raw cubic. -/
theorem primitiveSpinCHopfThirdSphereNestedCoordinate_eq_product
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCRealScalarMulSection
        period hPeriod .positiveQuarter
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
        (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod first)
        (d9PrimitiveSpinCRealScalarMulSection
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod second)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod second)
          (primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod third sector circleMode)) =
      primitiveSpinCHopfThirdSphereProductSection
        period hPeriod first second third sector circleMode := by
  ext base
  rw [d9PrimitiveSpinCRealScalarMulSection_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply,
    primitiveSpinCHopfFirstSphereCoordinateSection_apply]
  unfold primitiveSpinCHopfThirdSphereProductSection
    primitiveSpinCScalarHarmonicSection
    primitiveSpinCThirdSphereProductScalar
  rw [d9PrimitiveSpinCRealScalarMulSection_apply]
  module

/-- One coordinate times a Clifford gradient of a first-level tangential
section. -/
def primitiveSpinCHopfThirdSphereWeightedCrossGradient
    (multiplier differential tangential : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  d9PrimitiveSpinCRealScalarMulSection
    period hPeriod .positiveQuarter
    (d9PrimitiveMonopoleBaseCoordinate period hPeriod multiplier)
    (d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod multiplier)
    (d9PrimitiveSpinCScalarCliffordGradientSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod differential)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod differential)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod tangential sector circleMode))

/-- Weighted symmetrized crossed gradients give a cubic term plus the
expected single trace. -/
theorem primitiveSpinCHopfThirdSphereWeightedCrossGradient_pair
    (multiplier first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCHopfThirdSphereWeightedCrossGradient
          period hPeriod multiplier first second sector circleMode +
        primitiveSpinCHopfThirdSphereWeightedCrossGradient
          period hPeriod multiplier second first sector circleMode =
      (2 : Real) •
          primitiveSpinCHopfThirdSphereProductSection
            period hPeriod multiplier first second sector circleMode -
        (2 * d9KroneckerDelta first second) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod multiplier sector circleMode := by
  unfold primitiveSpinCHopfThirdSphereWeightedCrossGradient
  rw [← d9PrimitiveSpinCRealScalarMulSection_add,
    primitiveSpinCHopfFirstSphereTangential_crossGradient_eq_productSection,
    d9PrimitiveSpinCRealScalarMulSection_sub,
    d9PrimitiveSpinCRealScalarMulSection_real_smul,
    d9PrimitiveSpinCRealScalarMulSection_real_smul,
    primitiveSpinCHopfThirdSphereProductSection_eq_nested,
    primitiveSpinCHopfCoordinateMulZeroMode_eq_firstSphere]

/-- Dirac action on one nested cubic tangential term. -/
theorem
    primitiveSpinCHopfThirdSphereNestedTangentialGeometricDiracOperator_eq
    (first second tangential : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfThirdSphereNestedTangentialSection
          period hPeriod first second tangential sector circleMode) =
      (2 : Real) •
          primitiveSpinCHopfThirdSphereProductSection
            period hPeriod first second tangential sector circleMode +
        normalRootLeviCivitaCorrectedFrequency period sector circleMode •
          primitiveSpinCHopfThirdSphereNestedTangentialSection
            period hPeriod first second tangential sector circleMode +
        primitiveSpinCHopfThirdSphereWeightedCrossGradient
          period hPeriod first second tangential sector circleMode +
        primitiveSpinCHopfThirdSphereWeightedCrossGradient
          period hPeriod second first tangential sector circleMode := by
  unfold primitiveSpinCHopfThirdSphereNestedTangentialSection
  rw [d9PrimitiveSpinCGeometricDiracOperator_realScalarMul,
    d9PrimitiveSpinCGeometricDiracOperator_realScalarMul,
    primitiveSpinCHopfFirstSphereTangentialGeometricDiracOperator_eq,
    d9PrimitiveSpinCScalarCliffordGradientSection_realScalarMul]
  simp_rw [d9PrimitiveSpinCRealScalarMulSection_add,
    d9PrimitiveSpinCRealScalarMulSection_real_smul]
  rw [primitiveSpinCHopfThirdSphereNestedCoordinate_eq_product]
  unfold primitiveSpinCHopfThirdSphereWeightedCrossGradient
  module

/-- Dirac action on a coordinate times the quadratic tangential partner. -/
theorem
    primitiveSpinCHopfThirdSphereCoordinateMulSecondTangentialDirac_eq
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCRealScalarMulSection
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod first)
          (primitiveSpinCHopfSecondSphereTangentialSection
            period hPeriod second third sector circleMode)) =
      (6 : Real) •
          primitiveSpinCHopfThirdSphereProductSection
            period hPeriod first second third sector circleMode -
        (2 * d9KroneckerDelta second third) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod first sector circleMode +
        normalRootLeviCivitaCorrectedFrequency period sector circleMode •
          d9PrimitiveSpinCRealScalarMulSection
            period hPeriod .positiveQuarter
            (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
            (d9PrimitiveMonopoleBaseCoordinate_contMDiff
              period hPeriod first)
            (primitiveSpinCHopfSecondSphereTangentialSection
              period hPeriod second third sector circleMode) +
        d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod first)
          (primitiveSpinCHopfSecondSphereTangentialSection
            period hPeriod second third sector circleMode) := by
  rw [d9PrimitiveSpinCGeometricDiracOperator_realScalarMul,
    primitiveSpinCHopfSecondSphereTangentialGeometricDiracOperator_eq,
    d9PrimitiveSpinCRealScalarMulSection_add,
    d9PrimitiveSpinCRealScalarMulSection_sub,
    d9PrimitiveSpinCRealScalarMulSection_real_smul,
    d9PrimitiveSpinCRealScalarMulSection_real_smul,
    d9PrimitiveSpinCRealScalarMulSection_real_smul,
    primitiveSpinCHopfThirdSphereProductSection_eq_nested,
    primitiveSpinCHopfCoordinateMulZeroMode_eq_firstSphere]

/-- The three crossed-gradient pairs contribute four raw cubics and the two
remaining trace contractions. -/
theorem primitiveSpinCHopfThirdSphere_crossGradient
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod first)
          (primitiveSpinCHopfSecondSphereTangentialSection
            period hPeriod second third sector circleMode) +
        primitiveSpinCHopfThirdSphereWeightedCrossGradient
          period hPeriod second third first sector circleMode +
        primitiveSpinCHopfThirdSphereWeightedCrossGradient
          period hPeriod third second first sector circleMode =
      (4 : Real) •
          primitiveSpinCHopfThirdSphereProductSection
            period hPeriod first second third sector circleMode -
        (2 * d9KroneckerDelta first third) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod second sector circleMode -
        (2 * d9KroneckerDelta first second) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod third sector circleMode := by
  unfold primitiveSpinCHopfSecondSphereTangentialSection
  rw [d9PrimitiveSpinCScalarCliffordGradientSection_add,
    d9PrimitiveSpinCScalarCliffordGradientSection_realScalarMul,
    d9PrimitiveSpinCScalarCliffordGradientSection_realScalarMul]
  change
    primitiveSpinCHopfThirdSphereWeightedCrossGradient
          period hPeriod second first third sector circleMode +
        primitiveSpinCHopfThirdSphereWeightedCrossGradient
          period hPeriod third first second sector circleMode +
        primitiveSpinCHopfThirdSphereWeightedCrossGradient
          period hPeriod second third first sector circleMode +
        primitiveSpinCHopfThirdSphereWeightedCrossGradient
          period hPeriod third second first sector circleMode = _
  calc
    _ =
        (primitiveSpinCHopfThirdSphereWeightedCrossGradient
            period hPeriod second first third sector circleMode +
          primitiveSpinCHopfThirdSphereWeightedCrossGradient
            period hPeriod second third first sector circleMode) +
        (primitiveSpinCHopfThirdSphereWeightedCrossGradient
            period hPeriod third first second sector circleMode +
          primitiveSpinCHopfThirdSphereWeightedCrossGradient
            period hPeriod third second first sector circleMode) := by
      module
    _ =
        ((2 : Real) •
            primitiveSpinCHopfThirdSphereProductSection
              period hPeriod second first third sector circleMode -
          (2 * d9KroneckerDelta first third) •
            primitiveSpinCHopfFirstSphereCoordinateSection
              period hPeriod second sector circleMode) +
        ((2 : Real) •
            primitiveSpinCHopfThirdSphereProductSection
              period hPeriod third first second sector circleMode -
          (2 * d9KroneckerDelta first second) •
            primitiveSpinCHopfFirstSphereCoordinateSection
              period hPeriod third sector circleMode) := by
      rw [primitiveSpinCHopfThirdSphereWeightedCrossGradient_pair,
        primitiveSpinCHopfThirdSphereWeightedCrossGradient_pair]
    _ = _ := by
      rw [
        primitiveSpinCHopfThirdSphereProductSection_swap_first_second
          period hPeriod second first third sector circleMode,
        primitiveSpinCHopfThirdSphereProductSection_swap_first_second
          period hPeriod third first second sector circleMode,
        primitiveSpinCHopfThirdSphereProductSection_swap_second_third
          period hPeriod first third second sector circleMode]
      module

/-- Second raw cubic Dirac equation:
`D Uᵢⱼₖ = 12 Qᵢⱼₖ - 2(δⱼₖXᵢ + δᵢₖXⱼ + δᵢⱼXₖ) + k Uᵢⱼₖ`. -/
theorem primitiveSpinCHopfThirdSphereTangentialGeometricDiracOperator_eq
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfThirdSphereTangentialSection
          period hPeriod first second third sector circleMode) =
      (12 : Real) •
          primitiveSpinCHopfThirdSphereProductSection
            period hPeriod first second third sector circleMode -
        (2 * d9KroneckerDelta second third) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod first sector circleMode -
        (2 * d9KroneckerDelta first third) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod second sector circleMode -
        (2 * d9KroneckerDelta first second) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod third sector circleMode +
        normalRootLeviCivitaCorrectedFrequency period sector circleMode •
          primitiveSpinCHopfThirdSphereTangentialSection
            period hPeriod first second third sector circleMode := by
  let q : SmoothSection period hPeriod :=
    primitiveSpinCHopfThirdSphereProductSection
      period hPeriod first second third sector circleMode
  let a : SmoothSection period hPeriod :=
    d9PrimitiveSpinCRealScalarMulSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod first)
      (primitiveSpinCHopfSecondSphereTangentialSection
        period hPeriod second third sector circleMode)
  let b : SmoothSection period hPeriod :=
    primitiveSpinCHopfThirdSphereNestedTangentialSection
      period hPeriod second third first sector circleMode
  let cross : SmoothSection period hPeriod :=
    d9PrimitiveSpinCScalarCliffordGradientSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod first)
      (primitiveSpinCHopfSecondSphereTangentialSection
        period hPeriod second third sector circleMode)
  let firstWeighted : SmoothSection period hPeriod :=
    primitiveSpinCHopfThirdSphereWeightedCrossGradient
      period hPeriod second third first sector circleMode
  let secondWeighted : SmoothSection period hPeriod :=
    primitiveSpinCHopfThirdSphereWeightedCrossGradient
      period hPeriod third second first sector circleMode
  let firstCoordinate : SmoothSection period hPeriod :=
    primitiveSpinCHopfFirstSphereCoordinateSection
      period hPeriod first sector circleMode
  let secondCoordinate : SmoothSection period hPeriod :=
    primitiveSpinCHopfFirstSphereCoordinateSection
      period hPeriod second sector circleMode
  let thirdCoordinate : SmoothSection period hPeriod :=
    primitiveSpinCHopfFirstSphereCoordinateSection
      period hPeriod third sector circleMode
  let frequency : Real :=
    normalRootLeviCivitaCorrectedFrequency period sector circleMode
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter (a + b) =
      (12 : Real) • q -
        (2 * d9KroneckerDelta second third) • firstCoordinate -
        (2 * d9KroneckerDelta first third) • secondCoordinate -
        (2 * d9KroneckerDelta first second) • thirdCoordinate +
        frequency • (a + b)
  have hA :
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter a =
        (6 : Real) • q -
          (2 * d9KroneckerDelta second third) • firstCoordinate +
          frequency • a + cross := by
    dsimp only [a, q, firstCoordinate, frequency, cross]
    exact
      primitiveSpinCHopfThirdSphereCoordinateMulSecondTangentialDirac_eq
        period hPeriod first second third sector circleMode
  have hB :
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter b =
        (2 : Real) • q + frequency • b +
          firstWeighted + secondWeighted := by
    dsimp only [b, q, frequency, firstWeighted, secondWeighted]
    have hRaw :=
      primitiveSpinCHopfThirdSphereNestedTangentialGeometricDiracOperator_eq
        period hPeriod second third first sector circleMode
    rw [
      primitiveSpinCHopfThirdSphereProductSection_swap_second_third
        period hPeriod second third first sector circleMode,
      primitiveSpinCHopfThirdSphereProductSection_swap_first_second
        period hPeriod second first third sector circleMode] at hRaw
    exact hRaw
  have hCross :
      cross + firstWeighted + secondWeighted =
        (4 : Real) • q -
          (2 * d9KroneckerDelta first third) • secondCoordinate -
          (2 * d9KroneckerDelta first second) • thirdCoordinate := by
    dsimp only [cross, firstWeighted, secondWeighted, q,
      secondCoordinate, thirdCoordinate]
    exact primitiveSpinCHopfThirdSphere_crossGradient
      period hPeriod first second third sector circleMode
  rw [d9PrimitiveSpinCGeometricDiracOperator_add, hA, hB]
  calc
    _ =
        (8 : Real) • q -
          (2 * d9KroneckerDelta second third) • firstCoordinate +
          frequency • (a + b) +
          (cross + firstWeighted + secondWeighted) := by
      module
    _ = _ := by
      rw [hCross]
      module

/-- Squaring the raw cubic block leaves exactly its symmetric trace defect. -/
theorem primitiveSpinCHopfThirdSphereProductGeometricDiracOperator_sq
    (first second third : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfThirdSphereProductSection
            period hPeriod first second third sector circleMode)) =
      (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 + 12) •
          primitiveSpinCHopfThirdSphereProductSection
            period hPeriod first second third sector circleMode -
        (2 * d9KroneckerDelta second third) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod first sector circleMode -
        (2 * d9KroneckerDelta first third) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod second sector circleMode -
        (2 * d9KroneckerDelta first second) •
          primitiveSpinCHopfFirstSphereCoordinateSection
            period hPeriod third sector circleMode := by
  rw [primitiveSpinCHopfThirdSphereProductGeometricDiracOperator_eq,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    primitiveSpinCHopfThirdSphereProductGeometricDiracOperator_eq,
    primitiveSpinCHopfThirdSphereTangentialGeometricDiracOperator_eq]
  module

/-- Standard seven-dimensional real trace-free cubic packet. -/
def primitiveSpinCHopfThirdSphereTraceFreeSection
    (multiplicity : Fin 7)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  ![
    primitiveSpinCHopfThirdSphereProductSection
        period hPeriod 0 0 0 sector circleMode +
      (-3 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 0 1 1 sector circleMode,
    (3 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 0 0 1 sector circleMode +
      (-1 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 1 1 1 sector circleMode,
    primitiveSpinCHopfThirdSphereProductSection
        period hPeriod 0 0 2 sector circleMode +
      (-1 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 1 1 2 sector circleMode,
    (2 : Real) •
      primitiveSpinCHopfThirdSphereProductSection
        period hPeriod 0 1 2 sector circleMode,
    (4 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 0 2 2 sector circleMode +
      (-1 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 0 0 0 sector circleMode +
      (-1 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 0 1 1 sector circleMode,
    (4 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 1 2 2 sector circleMode +
      (-1 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 0 0 1 sector circleMode +
      (-1 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 1 1 1 sector circleMode,
    (2 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 2 2 2 sector circleMode +
      (-3 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 0 0 2 sector circleMode +
      (-3 : Real) •
        primitiveSpinCHopfThirdSphereProductSection
          period hPeriod 1 1 2 sector circleMode
  ] multiplicity

/-- Every member of the seven-dimensional cubic packet is a genuine `D²`
eigensection with sphere energy twelve. -/
theorem primitiveSpinCHopfThirdSphereTraceFreeGeometricDiracOperator_sq
    (multiplicity : Fin 7)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfThirdSphereTraceFreeSection
            period hPeriod multiplicity sector circleMode)) =
      (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 + 12) •
        primitiveSpinCHopfThirdSphereTraceFreeSection
          period hPeriod multiplicity sector circleMode := by
  fin_cases multiplicity <;>
    simp [primitiveSpinCHopfThirdSphereTraceFreeSection,
      d9PrimitiveSpinCGeometricDiracOperator_sq_add,
      d9PrimitiveSpinCGeometricDiracOperator_sq_real_smul,
      d9PrimitiveSpinCGeometricDiracOperator_sq_neg,
      primitiveSpinCHopfThirdSphereProductGeometricDiracOperator_sq,
      d9KroneckerDelta] <;>
    module

/-- The seven scalar trace-free cubic harmonics underlying the section
packet. -/
def primitiveSpinCThirdSphereTraceFreeScalar
    (multiplicity : Fin 7) :
    ThroatBase period hPeriod → Real :=
  ![
    fun base =>
      primitiveSpinCThirdSphereProductScalar
          period hPeriod 0 0 0 base -
        3 * primitiveSpinCThirdSphereProductScalar
          period hPeriod 0 1 1 base,
    fun base =>
      3 * primitiveSpinCThirdSphereProductScalar
          period hPeriod 0 0 1 base -
        primitiveSpinCThirdSphereProductScalar
          period hPeriod 1 1 1 base,
    fun base =>
      primitiveSpinCThirdSphereProductScalar
          period hPeriod 0 0 2 base -
        primitiveSpinCThirdSphereProductScalar
          period hPeriod 1 1 2 base,
    fun base =>
      2 * primitiveSpinCThirdSphereProductScalar
        period hPeriod 0 1 2 base,
    fun base =>
      4 * primitiveSpinCThirdSphereProductScalar
          period hPeriod 0 2 2 base -
        primitiveSpinCThirdSphereProductScalar
          period hPeriod 0 0 0 base -
        primitiveSpinCThirdSphereProductScalar
          period hPeriod 0 1 1 base,
    fun base =>
      4 * primitiveSpinCThirdSphereProductScalar
          period hPeriod 1 2 2 base -
        primitiveSpinCThirdSphereProductScalar
          period hPeriod 0 0 1 base -
        primitiveSpinCThirdSphereProductScalar
          period hPeriod 1 1 1 base,
    fun base =>
      2 * primitiveSpinCThirdSphereProductScalar
          period hPeriod 2 2 2 base -
        3 * primitiveSpinCThirdSphereProductScalar
          period hPeriod 0 0 2 base -
        3 * primitiveSpinCThirdSphereProductScalar
          period hPeriod 1 1 2 base
  ] multiplicity

theorem primitiveSpinCThirdSphereTraceFreeScalar_contMDiff
    (multiplicity : Fin 7) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (primitiveSpinCThirdSphereTraceFreeScalar
        period hPeriod multiplicity) := by
  fin_cases multiplicity
  · exact
      (primitiveSpinCThirdSphereProductScalar_contMDiff
          period hPeriod 0 0 0).sub
        (contMDiff_const.mul
          (primitiveSpinCThirdSphereProductScalar_contMDiff
            period hPeriod 0 1 1))
  · exact
      (contMDiff_const.mul
          (primitiveSpinCThirdSphereProductScalar_contMDiff
            period hPeriod 0 0 1)).sub
        (primitiveSpinCThirdSphereProductScalar_contMDiff
          period hPeriod 1 1 1)
  · exact
      (primitiveSpinCThirdSphereProductScalar_contMDiff
          period hPeriod 0 0 2).sub
        (primitiveSpinCThirdSphereProductScalar_contMDiff
          period hPeriod 1 1 2)
  · exact
      contMDiff_const.mul
        (primitiveSpinCThirdSphereProductScalar_contMDiff
          period hPeriod 0 1 2)
  · exact
      ((contMDiff_const.mul
          (primitiveSpinCThirdSphereProductScalar_contMDiff
            period hPeriod 0 2 2)).sub
        (primitiveSpinCThirdSphereProductScalar_contMDiff
          period hPeriod 0 0 0)).sub
        (primitiveSpinCThirdSphereProductScalar_contMDiff
          period hPeriod 0 1 1)
  · exact
      ((contMDiff_const.mul
          (primitiveSpinCThirdSphereProductScalar_contMDiff
            period hPeriod 1 2 2)).sub
        (primitiveSpinCThirdSphereProductScalar_contMDiff
          period hPeriod 0 0 1)).sub
        (primitiveSpinCThirdSphereProductScalar_contMDiff
          period hPeriod 1 1 1)
  · exact
      ((contMDiff_const.mul
          (primitiveSpinCThirdSphereProductScalar_contMDiff
            period hPeriod 2 2 2)).sub
        (contMDiff_const.mul
          (primitiveSpinCThirdSphereProductScalar_contMDiff
            period hPeriod 0 0 2))).sub
        (contMDiff_const.mul
          (primitiveSpinCThirdSphereProductScalar_contMDiff
            period hPeriod 1 1 2))

/-- Scalar multiplication by each cubic gives exactly the corresponding
trace-free smooth section. -/
theorem primitiveSpinCThirdSphereScalarHarmonicSection_eq
    (multiplicity : Fin 7)
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCScalarHarmonicSection
        period hPeriod
        (primitiveSpinCThirdSphereTraceFreeScalar
          period hPeriod multiplicity)
        (primitiveSpinCThirdSphereTraceFreeScalar_contMDiff
          period hPeriod multiplicity)
        sector circleMode =
      primitiveSpinCHopfThirdSphereTraceFreeSection
        period hPeriod multiplicity sector circleMode := by
  ext base
  fin_cases multiplicity <;>
    simp [primitiveSpinCScalarHarmonicSection,
      primitiveSpinCThirdSphereTraceFreeScalar,
      primitiveSpinCHopfThirdSphereTraceFreeSection,
      primitiveSpinCHopfThirdSphereProductSection,
      primitiveSpinCThirdSphereProductScalar,
      d9PrimitiveSpinCRealScalarMulSection_apply] <;>
    module

theorem primitiveSpinCHarmonicSphereEnergy_two :
    primitiveSpinCHarmonicSphereEnergy 2 = 12 := by
  rw [primitiveSpinCHarmonicSphereEnergy_eq]
  norm_num

/-- Each concrete cubic is an unconditional Lichnerowicz seed for sphere
level `p = 3`. -/
def primitiveSpinCThirdPositiveScalarHarmonicLichnerowiczSeed
    (multiplicity : Fin 7) :
    PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
      period hPeriod 2 where
  scalar :=
    primitiveSpinCThirdSphereTraceFreeScalar
      period hPeriod multiplicity
  scalar_contMDiff :=
    primitiveSpinCThirdSphereTraceFreeScalar_contMDiff
      period hPeriod multiplicity
  dirac_sq_scalar := by
    intro sector circleMode
    rw [primitiveSpinCThirdSphereScalarHarmonicSection_eq]
    simpa [primitiveSpinCHarmonicSphereEnergy_two] using
      primitiveSpinCHopfThirdSphereTraceFreeGeometricDiracOperator_sq
        period hPeriod multiplicity sector circleMode

theorem primitiveSphereModeDegeneracy_three :
    primitiveSphereModeDegeneracy 3 = 7 := by
  norm_num [primitiveSphereModeDegeneracy]

/-- Canonically indexed concrete `p = 3` scalar packet. -/
def primitiveSpinCThirdPositiveScalarHarmonicLichnerowiczPacket
    (multiplicity : Fin (primitiveSphereModeDegeneracy (2 + 1))) :
    PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
      period hPeriod 2 :=
  primitiveSpinCThirdPositiveScalarHarmonicLichnerowiczSeed
    period hPeriod
    (Fin.cast (by norm_num [primitiveSphereModeDegeneracy]) multiplicity)

/-- Canonical first-order signed seed generated by a cubic harmonic. -/
def primitiveSpinCThirdPositiveHarmonicDiracSeed
    (multiplicity : Fin 7)
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCHarmonicDiracSeed4D
      period hPeriod 2 sector circleMode :=
  (primitiveSpinCThirdPositiveScalarHarmonicLichnerowiczSeed
    period hPeriod multiplicity).toDiracSeed sector circleMode

theorem primitiveSpinCThirdPositiveHarmonicDiracSeed_positive_eigen
    (multiplicity : Fin 7)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCThirdPositiveHarmonicDiracSeed
          period hPeriod multiplicity sector circleMode).positiveSection =
      primitiveSpinCHarmonicDiracFrequency
          period 2 sector circleMode •
        (primitiveSpinCThirdPositiveHarmonicDiracSeed
          period hPeriod multiplicity sector circleMode).positiveSection :=
  (primitiveSpinCThirdPositiveHarmonicDiracSeed
    period hPeriod multiplicity sector circleMode).positiveSection_eigen

theorem primitiveSpinCThirdPositiveHarmonicDiracSeed_negative_eigen
    (multiplicity : Fin 7)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCThirdPositiveHarmonicDiracSeed
          period hPeriod multiplicity sector circleMode).negativeSection =
      (-primitiveSpinCHarmonicDiracFrequency
          period 2 sector circleMode) •
        (primitiveSpinCThirdPositiveHarmonicDiracSeed
          period hPeriod multiplicity sector circleMode).negativeSection :=
  (primitiveSpinCThirdPositiveHarmonicDiracSeed
    period hPeriod multiplicity sector circleMode).negativeSection_eigen

/-- Seven rational sphere witnesses with a nonsingular cubic evaluation
matrix. -/
def primitiveSpinCThirdSphereWitnessPoint
    (witness : Fin 7) : MonopoleSphere :=
  ![
    primitiveSpinCSecondSphereRationalPoint 1 0 0 (by norm_num),
    primitiveSpinCSecondSphereRationalPoint 0 1 0 (by norm_num),
    primitiveSpinCSecondSphereRationalPoint
      (3 / 5 : Real) (4 / 5 : Real) 0 (by norm_num),
    primitiveSpinCSecondSphereRationalPoint 0 0 1 (by norm_num),
    primitiveSpinCSecondSphereRationalPoint
      (3 / 5 : Real) 0 (4 / 5 : Real) (by norm_num),
    primitiveSpinCSecondSphereRationalPoint
      0 (3 / 5 : Real) (4 / 5 : Real) (by norm_num),
    primitiveSpinCSecondSphereRationalPoint
      (1 / 3 : Real) (2 / 3 : Real) (2 / 3 : Real) (by norm_num)
  ] witness

def primitiveSpinCThirdSphereWitnessCover
    (witness : Fin 7) : MappingTorusCover (ThroatData period hPeriod) :=
  ⟨equatorialTwoSphereHomeomorph.symm
      (primitiveSpinCThirdSphereWitnessPoint witness), 0⟩

def primitiveSpinCThirdSphereWitnessBase
    (witness : Fin 7) : ThroatBase period hPeriod :=
  mappingTorusMk (ThroatData period hPeriod)
    (primitiveSpinCThirdSphereWitnessCover
      period hPeriod witness)

@[simp]
theorem primitiveSpinCThirdSphereWitnessCover_sphere
    (witness : Fin 7) :
    d9MonopoleSphereCoverProjection period hPeriod
        (primitiveSpinCThirdSphereWitnessCover
          period hPeriod witness) =
      primitiveSpinCThirdSphereWitnessPoint witness := by
  simp [primitiveSpinCThirdSphereWitnessCover,
    d9MonopoleSphereCoverProjection]

@[simp]
theorem primitiveSpinCThirdSphereWitnessBase_coordinate
    (witness : Fin 7) (coordinate : Fin 3) :
    d9PrimitiveMonopoleBaseCoordinate
        period hPeriod coordinate
        (primitiveSpinCThirdSphereWitnessBase
          period hPeriod witness) =
      monopoleSphereCoordinate
        (primitiveSpinCThirdSphereWitnessPoint witness) coordinate := by
  unfold d9PrimitiveMonopoleBaseCoordinate
    primitiveSpinCThirdSphereWitnessBase
  rw [d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCThirdSphereWitnessCover_sphere]

/-- North primitive-SpinC chart attached to one cubic witness. -/
def primitiveSpinCThirdSphereWitnessIndex
    (witness : Fin 7) :
    D9PrimitiveSpinCIndex period hPeriod :=
  (primitiveSpinCThirdSphereWitnessCover
    period hPeriod witness, .north)

theorem primitiveSpinCThirdSphereWitnessBase_mem
    (witness : Fin 7) :
    primitiveSpinCThirdSphereWitnessBase
        period hPeriod witness ∈
      d9PrimitiveSpinCBaseSet period hPeriod
        (primitiveSpinCThirdSphereWitnessIndex
          period hPeriod witness) := by
  constructor
  · exact ((mappingTorusMk_isCoveringMap
      (ThroatData period hPeriod)).isLocalHomeomorph)
      |>.apply_self_mem_localInverseAt_source
  · change
      d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCThirdSphereWitnessBase
            period hPeriod witness) ∈
        monopoleChartDomain .north
    rw [primitiveSpinCThirdSphereWitnessBase,
      d9ThroatMonopoleSphereProjection_mk,
      primitiveSpinCThirdSphereWitnessCover_sphere]
    fin_cases witness <;>
      norm_num [monopoleChartDomain,
        primitiveSpinCThirdSphereWitnessPoint,
        primitiveSpinCSecondSphereRationalPoint,
        monopoleSphereCoordinate, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.cons_val_succ, Matrix.cons_val_fin_one,
        Fin.reduceFinMk]

/-- Normal Fourier matter at one cubic witness. -/
def primitiveSpinCThirdSphereWitnessMode
    (witness : Fin 7) (sector : NormalRootChoice) (mode : Int) :
    D9DoubledMatterFiber :=
  primitiveSpinCNormalModeDoubledLift
    period hPeriod sector mode
    (primitiveSpinCThirdSphereWitnessCover
      period hPeriod witness)

theorem primitiveSpinCThirdSphereWitnessMode_halfSpinor
    (witness : Fin 7) (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (primitiveSpinCThirdSphereWitnessMode
          period hPeriod witness sector mode) =
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
    simp [primitiveSpinCThirdSphereWitnessMode,
      primitiveSpinCThirdSphereWitnessCover,
      primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      normalRootSpinFramePhase, normalRootSpinFramePhaseAngle,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      ambientHalfGammaPositiveEigenvector, zero_apply]

@[simp]
theorem primitiveSpinCThirdSphereWitnessMode_sectorCoefficient
    (witness : Fin 7) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (primitiveSpinCThirdSphereWitnessMode
          period hPeriod witness sector mode) = 1 := by
  cases sector
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (primitiveSpinCThirdSphereWitnessMode
          period hPeriod witness .positiveQuarter mode)).1 0 = 1
    rw [primitiveSpinCThirdSphereWitnessMode_halfSpinor]
    rfl
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (primitiveSpinCThirdSphereWitnessMode
          period hPeriod witness .negativeQuarter mode)).2 0 = 1
    rw [primitiveSpinCThirdSphereWitnessMode_halfSpinor]
    rfl

@[simp]
theorem primitiveSpinCThirdSphereWitnessMode_gamma_two_sectorCoefficient
    (witness : Fin 7) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCThirdSphereWitnessMode
            period hPeriod witness sector mode)) = 0 := by
  cases sector
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCThirdSphereWitnessMode
            period hPeriod witness .positiveQuarter mode))).1 0 = 0
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_two,
      primitiveSpinCThirdSphereWitnessMode_halfSpinor]
    simp
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCThirdSphereWitnessMode
            period hPeriod witness .negativeQuarter mode))).2 0 = 0
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_two,
      primitiveSpinCThirdSphereWitnessMode_halfSpinor]
    simp

/-- Local Hopf zero-mode value at one cubic witness. -/
def primitiveSpinCThirdSphereHopfZeroLocal
    (witness : Fin 7) (sector : NormalRootChoice) (mode : Int) :
    D9DoubledMatterFiber :=
  primitiveSpinCGeometricSectionLocalCoordinate
    period hPeriod
    (primitiveSpinCThirdSphereWitnessIndex
      period hPeriod witness)
    (primitiveSpinCThirdSphereWitnessBase
      period hPeriod witness)
    (primitiveSpinCHopfZeroModeSection
      period hPeriod sector mode)

@[simp]
theorem primitiveSpinCThirdSphereWitnessMode_firstFrame_sectorCoefficient
    (witness : Fin 7) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (d9PrimitiveSpinCHopfFirstFrameCLM sector
          (primitiveSpinCThirdSphereWitnessMode
            period hPeriod witness sector mode)) = 1 := by
  rw [d9PrimitiveSpinCHopfFirstFrameCLM_apply, map_sub,
    ← d9PrimitiveSpinCComplexAction_I,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction,
    primitiveSpinCThirdSphereWitnessMode_sectorCoefficient,
    primitiveSpinCThirdSphereWitnessMode_gamma_two_sectorCoefficient]
  simp

@[simp]
theorem primitiveSpinCThirdSphereWitnessMode_secondFrame_sectorCoefficient
    (witness : Fin 7) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (d9PrimitiveSpinCHopfSecondFrameCLM sector
          (primitiveSpinCThirdSphereWitnessMode
            period hPeriod witness sector mode)) = 1 := by
  rw [d9PrimitiveSpinCHopfSecondFrameCLM_apply, map_add,
    ← d9PrimitiveSpinCComplexAction_I,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction,
    primitiveSpinCThirdSphereWitnessMode_sectorCoefficient,
    primitiveSpinCThirdSphereWitnessMode_gamma_two_sectorCoefficient]
  simp

theorem primitiveSpinCThirdSphereHopfZeroLocal_sectorCoefficient
    (witness : Fin 7) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (primitiveSpinCThirdSphereHopfZeroLocal
          period hPeriod witness sector mode) =
      primitiveMonopoleZeroNorthValue
          (primitiveSpinCThirdSphereWitnessPoint witness) +
        primitiveMonopoleZeroComplementNorthValue
          (primitiveSpinCThirdSphereWitnessPoint witness) := by
  unfold primitiveSpinCThirdSphereHopfZeroLocal
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
    period hPeriod sector mode
    (primitiveSpinCThirdSphereWitnessIndex
      period hPeriod witness)
    (primitiveSpinCThirdSphereWitnessBase
      period hPeriod witness)
    (primitiveSpinCThirdSphereWitnessBase_mem
      period hPeriod witness)]
  change
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (primitiveSpinCThirdSphereWitnessCover
              period hPeriod witness, .north)
            (mappingTorusMk (ThroatData period hPeriod)
              (primitiveSpinCThirdSphereWitnessCover
                period hPeriod witness))) = _
  rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    primitiveSpinCThirdSphereWitnessCover_sphere, map_add,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction]
  change
    primitiveMonopoleZeroLocalValue .north
          (primitiveSpinCThirdSphereWitnessPoint witness) *
        primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          (d9PrimitiveSpinCHopfFirstFrameCLM sector
            (primitiveSpinCThirdSphereWitnessMode
              period hPeriod witness sector mode)) +
      primitiveMonopoleZeroComplementLocalValue .north
          (primitiveSpinCThirdSphereWitnessPoint witness) *
        primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          (d9PrimitiveSpinCHopfSecondFrameCLM sector
            (primitiveSpinCThirdSphereWitnessMode
              period hPeriod witness sector mode)) = _
  rw [primitiveSpinCThirdSphereWitnessMode_firstFrame_sectorCoefficient,
    primitiveSpinCThirdSphereWitnessMode_secondFrame_sectorCoefficient]
  simp [primitiveMonopoleZeroLocalValue,
    primitiveMonopoleZeroComplementLocalValue]

/-- The common Hopf factor is nonzero at every cubic witness. -/
theorem primitiveSpinCThirdSphereHopfZeroLocal_ne_zero
    (witness : Fin 7) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCThirdSphereHopfZeroLocal
        period hPeriod witness sector mode ≠ 0 := by
  intro hZero
  have hCoefficient := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector)
    hZero
  rw [primitiveSpinCThirdSphereHopfZeroLocal_sectorCoefficient] at hCoefficient
  simp only [map_zero] at hCoefficient
  have hReal := congrArg Complex.re hCoefficient
  fin_cases witness <;>
    norm_num [primitiveMonopoleZeroNorthValue,
      primitiveMonopoleZeroComplementNorthValue,
      primitiveSpinCThirdSphereWitnessPoint,
      primitiveSpinCSecondSphereRationalPoint,
      monopoleSphereCoordinate, monopoleSphereXY,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val_succ,
      Matrix.cons_val_fin_one, Fin.reduceFinMk,
      Complex.real_smul] at hReal
  · have hSqrtFive : 0 < Real.sqrt 5 :=
      Real.sqrt_pos.2 (by norm_num)
    exact
      (ne_of_gt
        (add_pos
          (div_pos (by norm_num) hSqrtFive)
          (mul_pos (div_pos hSqrtFive (by norm_num)) (by norm_num))))
        hReal
  · have hSqrtFive : 0 < Real.sqrt 5 :=
      Real.sqrt_pos.2 (by norm_num)
    have hSqrtThree : 0 < Real.sqrt 3 :=
      Real.sqrt_pos.2 (by norm_num)
    exact
      (ne_of_gt
        (add_pos
          (div_pos hSqrtFive hSqrtThree)
          (mul_pos (div_pos hSqrtThree hSqrtFive) (by norm_num))))
        hReal

/-- Explicit rational evaluation matrix, stored by basis vector and
witness. -/
@[simp]
private theorem primitiveSpinCVecSeven_five
    {α : Type*} (a b c d e f g : α) :
    ![a, b, c, d, e, f, g] (5 : Fin 7) = f := by
  rfl

@[simp]
private theorem primitiveSpinCVecSeven_six
    {α : Type*} (a b c d e f g : α) :
    ![a, b, c, d, e, f, g] (6 : Fin 7) = g := by
  rfl

def primitiveSpinCThirdSphereWitnessValue
    (basis witness : Fin 7) : Real :=
  ![
    ![(1 : Real), 0, -(117 / 125), 0, 27 / 125, 0, -(11 / 27)] witness,
    ![(0 : Real), -1, 44 / 125, 0, 0, -(27 / 125), -(2 / 27)] witness,
    ![(0 : Real), 0, 0, 0, 36 / 125, -(36 / 125), -(2 / 9)] witness,
    ![(0 : Real), 0, 0, 0, 0, 0, 8 / 27] witness,
    ![(-1 : Real), 0, -(3 / 5), 0, 33 / 25, 0, 11 / 27] witness,
    ![(0 : Real), -1, -(4 / 5), 0, 0, 33 / 25, 22 / 27] witness,
    ![(0 : Real), 0, 0, 2, 4 / 25, 4 / 25, -(14 / 27)] witness
  ] basis

@[simp]
theorem primitiveSpinCThirdSphereTraceFreeScalar_witness
    (basis witness : Fin 7) :
    primitiveSpinCThirdSphereTraceFreeScalar
        period hPeriod basis
        (primitiveSpinCThirdSphereWitnessBase
          period hPeriod witness) =
      primitiveSpinCThirdSphereWitnessValue basis witness := by
  fin_cases basis <;> fin_cases witness <;>
    norm_num [primitiveSpinCThirdSphereTraceFreeScalar,
      primitiveSpinCThirdSphereProductScalar,
      primitiveSpinCThirdSphereWitnessValue,
      primitiveSpinCThirdSphereWitnessPoint,
      primitiveSpinCSecondSphereRationalPoint,
      monopoleSphereCoordinate, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      Fin.reduceFinMk]

private theorem primitiveSpinCThirdSphereWitnessKernel
    (coefficients : Fin 7 → Real)
    (hEvaluate :
      ∀ witness : Fin 7,
        (∑ basis : Fin 7,
          coefficients basis *
            primitiveSpinCThirdSphereWitnessValue basis witness) = 0)
    (multiplicity : Fin 7) :
    coefficients multiplicity = 0 := by
  have hZero := hEvaluate (0 : Fin 7)
  have hOne := hEvaluate (1 : Fin 7)
  have hTwo := hEvaluate (2 : Fin 7)
  have hThree := hEvaluate (3 : Fin 7)
  have hFour := hEvaluate (4 : Fin 7)
  have hFive := hEvaluate (5 : Fin 7)
  have hSix := hEvaluate (6 : Fin 7)
  norm_num [Fin.sum_univ_succ,
    primitiveSpinCThirdSphereWitnessValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    primitiveSpinCVecSeven_five, primitiveSpinCVecSeven_six,
    Fin.reduceFinMk] at hZero hOne hTwo hThree hFour hFive hSix
  have hCoefficientZero : coefficients 0 = 0 := by
    linarith
  have hCoefficientOne : coefficients 1 = 0 := by
    linarith
  have hCoefficientTwo : coefficients 2 = 0 := by
    linarith
  have hCoefficientSix : coefficients 6 = 0 := by
    simpa [Fin.reduceFinMk] using hThree
  have hZero' :
      coefficients 0 - coefficients 4 = 0 := by
    simpa [sub_eq_add_neg, Fin.reduceFinMk] using hZero
  have hCoefficientFour : coefficients 4 = 0 := by
    linarith
  have hOne' :
      -coefficients 1 - coefficients 5 = 0 := by
    simpa [sub_eq_add_neg, Fin.reduceFinMk] using hOne
  have hCoefficientFive : coefficients 5 = 0 := by
    linarith
  have hSix' :
      -(coefficients 0 * (11 / 27)) +
        (-(coefficients 1 * (2 / 27)) +
          (-(coefficients 2 * (2 / 9)) +
            (coefficients 3 * (8 / 27) +
              (coefficients 4 * (11 / 27) +
                (coefficients 5 * (22 / 27) +
                  -(coefficients 6 * (14 / 27))))))) = 0 := by
    simpa [Fin.reduceFinMk] using hSix
  have hCoefficientThree : coefficients 3 = 0 := by
    linarith
  fin_cases multiplicity
  · exact hCoefficientZero
  · exact hCoefficientOne
  · exact hCoefficientTwo
  · exact hCoefficientThree
  · exact hCoefficientFour
  · exact hCoefficientFive
  · exact hCoefficientSix

/-- The seven concrete cubic scalar harmonics are linearly independent. -/
theorem primitiveSpinCThirdSphereTraceFreeScalar_linearIndependent :
    LinearIndependent Real
      (fun multiplicity : Fin 7 =>
        primitiveSpinCThirdSphereTraceFreeScalar
          period hPeriod multiplicity) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients hSum multiplicity
  have hEvaluate (witness : Fin 7) :=
    congrArg
      (fun scalar : ThroatBase period hPeriod → Real =>
        scalar
          (primitiveSpinCThirdSphereWitnessBase
            period hPeriod witness))
      hSum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply,
    primitiveSpinCThirdSphereTraceFreeScalar_witness] at hEvaluate
  exact primitiveSpinCThirdSphereWitnessKernel
    coefficients hEvaluate multiplicity

/-- Local evaluation of a cubic eigensection factors through its scalar
matrix entry and the common nonzero Hopf value. -/
theorem primitiveSpinCHopfThirdSphereTraceFreeSection_localCoordinate
    (basis witness : Fin 7)
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCThirdSphereWitnessIndex
          period hPeriod witness)
        (primitiveSpinCThirdSphereWitnessBase
          period hPeriod witness)
        (primitiveSpinCHopfThirdSphereTraceFreeSection
          period hPeriod basis sector mode) =
      primitiveSpinCThirdSphereWitnessValue basis witness •
        primitiveSpinCThirdSphereHopfZeroLocal
          period hPeriod witness sector mode := by
  rw [← primitiveSpinCThirdSphereScalarHarmonicSection_eq]
  unfold primitiveSpinCScalarHarmonicSection
  rw [primitiveSpinCGeometricSectionLocalCoordinate_realScalarMul,
    primitiveSpinCThirdSphereTraceFreeScalar_witness]
  rfl

/-- The seven genuine smooth `D²` eigensections at sphere level `p = 3`
are linearly independent for every sector and circle mode. -/
theorem primitiveSpinCHopfThirdSphereTraceFreeSection_linearIndependent
    (sector : NormalRootChoice) (mode : Int) :
    LinearIndependent Real
      (fun multiplicity : Fin 7 =>
        primitiveSpinCHopfThirdSphereTraceFreeSection
          period hPeriod multiplicity sector mode) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients hSum multiplicity
  have hEvaluate (witness : Fin 7) :
      (∑ basis : Fin 7,
          coefficients basis *
            primitiveSpinCThirdSphereWitnessValue basis witness) = 0 := by
    let localCoordinate :=
      primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCThirdSphereWitnessIndex
          period hPeriod witness)
        (primitiveSpinCThirdSphereWitnessBase
          period hPeriod witness)
    have hLocal := congrArg localCoordinate hSum
    dsimp only [localCoordinate] at hLocal
    simp only [map_sum, map_smul, map_zero,
      primitiveSpinCHopfThirdSphereTraceFreeSection_localCoordinate] at hLocal
    simp_rw [smul_smul] at hLocal
    rw [← Finset.sum_smul] at hLocal
    by_contra hScalar
    exact
      (smul_ne_zero hScalar
        (primitiveSpinCThirdSphereHopfZeroLocal_ne_zero
          period hPeriod witness sector mode)) hLocal
  exact primitiveSpinCThirdSphereWitnessKernel
    coefficients hEvaluate multiplicity

/-- Consolidated unconditional certificate for the complete concrete
`p = 3` scalar and smooth-section packet. -/
structure PrimitiveSpinCThirdPositiveSpherePacketCertificate4D where
  harmonic :
    Fin 7 →
      PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
        period hPeriod 2
  scalar_linearIndependent :
    LinearIndependent Real (fun multiplicity => (harmonic multiplicity).scalar)
  section_linearIndependent :
    ∀ (sector : NormalRootChoice) (mode : Int),
      LinearIndependent Real
        (fun multiplicity : Fin 7 =>
          primitiveSpinCHopfThirdSphereTraceFreeSection
            period hPeriod multiplicity sector mode)
  degeneracy : primitiveSphereModeDegeneracy 3 = 7

def primitiveSpinCThirdPositiveSpherePacketCertificate4D :
    PrimitiveSpinCThirdPositiveSpherePacketCertificate4D
      period hPeriod where
  harmonic :=
    primitiveSpinCThirdPositiveScalarHarmonicLichnerowiczSeed
      period hPeriod
  scalar_linearIndependent :=
    primitiveSpinCThirdSphereTraceFreeScalar_linearIndependent
      period hPeriod
  section_linearIndependent :=
    primitiveSpinCHopfThirdSphereTraceFreeSection_linearIndependent
      period hPeriod
  degeneracy := primitiveSphereModeDegeneracy_three

theorem primitiveSpinCThirdPositiveSpherePacket_gate :
    Nonempty
      (PrimitiveSpinCThirdPositiveSpherePacketCertificate4D
        period hPeriod) :=
  ⟨primitiveSpinCThirdPositiveSpherePacketCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCThirdPositiveSphereDirac4D
end JanusFormal
