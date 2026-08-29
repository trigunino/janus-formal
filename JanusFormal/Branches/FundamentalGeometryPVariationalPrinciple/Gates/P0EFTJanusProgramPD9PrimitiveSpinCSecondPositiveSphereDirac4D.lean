import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D

/-!
# The second positive primitive SpinC sphere level

This gate constructs the five real trace-free quadratic harmonics on the
quotient two-sphere.  It derives their genuine SpinC `D²` equation from the
global scalar Leibniz rule, the already established first-level block, and
the Clifford anticommutation relations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D

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
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereComplexMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracLeibniz4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
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

/-- Smooth scalar multiplication distributes over section addition. -/
theorem d9PrimitiveSpinCRealScalarMulSection_add
    (choice : NormalRootChoice)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (first second :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCRealScalarMulSection
        period hPeriod choice scalar hScalar (first + second) =
      d9PrimitiveSpinCRealScalarMulSection
          period hPeriod choice scalar hScalar first +
        d9PrimitiveSpinCRealScalarMulSection
          period hPeriod choice scalar hScalar second := by
  ext base
  rw [d9PrimitiveSpinCRealScalarMulSection_apply]
  have hState :
      (first + second) base = first base + second base := rfl
  have hResult :
      (d9PrimitiveSpinCRealScalarMulSection
            period hPeriod choice scalar hScalar first +
          d9PrimitiveSpinCRealScalarMulSection
            period hPeriod choice scalar hScalar second) base =
        d9PrimitiveSpinCRealScalarMulSection
              period hPeriod choice scalar hScalar first base +
          d9PrimitiveSpinCRealScalarMulSection
            period hPeriod choice scalar hScalar second base := rfl
  rw [hState, hResult,
    d9PrimitiveSpinCRealScalarMulSection_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply]
  exact smul_add _ _ _

/-- Iterated smooth real scalar multiplication is multiplication of the
two scalar functions. -/
theorem d9PrimitiveSpinCRealScalarMulSection_mul
    (choice : NormalRootChoice)
    (first second : ThroatBase period hPeriod → Real)
    (hFirst :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ first)
    (hSecond :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ second)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    d9PrimitiveSpinCRealScalarMulSection
        period hPeriod choice first hFirst
        (d9PrimitiveSpinCRealScalarMulSection
          period hPeriod choice second hSecond state) =
      d9PrimitiveSpinCRealScalarMulSection
        period hPeriod choice (fun base => first base * second base)
        (hFirst.mul hSecond) state := by
  ext base
  rw [d9PrimitiveSpinCRealScalarMulSection_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply]
  exact smul_smul _ _ _

/-- The generic Clifford-gradient remainder for one coordinate is exactly
the already constructed first-level tangential section. -/
theorem primitiveSpinCFirstPositiveScalarHarmonicGradientSection_eq
    (coordinate : Fin 3) (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCScalarHarmonicGradientSection
        period hPeriod
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate)
        (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod coordinate)
        sector circleMode =
      primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod coordinate sector circleMode := by
  have hGeneric :=
    primitiveSpinCScalarHarmonicSection_dirac
      period hPeriod
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod coordinate)
      sector circleMode
  rw [primitiveSpinCFirstPositiveScalarHarmonicSection_eq,
    primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_eq]
      at hGeneric
  exact (add_left_cancel hGeneric).symm

/-- For an arbitrary genuine SpinC section, the Clifford gradient of one
sphere coordinate is the tangential projector `γᵢ - nᵢ γ(n)`. -/
theorem d9PrimitiveSpinCCoordinateCliffordGradientSection_apply
    (choice : NormalRootChoice) (coordinate : Fin 3)
    (state :
      D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    (d9PrimitiveSpinCScalarCliffordGradientSection
        period hPeriod choice
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate)
        (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod coordinate)
        state base : D9DoubledMatterFiber) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate (state base) -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate base •
          d9PrimitiveSpinCBaseUnitRadialClifford
            period hPeriod base (state base) := by
  rw [d9PrimitiveSpinCScalarCliffordGradientSection_apply]
  unfold d9PrimitiveSpinCScalarCliffordGradientAt
  simp_rw [
    d9PrimitiveMonopoleBaseCoordinate_mvfderiv_intrinsicFrame,
    d9PrimitiveMonopoleCoordinateFrameDerivative_eq_projector,
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily_indexAt]
  let matter : D9DoubledMatterFiber := state base
  change
    (∑ direction : Fin 3,
      d9DoubledMatterFiberCliffordGammaCLM direction
        ((d9KroneckerDelta direction coordinate -
            d9PrimitiveSpinCBaseUnitRadialCoordinate
                period hPeriod direction base *
              d9PrimitiveSpinCBaseUnitRadialCoordinate
                period hPeriod coordinate base) • matter)) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate matter -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate base •
          d9PrimitiveSpinCBaseUnitRadialClifford
            period hPeriod base matter
  fin_cases coordinate <;>
    simp [Fin.sum_univ_succ, d9KroneckerDelta,
      d9PrimitiveSpinCBaseUnitRadialClifford, map_smul] <;>
    module

/-- The global Hopf zero mode retains the radial Clifford eigen-equation in
the preferred quotient fiber. -/
theorem primitiveSpinCHopfZeroModeSection_baseUnitRadial_eigen
    (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    d9PrimitiveSpinCBaseUnitRadialClifford
        period hPeriod base
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode base) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode base) := by
  let point := normalBundleIndexAt period hPeriod base
  let chart :=
    (d9PrimitiveMonopolePrincipalBundleCore
      period hPeriod 1).indexAt base
  let core :=
    d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter
  have hProject :
      mappingTorusMk (ThroatData period hPeriod) point = base :=
    normalBundleIndexAt_projects period hPeriod base
  have hChartBase :
      base ∈ d9PrimitiveMonopoleChartDomain
        period hPeriod chart :=
    (core.mem_baseSet_at base).2
  have hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart := by
    unfold d9PrimitiveMonopoleChartDomain at hChartBase
    rw [← hProject] at hChartBase
    exact hChartBase
  have hLocal :=
    primitiveSpinCHopfZeroModeLocalGaugeFamily_unitRadial_eigen
      period hPeriod sector circleMode point chart hChart
  change
    d9PrimitiveSpinCBaseUnitRadialClifford
        period hPeriod base
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector circleMode).localValue
            (point, chart) base) =
      d9PrimitiveSpinCImaginaryAction
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector circleMode).localValue
            (point, chart) base)
  rw [← hProject, d9PrimitiveSpinCBaseUnitRadialClifford_mk]
  exact hLocal

/-- Radial Clifford multiplication is real-linear. -/
theorem d9PrimitiveSpinCBaseUnitRadialClifford_sub
    (base : ThroatBase period hPeriod)
    (first second : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseUnitRadialClifford
        period hPeriod base (first - second) =
      d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base first -
        d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base second := by
  unfold d9PrimitiveSpinCBaseUnitRadialClifford
  simp_rw [map_sub, smul_sub]
  rw [Finset.sum_sub_distrib]

theorem d9PrimitiveSpinCBaseUnitRadialClifford_real_smul
    (base : ThroatBase period hPeriod) (scalar : Real)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseUnitRadialClifford
        period hPeriod base (scalar • matter) =
      scalar •
        d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base matter := by
  unfold d9PrimitiveSpinCBaseUnitRadialClifford
  simp_rw [map_smul]
  calc
    _ = ∑ direction : Fin 3,
        scalar •
          (d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod direction base •
            d9DoubledMatterFiberCliffordGammaCLM direction matter) := by
      apply Finset.sum_congr rfl
      intro direction _
      simp only [smul_smul, mul_comm]
    _ = _ := by
      exact (Finset.smul_sum (r := scalar)
        (f := fun direction : Fin 3 =>
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod direction base •
            d9DoubledMatterFiberCliffordGammaCLM direction matter)
        (s := Finset.univ)).symm

/-- Anticommuting a fixed Clifford generator through the radial contraction. -/
theorem d9PrimitiveSpinCBaseUnitRadialClifford_clifford
    (coordinate : Fin 3) (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (d9DoubledMatterFiberCliffordGammaCLM coordinate matter) =
      -d9DoubledMatterFiberCliffordGammaCLM coordinate
          (d9PrimitiveSpinCBaseUnitRadialClifford
            period hPeriod base matter) -
        (2 *
          d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate base) • matter := by
  fin_cases coordinate <;>
    simp [d9PrimitiveSpinCBaseUnitRadialClifford,
      Fin.sum_univ_succ, map_smul,
      d9DoubledMatterFiberCliffordGamma_sq,
      d9DoubledMatterFiberCliffordGamma_anticommute
        1 0 (by decide),
      d9DoubledMatterFiberCliffordGamma_anticommute
        2 0 (by decide),
      d9DoubledMatterFiberCliffordGamma_anticommute
        2 1 (by decide)] <;>
    module

/-- The radial contraction commutes with the fiberwise complex structure. -/
theorem d9PrimitiveSpinCBaseUnitRadialClifford_imaginary
    (base : ThroatBase period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (d9PrimitiveSpinCImaginaryAction matter) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCBaseUnitRadialClifford
          period hPeriod base matter) := by
  unfold d9PrimitiveSpinCBaseUnitRadialClifford
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  rw [map_smul, d9PrimitiveSpinCImaginaryAction_clifford]

/-- Radial Clifford action on a first-level tangential partner. -/
theorem primitiveSpinCHopfFirstSphereTangential_baseUnitRadial
    (coordinate : Fin 3) (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    let matter : D9DoubledMatterFiber :=
      primitiveSpinCHopfZeroModeSection
        period hPeriod sector circleMode base
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode base :
          D9DoubledMatterFiber) =
      -d9DoubledMatterFiberCliffordGammaCLM coordinate
          (d9PrimitiveSpinCImaginaryAction matter) -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate base • matter := by
  rw [primitiveSpinCHopfFirstSphereTangentialSection_apply]
  unfold primitiveSpinCHopfFirstSphereCoordinateTangentialAt
  rw [d9PrimitiveSpinCBaseUnitRadialClifford_sub,
    d9PrimitiveSpinCBaseUnitRadialClifford_real_smul,
    d9PrimitiveSpinCBaseUnitRadialClifford_clifford,
    d9PrimitiveSpinCBaseUnitRadialClifford_imaginary,
    primitiveSpinCHopfZeroModeSection_baseUnitRadial_eigen,
    d9PrimitiveSpinCImaginaryAction_sq,
    smul_neg]
  dsimp only
  rw [two_mul, add_smul]
  abel

/-- Product of two quotient sphere coordinates. -/
def primitiveSpinCSecondSphereProductScalar
    (first second : Fin 3) :
    ThroatBase period hPeriod → Real :=
  fun base =>
    d9PrimitiveMonopoleBaseCoordinate period hPeriod first base *
      d9PrimitiveMonopoleBaseCoordinate period hPeriod second base

theorem primitiveSpinCSecondSphereProductScalar_contMDiff
    (first second : Fin 3) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (primitiveSpinCSecondSphereProductScalar
        period hPeriod first second) :=
  (d9PrimitiveMonopoleBaseCoordinate_contMDiff
    period hPeriod first).mul
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod second)

/-- Symmetrized Clifford gradients of the first-level tangential partners.
This is the trace correction that distinguishes quadratic harmonics from
arbitrary coordinate products. -/
theorem primitiveSpinCHopfFirstSphereTangential_crossGradient
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod first)
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod second sector circleMode) +
        d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod second)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod second)
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod first sector circleMode) =
      (2 : Real) •
          d9PrimitiveSpinCRealScalarMulSection
            period hPeriod .positiveQuarter
            (primitiveSpinCSecondSphereProductScalar
              period hPeriod first second)
            (primitiveSpinCSecondSphereProductScalar_contMDiff
              period hPeriod first second)
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode) -
      (2 * d9KroneckerDelta first second) •
        primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode := by
  ext base
  change
    (d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod first)
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod second sector circleMode) base :
        D9DoubledMatterFiber) +
      (d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod second)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod second)
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod first sector circleMode) base :
        D9DoubledMatterFiber) = _
  rw [
    d9PrimitiveSpinCCoordinateCliffordGradientSection_apply,
    d9PrimitiveSpinCCoordinateCliffordGradientSection_apply,
    primitiveSpinCHopfFirstSphereTangential_baseUnitRadial,
    primitiveSpinCHopfFirstSphereTangential_baseUnitRadial]
  have hLeftSmul :
      ((2 : Real) •
          d9PrimitiveSpinCRealScalarMulSection
            period hPeriod .positiveQuarter
            (primitiveSpinCSecondSphereProductScalar
              period hPeriod first second)
            (primitiveSpinCSecondSphereProductScalar_contMDiff
              period hPeriod first second)
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode)) base =
        (2 *
            d9PrimitiveMonopoleBaseCoordinate
                period hPeriod first base *
              d9PrimitiveMonopoleBaseCoordinate
                period hPeriod second base) •
          primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base := by
    have hOuter :
        ((2 : Real) •
          d9PrimitiveSpinCRealScalarMulSection
            period hPeriod .positiveQuarter
            (primitiveSpinCSecondSphereProductScalar
              period hPeriod first second)
            (primitiveSpinCSecondSphereProductScalar_contMDiff
              period hPeriod first second)
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode)) base =
          (2 : Real) •
            d9PrimitiveSpinCRealScalarMulSection
              period hPeriod .positiveQuarter
              (primitiveSpinCSecondSphereProductScalar
                period hPeriod first second)
              (primitiveSpinCSecondSphereProductScalar_contMDiff
                period hPeriod first second)
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode) base := rfl
    rw [hOuter, d9PrimitiveSpinCRealScalarMulSection_apply]
    unfold primitiveSpinCSecondSphereProductScalar
    module
  have hTraceSmul :
      ((2 * d9KroneckerDelta first second) •
        primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode) base =
        (2 * d9KroneckerDelta first second) •
          primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode base := rfl
  have hSubApply :
      ((2 : Real) •
            d9PrimitiveSpinCRealScalarMulSection
              period hPeriod .positiveQuarter
              (primitiveSpinCSecondSphereProductScalar
                period hPeriod first second)
              (primitiveSpinCSecondSphereProductScalar_contMDiff
                period hPeriod first second)
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode) -
          (2 * d9KroneckerDelta first second) •
            primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode) base =
        ((2 : Real) •
            d9PrimitiveSpinCRealScalarMulSection
              period hPeriod .positiveQuarter
              (primitiveSpinCSecondSphereProductScalar
                period hPeriod first second)
              (primitiveSpinCSecondSphereProductScalar_contMDiff
                period hPeriod first second)
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode)) base -
          ((2 * d9KroneckerDelta first second) •
            primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode) base := rfl
  rw [hSubApply, hLeftSmul, hTraceSmul,
    primitiveSpinCHopfFirstSphereTangentialSection_apply,
    primitiveSpinCHopfFirstSphereTangentialSection_apply]
  unfold primitiveSpinCHopfFirstSphereCoordinateTangentialAt
  let matter : D9DoubledMatterFiber :=
    primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode base
  change
    d9DoubledMatterFiberCliffordGammaCLM first
          (d9DoubledMatterFiberCliffordGammaCLM second matter -
            d9PrimitiveSpinCBaseUnitRadialCoordinate
                period hPeriod second base •
              d9PrimitiveSpinCImaginaryAction matter) -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod first base •
          (-d9DoubledMatterFiberCliffordGammaCLM second
              (d9PrimitiveSpinCImaginaryAction matter) -
            d9PrimitiveSpinCBaseUnitRadialCoordinate
                period hPeriod second base • matter) +
      (d9DoubledMatterFiberCliffordGammaCLM second
          (d9DoubledMatterFiberCliffordGammaCLM first matter -
            d9PrimitiveSpinCBaseUnitRadialCoordinate
                period hPeriod first base •
              d9PrimitiveSpinCImaginaryAction matter) -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod second base •
          (-d9DoubledMatterFiberCliffordGammaCLM first
              (d9PrimitiveSpinCImaginaryAction matter) -
            d9PrimitiveSpinCBaseUnitRadialCoordinate
                period hPeriod first base • matter)) =
      (2 *
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod first base *
            d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod second base) • matter -
        (2 * d9KroneckerDelta first second) • matter
  unfold d9PrimitiveSpinCBaseUnitRadialCoordinate
  fin_cases first <;> fin_cases second <;>
    simp [d9KroneckerDelta, map_sub, map_smul,
      d9DoubledMatterFiberCliffordGamma_sq,
      d9DoubledMatterFiberCliffordGamma_anticommute
        1 0 (by decide),
      d9DoubledMatterFiberCliffordGamma_anticommute
        2 0 (by decide),
      d9DoubledMatterFiberCliffordGamma_anticommute
        2 1 (by decide)] <;>
    module

/-- Raw quadratic section `nᵢ nⱼ ψ` obtained by multiplying a first-level
coordinate section by a second sphere coordinate. -/
def primitiveSpinCHopfSecondSphereProductSection
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  d9PrimitiveSpinCRealScalarMulSection
    period hPeriod .positiveQuarter
    (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
    (d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod first)
    (primitiveSpinCHopfFirstSphereCoordinateSection
      period hPeriod second sector circleMode)

/-- Symmetric first-order partner
`nᵢ Tⱼ + nⱼ Tᵢ` of a raw quadratic section. -/
def primitiveSpinCHopfSecondSphereTangentialSection
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  d9PrimitiveSpinCRealScalarMulSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod first)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod second sector circleMode) +
    d9PrimitiveSpinCRealScalarMulSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod second)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod second)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod first sector circleMode)

/-- The raw quadratic section is exactly multiplication of the Hopf zero
mode by the product scalar. -/
theorem primitiveSpinCHopfSecondSphereProductSection_eq_scalarHarmonicSection
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCHopfSecondSphereProductSection
        period hPeriod first second sector circleMode =
      primitiveSpinCScalarHarmonicSection
        period hPeriod
        (primitiveSpinCSecondSphereProductScalar
          period hPeriod first second)
        (primitiveSpinCSecondSphereProductScalar_contMDiff
          period hPeriod first second)
        sector circleMode := by
  unfold primitiveSpinCHopfSecondSphereProductSection
  rw [← primitiveSpinCFirstPositiveScalarHarmonicSection_eq
    period hPeriod second sector circleMode]
  unfold primitiveSpinCScalarHarmonicSection
  rw [d9PrimitiveSpinCRealScalarMulSection_mul]
  rfl

/-- Raw quadratic products are symmetric in their coordinate labels. -/
theorem primitiveSpinCHopfSecondSphereProductSection_comm
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCHopfSecondSphereProductSection
        period hPeriod first second sector circleMode =
      primitiveSpinCHopfSecondSphereProductSection
        period hPeriod second first sector circleMode := by
  rw [
    primitiveSpinCHopfSecondSphereProductSection_eq_scalarHarmonicSection,
    primitiveSpinCHopfSecondSphereProductSection_eq_scalarHarmonicSection]
  ext base
  unfold primitiveSpinCScalarHarmonicSection
  rw [d9PrimitiveSpinCRealScalarMulSection_apply,
    d9PrimitiveSpinCRealScalarMulSection_apply]
  unfold primitiveSpinCSecondSphereProductScalar
  rw [mul_comm]

/-- Clifford differentiation of `nⱼ ψ` by `nᵢ` factors as
`nⱼ Clifford(dnᵢ) ψ`. -/
theorem primitiveSpinCHopfFirstSphereCoordinate_crossGradientFactor
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCScalarCliffordGradientSection
        period hPeriod .positiveQuarter
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
        (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod first)
        (primitiveSpinCHopfFirstSphereCoordinateSection
          period hPeriod second sector circleMode) =
      d9PrimitiveSpinCRealScalarMulSection
        period hPeriod .positiveQuarter
        (d9PrimitiveMonopoleBaseCoordinate period hPeriod second)
        (d9PrimitiveMonopoleBaseCoordinate_contMDiff
          period hPeriod second)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod first sector circleMode) := by
  rw [← primitiveSpinCFirstPositiveScalarHarmonicSection_eq
    period hPeriod second sector circleMode]
  unfold primitiveSpinCScalarHarmonicSection
  rw [d9PrimitiveSpinCScalarCliffordGradientSection_realScalarMul]
  congr 1
  exact primitiveSpinCFirstPositiveScalarHarmonicGradientSection_eq
    period hPeriod first sector circleMode

/-- First raw quadratic Dirac equation:
`D Qᵢⱼ = -k Qᵢⱼ + Uᵢⱼ`. -/
theorem primitiveSpinCHopfSecondSphereProductGeometricDiracOperator_eq
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfSecondSphereProductSection
          period hPeriod first second sector circleMode) =
      (-normalRootLeviCivitaCorrectedFrequency
          period sector circleMode) •
          primitiveSpinCHopfSecondSphereProductSection
            period hPeriod first second sector circleMode +
        primitiveSpinCHopfSecondSphereTangentialSection
          period hPeriod first second sector circleMode := by
  unfold primitiveSpinCHopfSecondSphereProductSection
    primitiveSpinCHopfSecondSphereTangentialSection
  rw [d9PrimitiveSpinCGeometricDiracOperator_realScalarMul,
    primitiveSpinCHopfFirstSphereCoordinateGeometricDiracOperator_eq,
    d9PrimitiveSpinCRealScalarMulSection_add,
    d9PrimitiveSpinCRealScalarMulSection_real_smul,
    primitiveSpinCHopfFirstSphereCoordinate_crossGradientFactor]
  module

/-- The symmetrized crossed gradient is the trace-corrected raw quadratic
section. -/
theorem primitiveSpinCHopfFirstSphereTangential_crossGradient_eq_productSection
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod first)
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod second sector circleMode) +
        d9PrimitiveSpinCScalarCliffordGradientSection
          period hPeriod .positiveQuarter
          (d9PrimitiveMonopoleBaseCoordinate period hPeriod second)
          (d9PrimitiveMonopoleBaseCoordinate_contMDiff
            period hPeriod second)
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod first sector circleMode) =
      (2 : Real) •
          primitiveSpinCHopfSecondSphereProductSection
            period hPeriod first second sector circleMode -
        (2 * d9KroneckerDelta first second) •
          primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode := by
  rw [primitiveSpinCHopfFirstSphereTangential_crossGradient,
    primitiveSpinCHopfSecondSphereProductSection_eq_scalarHarmonicSection]
  rfl

/-- Second raw quadratic Dirac equation:
`D Uᵢⱼ = 6 Qᵢⱼ - 2 δᵢⱼ ψ + k Uᵢⱼ`. -/
theorem primitiveSpinCHopfSecondSphereTangentialGeometricDiracOperator_eq
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfSecondSphereTangentialSection
          period hPeriod first second sector circleMode) =
      (6 : Real) •
          primitiveSpinCHopfSecondSphereProductSection
            period hPeriod first second sector circleMode -
        (2 * d9KroneckerDelta first second) •
          primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode +
        normalRootLeviCivitaCorrectedFrequency
            period sector circleMode •
          primitiveSpinCHopfSecondSphereTangentialSection
            period hPeriod first second sector circleMode := by
  let q : SmoothSection period hPeriod :=
    primitiveSpinCHopfSecondSphereProductSection
      period hPeriod first second sector circleMode
  let qSwap : SmoothSection period hPeriod :=
    primitiveSpinCHopfSecondSphereProductSection
      period hPeriod second first sector circleMode
  let firstPart : SmoothSection period hPeriod :=
    d9PrimitiveSpinCRealScalarMulSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod first)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod second sector circleMode)
  let secondPart : SmoothSection period hPeriod :=
    d9PrimitiveSpinCRealScalarMulSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod second)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod second)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod first sector circleMode)
  let firstGradient : SmoothSection period hPeriod :=
    d9PrimitiveSpinCScalarCliffordGradientSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod first)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod first)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod second sector circleMode)
  let secondGradient : SmoothSection period hPeriod :=
    d9PrimitiveSpinCScalarCliffordGradientSection
      period hPeriod .positiveQuarter
      (d9PrimitiveMonopoleBaseCoordinate period hPeriod second)
      (d9PrimitiveMonopoleBaseCoordinate_contMDiff
        period hPeriod second)
      (primitiveSpinCHopfFirstSphereTangentialSection
        period hPeriod first sector circleMode)
  let zeroMode : SmoothSection period hPeriod :=
    primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode
  let frequency : Real :=
    normalRootLeviCivitaCorrectedFrequency period sector circleMode
  change
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter (firstPart + secondPart) =
      (6 : Real) • q -
        (2 * d9KroneckerDelta first second) • zeroMode +
        frequency • (firstPart + secondPart)
  have hFirst :
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter firstPart =
        (2 : Real) • q + frequency • firstPart + firstGradient := by
    dsimp only [firstPart, q, firstGradient, frequency]
    rw [d9PrimitiveSpinCGeometricDiracOperator_realScalarMul,
      primitiveSpinCHopfFirstSphereTangentialGeometricDiracOperator_eq,
      d9PrimitiveSpinCRealScalarMulSection_add,
      d9PrimitiveSpinCRealScalarMulSection_real_smul,
      d9PrimitiveSpinCRealScalarMulSection_real_smul]
    rfl
  have hSecond :
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter secondPart =
        (2 : Real) • qSwap + frequency • secondPart +
          secondGradient := by
    dsimp only [secondPart, qSwap, secondGradient, frequency]
    rw [d9PrimitiveSpinCGeometricDiracOperator_realScalarMul,
      primitiveSpinCHopfFirstSphereTangentialGeometricDiracOperator_eq,
      d9PrimitiveSpinCRealScalarMulSection_add,
      d9PrimitiveSpinCRealScalarMulSection_real_smul,
      d9PrimitiveSpinCRealScalarMulSection_real_smul]
    rfl
  have hProductComm : qSwap = q := by
    exact primitiveSpinCHopfSecondSphereProductSection_comm
      period hPeriod second first sector circleMode
  have hCross :
      firstGradient + secondGradient =
        (2 : Real) • q -
          (2 * d9KroneckerDelta first second) • zeroMode := by
    exact
      primitiveSpinCHopfFirstSphereTangential_crossGradient_eq_productSection
        period hPeriod first second sector circleMode
  rw [d9PrimitiveSpinCGeometricDiracOperator_add,
    hFirst, hSecond, hProductComm]
  calc
    _ =
        (4 : Real) • q + (firstGradient + secondGradient) +
          frequency • (firstPart + secondPart) := by
      module
    _ = _ := by
      rw [hCross]
      module

/-- Squaring the raw quadratic block leaves exactly its trace defect. -/
theorem primitiveSpinCHopfSecondSphereProductGeometricDiracOperator_sq
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfSecondSphereProductSection
            period hPeriod first second sector circleMode)) =
      (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 + 6) •
          primitiveSpinCHopfSecondSphereProductSection
            period hPeriod first second sector circleMode -
        (2 * d9KroneckerDelta first second) •
          primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode := by
  rw [
    primitiveSpinCHopfSecondSphereProductGeometricDiracOperator_eq,
    d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    primitiveSpinCHopfSecondSphereProductGeometricDiracOperator_eq,
    primitiveSpinCHopfSecondSphereTangentialGeometricDiracOperator_eq]
  module

/-- Squared Dirac is additive on genuine smooth sections. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_sq_add
    (first second : SmoothSection period hPeriod) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter (first + second)) =
      d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter first) +
        d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter second) := by
  rw [d9PrimitiveSpinCGeometricDiracOperator_add,
    d9PrimitiveSpinCGeometricDiracOperator_add]

/-- Squared Dirac commutes with constant real scaling. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_sq_real_smul
    (coefficient : Real) (state : SmoothSection period hPeriod) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter (coefficient • state)) =
      coefficient •
        d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (d9PrimitiveSpinCGeometricDiracOperator
            period hPeriod .positiveQuarter state) := by
  rw [d9PrimitiveSpinCGeometricDiracOperator_real_smul,
    d9PrimitiveSpinCGeometricDiracOperator_real_smul]

/-- Squared Dirac commutes with additive negation. -/
theorem d9PrimitiveSpinCGeometricDiracOperator_sq_neg
    (state : SmoothSection period hPeriod) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter (-state)) =
      -d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter state) := by
  simpa using
    d9PrimitiveSpinCGeometricDiracOperator_sq_real_smul
      period hPeriod (-1 : Real) state

/-- The standard five-dimensional real trace-free quadratic packet. -/
def primitiveSpinCHopfSecondSphereTraceFreeSection
    (multiplicity : Fin 5)
    (sector : NormalRootChoice) (circleMode : Int) :
    SmoothSection period hPeriod :=
  ![
    primitiveSpinCHopfSecondSphereProductSection
        period hPeriod 0 0 sector circleMode +
      (-1 : Real) •
        primitiveSpinCHopfSecondSphereProductSection
          period hPeriod 1 1 sector circleMode,
    (2 : Real) •
      primitiveSpinCHopfSecondSphereProductSection
        period hPeriod 0 1 sector circleMode,
    (2 : Real) •
      primitiveSpinCHopfSecondSphereProductSection
        period hPeriod 0 2 sector circleMode,
    (2 : Real) •
      primitiveSpinCHopfSecondSphereProductSection
        period hPeriod 1 2 sector circleMode,
    (2 : Real) •
        primitiveSpinCHopfSecondSphereProductSection
          period hPeriod 2 2 sector circleMode +
      (-1 : Real) •
        primitiveSpinCHopfSecondSphereProductSection
          period hPeriod 0 0 sector circleMode +
      (-1 : Real) •
        primitiveSpinCHopfSecondSphereProductSection
          period hPeriod 1 1 sector circleMode
  ] multiplicity

/-- Every member of the five-dimensional trace-free packet is a genuine
`D²` eigensection with sphere energy six. -/
theorem primitiveSpinCHopfSecondSphereTraceFreeGeometricDiracOperator_sq
    (multiplicity : Fin 5)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (d9PrimitiveSpinCGeometricDiracOperator
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfSecondSphereTraceFreeSection
            period hPeriod multiplicity sector circleMode)) =
      (normalRootLeviCivitaCorrectedFrequency
            period sector circleMode ^ 2 + 6) •
        primitiveSpinCHopfSecondSphereTraceFreeSection
          period hPeriod multiplicity sector circleMode := by
  fin_cases multiplicity <;>
    simp [primitiveSpinCHopfSecondSphereTraceFreeSection,
      d9PrimitiveSpinCGeometricDiracOperator_sq_add,
      d9PrimitiveSpinCGeometricDiracOperator_sq_real_smul,
      d9PrimitiveSpinCGeometricDiracOperator_sq_neg,
      primitiveSpinCHopfSecondSphereProductGeometricDiracOperator_sq,
      d9KroneckerDelta] <;>
    module

/-- The five scalar trace-free quadratic harmonics underlying the section
packet. -/
def primitiveSpinCSecondSphereTraceFreeScalar
    (multiplicity : Fin 5) :
    ThroatBase period hPeriod → Real :=
  ![
    fun base =>
      primitiveSpinCSecondSphereProductScalar
          period hPeriod 0 0 base -
        primitiveSpinCSecondSphereProductScalar
          period hPeriod 1 1 base,
    (fun _ : ThroatBase period hPeriod => (2 : Real)) *
      primitiveSpinCSecondSphereProductScalar
        period hPeriod 0 1,
    (fun _ : ThroatBase period hPeriod => (2 : Real)) *
      primitiveSpinCSecondSphereProductScalar
        period hPeriod 0 2,
    (fun _ : ThroatBase period hPeriod => (2 : Real)) *
      primitiveSpinCSecondSphereProductScalar
        period hPeriod 1 2,
    fun base =>
      2 * primitiveSpinCSecondSphereProductScalar
          period hPeriod 2 2 base -
        primitiveSpinCSecondSphereProductScalar
          period hPeriod 0 0 base -
        primitiveSpinCSecondSphereProductScalar
          period hPeriod 1 1 base
  ] multiplicity

theorem primitiveSpinCSecondSphereTraceFreeScalar_contMDiff
    (multiplicity : Fin 5) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (primitiveSpinCSecondSphereTraceFreeScalar
        period hPeriod multiplicity) := by
  fin_cases multiplicity
  · simpa [primitiveSpinCSecondSphereTraceFreeScalar] using
      (primitiveSpinCSecondSphereProductScalar_contMDiff
          period hPeriod 0 0).sub
        (primitiveSpinCSecondSphereProductScalar_contMDiff
          period hPeriod 1 1)
  · simpa [primitiveSpinCSecondSphereTraceFreeScalar, Pi.mul_apply] using
      contMDiff_const.mul
        (primitiveSpinCSecondSphereProductScalar_contMDiff
          period hPeriod 0 1)
  · simpa [primitiveSpinCSecondSphereTraceFreeScalar, Pi.mul_apply] using
      contMDiff_const.mul
        (primitiveSpinCSecondSphereProductScalar_contMDiff
          period hPeriod 0 2)
  · simpa [primitiveSpinCSecondSphereTraceFreeScalar, Pi.mul_apply] using
      contMDiff_const.mul
        (primitiveSpinCSecondSphereProductScalar_contMDiff
          period hPeriod 1 2)
  · simpa [primitiveSpinCSecondSphereTraceFreeScalar] using
      ((contMDiff_const.mul
          (primitiveSpinCSecondSphereProductScalar_contMDiff
            period hPeriod 2 2)).sub
        (primitiveSpinCSecondSphereProductScalar_contMDiff
          period hPeriod 0 0)).sub
        (primitiveSpinCSecondSphereProductScalar_contMDiff
          period hPeriod 1 1)

@[simp]
theorem primitiveSpinCHopfSecondSphereProductSection_apply
    (first second : Fin 3)
    (sector : NormalRootChoice) (circleMode : Int)
    (base : ThroatBase period hPeriod) :
    primitiveSpinCHopfSecondSphereProductSection
        period hPeriod first second sector circleMode base =
      primitiveSpinCSecondSphereProductScalar
          period hPeriod first second base •
        primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode base := by
  rw [
    primitiveSpinCHopfSecondSphereProductSection_eq_scalarHarmonicSection]
  exact d9PrimitiveSpinCRealScalarMulSection_apply
    period hPeriod .positiveQuarter
    (primitiveSpinCSecondSphereProductScalar
      period hPeriod first second)
    (primitiveSpinCSecondSphereProductScalar_contMDiff
      period hPeriod first second)
    (primitiveSpinCHopfZeroModeSection
      period hPeriod sector circleMode) base

/-- Multiplication by each scalar quadratic gives exactly the corresponding
trace-free section. -/
theorem primitiveSpinCSecondSphereScalarHarmonicSection_eq
    (multiplicity : Fin 5)
    (sector : NormalRootChoice) (circleMode : Int) :
    primitiveSpinCScalarHarmonicSection
        period hPeriod
        (primitiveSpinCSecondSphereTraceFreeScalar
          period hPeriod multiplicity)
        (primitiveSpinCSecondSphereTraceFreeScalar_contMDiff
          period hPeriod multiplicity)
        sector circleMode =
      primitiveSpinCHopfSecondSphereTraceFreeSection
        period hPeriod multiplicity sector circleMode := by
  ext base
  fin_cases multiplicity <;>
    simp [primitiveSpinCScalarHarmonicSection,
      primitiveSpinCSecondSphereTraceFreeScalar,
      primitiveSpinCHopfSecondSphereTraceFreeSection,
      d9PrimitiveSpinCRealScalarMulSection_apply] <;>
    module

theorem primitiveSpinCHarmonicSphereEnergy_one :
    primitiveSpinCHarmonicSphereEnergy 1 = 6 := by
  rw [primitiveSpinCHarmonicSphereEnergy_eq]
  norm_num

/-- Each of the five concrete scalar quadratics is an unconditional
Lichnerowicz seed for the second positive sphere level. -/
def primitiveSpinCSecondPositiveScalarHarmonicLichnerowiczSeed
    (multiplicity : Fin 5) :
    PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
      period hPeriod 1 where
  scalar :=
    primitiveSpinCSecondSphereTraceFreeScalar
      period hPeriod multiplicity
  scalar_contMDiff :=
    primitiveSpinCSecondSphereTraceFreeScalar_contMDiff
      period hPeriod multiplicity
  dirac_sq_scalar := by
    intro sector circleMode
    rw [primitiveSpinCSecondSphereScalarHarmonicSection_eq]
    simpa [primitiveSpinCHarmonicSphereEnergy_one] using
      primitiveSpinCHopfSecondSphereTraceFreeGeometricDiracOperator_sq
        period hPeriod multiplicity sector circleMode

/-- The primitive-monopole degeneracy at sphere level `p = 2` is five. -/
theorem primitiveSphereModeDegeneracy_two :
    primitiveSphereModeDegeneracy 2 = 5 := by
  norm_num [primitiveSphereModeDegeneracy]

/-- The concrete packet, indexed by the canonical all-level multiplicity
type. -/
def primitiveSpinCSecondPositiveScalarHarmonicLichnerowiczPacket
    (multiplicity : Fin (primitiveSphereModeDegeneracy (1 + 1))) :
    PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
      period hPeriod 1 :=
  primitiveSpinCSecondPositiveScalarHarmonicLichnerowiczSeed
    period hPeriod
    (Fin.cast (by norm_num [primitiveSphereModeDegeneracy]) multiplicity)

/-- A rational unit-sphere point used to certify independence of the five
quadratic harmonics. -/
def primitiveSpinCSecondSphereRationalPoint
    (x y z : Real) (hUnit : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    MonopoleSphere := by
  refine ⟨WithLp.toLp 2 ![x, y, z], ?_⟩
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_succ]
  linarith

/-- Five rational sphere witnesses giving a nonsingular evaluation matrix. -/
def primitiveSpinCSecondSphereWitnessPoint
    (witness : Fin 5) : MonopoleSphere :=
  ![
    primitiveSpinCSecondSphereRationalPoint 1 0 0 (by norm_num),
    primitiveSpinCSecondSphereRationalPoint 0 1 0 (by norm_num),
    primitiveSpinCSecondSphereRationalPoint
      (3 / 5 : Real) (4 / 5 : Real) 0 (by norm_num),
    primitiveSpinCSecondSphereRationalPoint
      (3 / 5 : Real) 0 (4 / 5 : Real) (by norm_num),
    primitiveSpinCSecondSphereRationalPoint
      0 (3 / 5 : Real) (4 / 5 : Real) (by norm_num)
  ] witness

def primitiveSpinCSecondSphereWitnessCover
    (witness : Fin 5) : ThroatCover period hPeriod :=
  ⟨equatorialTwoSphereHomeomorph.symm
      (primitiveSpinCSecondSphereWitnessPoint witness), 0⟩

def primitiveSpinCSecondSphereWitnessBase
    (witness : Fin 5) : ThroatBase period hPeriod :=
  mappingTorusMk (ThroatData period hPeriod)
    (primitiveSpinCSecondSphereWitnessCover
      period hPeriod witness)

@[simp]
theorem primitiveSpinCSecondSphereWitnessCover_sphere
    (witness : Fin 5) :
    d9MonopoleSphereCoverProjection period hPeriod
        (primitiveSpinCSecondSphereWitnessCover
          period hPeriod witness) =
      primitiveSpinCSecondSphereWitnessPoint witness := by
  simp [primitiveSpinCSecondSphereWitnessCover,
    d9MonopoleSphereCoverProjection]

@[simp]
theorem primitiveSpinCSecondSphereWitnessBase_coordinate
    (witness : Fin 5) (coordinate : Fin 3) :
    d9PrimitiveMonopoleBaseCoordinate
        period hPeriod coordinate
        (primitiveSpinCSecondSphereWitnessBase
          period hPeriod witness) =
      monopoleSphereCoordinate
        (primitiveSpinCSecondSphereWitnessPoint witness) coordinate := by
  unfold d9PrimitiveMonopoleBaseCoordinate
    primitiveSpinCSecondSphereWitnessBase
  rw [d9ThroatMonopoleSphereProjection_mk,
    primitiveSpinCSecondSphereWitnessCover_sphere]

/-- North primitive-SpinC chart attached to one quadratic witness. -/
def primitiveSpinCSecondSphereWitnessIndex
    (witness : Fin 5) :
    D9PrimitiveSpinCIndex period hPeriod :=
  (primitiveSpinCSecondSphereWitnessCover
    period hPeriod witness, .north)

theorem primitiveSpinCSecondSphereWitnessBase_mem
    (witness : Fin 5) :
    primitiveSpinCSecondSphereWitnessBase
        period hPeriod witness ∈
      d9PrimitiveSpinCBaseSet period hPeriod
        (primitiveSpinCSecondSphereWitnessIndex
          period hPeriod witness) := by
  constructor
  · exact ((mappingTorusMk_isCoveringMap
      (ThroatData period hPeriod)).isLocalHomeomorph)
      |>.apply_self_mem_localInverseAt_source
  · change
      d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCSecondSphereWitnessBase
            period hPeriod witness) ∈
        monopoleChartDomain .north
    rw [primitiveSpinCSecondSphereWitnessBase,
      d9ThroatMonopoleSphereProjection_mk,
      primitiveSpinCSecondSphereWitnessCover_sphere]
    fin_cases witness <;>
      norm_num [monopoleChartDomain,
        primitiveSpinCSecondSphereWitnessPoint,
        primitiveSpinCSecondSphereRationalPoint,
        monopoleSphereCoordinate, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_fin_one]

/-- The normal Fourier matter at one quadratic witness. -/
def primitiveSpinCSecondSphereWitnessMode
    (witness : Fin 5) (sector : NormalRootChoice) (mode : Int) :
    D9DoubledMatterFiber :=
  primitiveSpinCNormalModeDoubledLift
    period hPeriod sector mode
    (primitiveSpinCSecondSphereWitnessCover
      period hPeriod witness)

theorem primitiveSpinCSecondSphereWitnessMode_halfSpinor
    (witness : Fin 5) (sector : NormalRootChoice) (mode : Int) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (primitiveSpinCSecondSphereWitnessMode
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
    simp [primitiveSpinCSecondSphereWitnessMode,
      primitiveSpinCSecondSphereWitnessCover,
      primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      normalRootSpinFramePhase, normalRootSpinFramePhaseAngle,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      ambientHalfGammaPositiveEigenvector, zero_apply]

@[simp]
theorem primitiveSpinCSecondSphereWitnessMode_sectorCoefficient
    (witness : Fin 5) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (primitiveSpinCSecondSphereWitnessMode
          period hPeriod witness sector mode) = 1 := by
  cases sector
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (primitiveSpinCSecondSphereWitnessMode
          period hPeriod witness .positiveQuarter mode)).1 0 = 1
    rw [primitiveSpinCSecondSphereWitnessMode_halfSpinor]
    rfl
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (primitiveSpinCSecondSphereWitnessMode
          period hPeriod witness .negativeQuarter mode)).2 0 = 1
    rw [primitiveSpinCSecondSphereWitnessMode_halfSpinor]
    rfl

@[simp]
theorem primitiveSpinCSecondSphereWitnessMode_gamma_two_sectorCoefficient
    (witness : Fin 5) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCSecondSphereWitnessMode
            period hPeriod witness sector mode)) = 0 := by
  cases sector
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCSecondSphereWitnessMode
            period hPeriod witness .positiveQuarter mode))).1 0 = 0
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_two,
      primitiveSpinCSecondSphereWitnessMode_halfSpinor]
    simp
  · change
      (d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9DoubledMatterFiberCliffordGammaCLM 2
          (primitiveSpinCSecondSphereWitnessMode
            period hPeriod witness .negativeQuarter mode))).2 0 = 0
    rw [d9DoubledMatterFiberCliffordGammaCLM_apply,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
      d9DoubledMatterSpinorCliffordGamma_two,
      primitiveSpinCSecondSphereWitnessMode_halfSpinor]
    simp

/-- Local Hopf zero-mode value at one quadratic witness. -/
def primitiveSpinCSecondSphereHopfZeroLocal
    (witness : Fin 5) (sector : NormalRootChoice) (mode : Int) :
    D9DoubledMatterFiber :=
  primitiveSpinCGeometricSectionLocalCoordinate
    period hPeriod
    (primitiveSpinCSecondSphereWitnessIndex
      period hPeriod witness)
    (primitiveSpinCSecondSphereWitnessBase
      period hPeriod witness)
    (primitiveSpinCHopfZeroModeSection
      period hPeriod sector mode)

@[simp]
theorem
    primitiveSpinCSecondSphereWitnessMode_firstFrame_sectorCoefficient
    (witness : Fin 5) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (d9PrimitiveSpinCHopfFirstFrameCLM sector
          (primitiveSpinCSecondSphereWitnessMode
            period hPeriod witness sector mode)) = 1 := by
  rw [d9PrimitiveSpinCHopfFirstFrameCLM_apply, map_sub,
    ← d9PrimitiveSpinCComplexAction_I,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction,
    primitiveSpinCSecondSphereWitnessMode_sectorCoefficient,
    primitiveSpinCSecondSphereWitnessMode_gamma_two_sectorCoefficient]
  simp

@[simp]
theorem
    primitiveSpinCSecondSphereWitnessMode_secondFrame_sectorCoefficient
    (witness : Fin 5) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (d9PrimitiveSpinCHopfSecondFrameCLM sector
          (primitiveSpinCSecondSphereWitnessMode
            period hPeriod witness sector mode)) = 1 := by
  rw [d9PrimitiveSpinCHopfSecondFrameCLM_apply, map_add,
    ← d9PrimitiveSpinCComplexAction_I,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction,
    primitiveSpinCSecondSphereWitnessMode_sectorCoefficient,
    primitiveSpinCSecondSphereWitnessMode_gamma_two_sectorCoefficient]
  simp

theorem primitiveSpinCSecondSphereHopfZeroLocal_sectorCoefficient
    (witness : Fin 5) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        (primitiveSpinCSecondSphereHopfZeroLocal
          period hPeriod witness sector mode) =
      primitiveMonopoleZeroNorthValue
          (primitiveSpinCSecondSphereWitnessPoint witness) +
        primitiveMonopoleZeroComplementNorthValue
          (primitiveSpinCSecondSphereWitnessPoint witness) := by
  unfold primitiveSpinCSecondSphereHopfZeroLocal
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
    period hPeriod sector mode
    (primitiveSpinCSecondSphereWitnessIndex
      period hPeriod witness)
    (primitiveSpinCSecondSphereWitnessBase
      period hPeriod witness)
    (primitiveSpinCSecondSphereWitnessBase_mem
      period hPeriod witness)]
  change
    primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (primitiveSpinCSecondSphereWitnessCover
              period hPeriod witness, .north)
            (mappingTorusMk (ThroatData period hPeriod)
              (primitiveSpinCSecondSphereWitnessCover
                period hPeriod witness))) = _
  rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    primitiveSpinCSecondSphereWitnessCover_sphere, map_add,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction,
    primitiveSpinCGeometricZeroModeSectorFiberCoefficient_complexAction]
  change
    primitiveMonopoleZeroLocalValue .north
          (primitiveSpinCSecondSphereWitnessPoint witness) *
        primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          (d9PrimitiveSpinCHopfFirstFrameCLM sector
            (primitiveSpinCSecondSphereWitnessMode
              period hPeriod witness sector mode)) +
      primitiveMonopoleZeroComplementLocalValue .north
          (primitiveSpinCSecondSphereWitnessPoint witness) *
        primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector
          (d9PrimitiveSpinCHopfSecondFrameCLM sector
            (primitiveSpinCSecondSphereWitnessMode
              period hPeriod witness sector mode)) = _
  rw [
    primitiveSpinCSecondSphereWitnessMode_firstFrame_sectorCoefficient,
    primitiveSpinCSecondSphereWitnessMode_secondFrame_sectorCoefficient]
  simp [primitiveMonopoleZeroLocalValue,
    primitiveMonopoleZeroComplementLocalValue]

theorem primitiveSpinCSecondSphereHopfZeroLocal_ne_zero
    (witness : Fin 5) (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCSecondSphereHopfZeroLocal
        period hPeriod witness sector mode ≠ 0 := by
  intro hZero
  have hCoefficient := congrArg
    (primitiveSpinCGeometricZeroModeSectorFiberCoefficientLinearMap sector)
    hZero
  rw [primitiveSpinCSecondSphereHopfZeroLocal_sectorCoefficient] at hCoefficient
  simp only [map_zero] at hCoefficient
  have hReal := congrArg Complex.re hCoefficient
  fin_cases witness <;>
    norm_num [primitiveMonopoleZeroNorthValue,
      primitiveMonopoleZeroComplementNorthValue,
      primitiveSpinCSecondSphereWitnessPoint,
      primitiveSpinCSecondSphereRationalPoint,
      monopoleSphereCoordinate, monopoleSphereXY,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_fin_one,
      Complex.real_smul] at hReal
  have hSqrtFive : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  exact
    (ne_of_gt
      (add_pos
        (div_pos (by norm_num) hSqrtFive)
        (mul_pos (div_pos hSqrtFive (by norm_num)) (by norm_num))))
      hReal

/-- Local coordinates commute with multiplication by a smooth real scalar,
evaluated at the chosen base point. -/
theorem primitiveSpinCGeometricSectionLocalCoordinate_realScalarMul
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (scalar : ThroatBase period hPeriod → Real)
    (hScalar :
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ∞ scalar)
    (state : SmoothSection period hPeriod) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod index base
        (d9PrimitiveSpinCRealScalarMulSection
          period hPeriod .positiveQuarter scalar hScalar state) =
      scalar base •
        primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base state := by
  change
    ((d9PrimitiveSpinCVectorBundleCore
        period hPeriod .positiveQuarter).localTriv index
      |>.linearMapAt Real base)
        ((d9PrimitiveSpinCRealScalarMulSection
          period hPeriod .positiveQuarter scalar hScalar state) base) =
      scalar base •
        ((d9PrimitiveSpinCVectorBundleCore
          period hPeriod .positiveQuarter).localTriv index
        |>.linearMapAt Real base) (state base)
  rw [d9PrimitiveSpinCRealScalarMulSection_apply, map_smul]

/-- Explicit evaluation matrix of the five trace-free quadratics on the
five rational witnesses. -/
def primitiveSpinCSecondSphereWitnessValue
    (basis witness : Fin 5) : Real :=
  ![
    ![(1 : Real), -1, -(7 / 25), 9 / 25, -(9 / 25)] witness,
    ![(0 : Real), 0, 24 / 25, 0, 0] witness,
    ![(0 : Real), 0, 0, 24 / 25, 0] witness,
    ![(0 : Real), 0, 0, 0, 24 / 25] witness,
    ![(-1 : Real), -1, -1, 23 / 25, 23 / 25] witness
  ] basis

@[simp]
theorem primitiveSpinCSecondSphereTraceFreeScalar_witness
    (basis witness : Fin 5) :
    primitiveSpinCSecondSphereTraceFreeScalar
        period hPeriod basis
        (primitiveSpinCSecondSphereWitnessBase
          period hPeriod witness) =
      primitiveSpinCSecondSphereWitnessValue basis witness := by
  fin_cases basis <;> fin_cases witness <;>
    norm_num [primitiveSpinCSecondSphereTraceFreeScalar,
      primitiveSpinCSecondSphereProductScalar,
      primitiveSpinCSecondSphereWitnessValue,
      primitiveSpinCSecondSphereWitnessPoint,
      primitiveSpinCSecondSphereRationalPoint,
      monopoleSphereCoordinate, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_fin_one]

/-- The five concrete quadratic scalar harmonics are linearly independent. -/
theorem primitiveSpinCSecondSphereTraceFreeScalar_linearIndependent :
    LinearIndependent Real
      (fun multiplicity : Fin 5 =>
        primitiveSpinCSecondSphereTraceFreeScalar
          period hPeriod multiplicity) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients hSum multiplicity
  have hEvaluate (witness : Fin 5) :=
    congrArg
      (fun scalar : ThroatBase period hPeriod → Real =>
        scalar
          (primitiveSpinCSecondSphereWitnessBase
            period hPeriod witness))
      hSum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply,
    primitiveSpinCSecondSphereTraceFreeScalar_witness] at hEvaluate
  have hZero := hEvaluate (0 : Fin 5)
  have hOne := hEvaluate (1 : Fin 5)
  have hTwo := hEvaluate (2 : Fin 5)
  have hThree := hEvaluate (3 : Fin 5)
  have hFour := hEvaluate (4 : Fin 5)
  norm_num [Fin.sum_univ_succ,
    primitiveSpinCSecondSphereWitnessValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Fin.reduceFinMk] at hZero hOne hTwo hThree hFour
  have hCoefficientZero : coefficients 0 = 0 := by
    linarith
  have hCoefficientFourRaw :
      coefficients ((2 : Fin 3).succ.succ) = 0 := by
    linarith
  have hCoefficientFour : coefficients 4 = 0 := by
    simpa using hCoefficientFourRaw
  have hCoefficientOne : coefficients 1 = 0 := by
    linarith
  have hCoefficientTwo : coefficients 2 = 0 := by
    linarith
  have hCoefficientThreeRaw :
      coefficients ((2 : Fin 4).succ) = 0 := by
    linarith
  have hCoefficientThree : coefficients 3 = 0 := by
    simpa using hCoefficientThreeRaw
  fin_cases multiplicity
  · exact hCoefficientZero
  · exact hCoefficientOne
  · exact hCoefficientTwo
  · exact hCoefficientThree
  · exact hCoefficientFour

/-- At each rational witness, a trace-free quadratic section is its scalar
evaluation times the common nonzero Hopf local value. -/
theorem primitiveSpinCHopfSecondSphereTraceFreeSection_localCoordinate
    (basis witness : Fin 5)
    (sector : NormalRootChoice) (mode : Int) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCSecondSphereWitnessIndex
          period hPeriod witness)
        (primitiveSpinCSecondSphereWitnessBase
          period hPeriod witness)
        (primitiveSpinCHopfSecondSphereTraceFreeSection
          period hPeriod basis sector mode) =
      primitiveSpinCSecondSphereWitnessValue basis witness •
        primitiveSpinCSecondSphereHopfZeroLocal
          period hPeriod witness sector mode := by
  rw [← primitiveSpinCSecondSphereScalarHarmonicSection_eq]
  unfold primitiveSpinCScalarHarmonicSection
  rw [primitiveSpinCGeometricSectionLocalCoordinate_realScalarMul,
    primitiveSpinCSecondSphereTraceFreeScalar_witness]
  rfl

/-- The five genuine smooth `D²` eigensections at sphere level `p = 2`
are linearly independent for every normal-root sector and circle mode. -/
theorem primitiveSpinCHopfSecondSphereTraceFreeSection_linearIndependent
    (sector : NormalRootChoice) (mode : Int) :
    LinearIndependent Real
      (fun multiplicity : Fin 5 =>
        primitiveSpinCHopfSecondSphereTraceFreeSection
          period hPeriod multiplicity sector mode) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients hSum multiplicity
  have hEvaluate (witness : Fin 5) :
      (∑ basis : Fin 5,
          coefficients basis *
            primitiveSpinCSecondSphereWitnessValue basis witness) = 0 := by
    let localCoordinate :=
      primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCSecondSphereWitnessIndex
          period hPeriod witness)
        (primitiveSpinCSecondSphereWitnessBase
          period hPeriod witness)
    have hLocal := congrArg localCoordinate hSum
    dsimp only [localCoordinate] at hLocal
    simp only [map_sum, map_smul, map_zero,
      primitiveSpinCHopfSecondSphereTraceFreeSection_localCoordinate] at hLocal
    simp_rw [smul_smul] at hLocal
    rw [← Finset.sum_smul] at hLocal
    by_contra hScalar
    exact
      (smul_ne_zero hScalar
        (primitiveSpinCSecondSphereHopfZeroLocal_ne_zero
          period hPeriod witness sector mode)) hLocal
  have hZero := hEvaluate (0 : Fin 5)
  have hOne := hEvaluate (1 : Fin 5)
  have hTwo := hEvaluate (2 : Fin 5)
  have hThree := hEvaluate (3 : Fin 5)
  have hFour := hEvaluate (4 : Fin 5)
  norm_num [Fin.sum_univ_succ,
    primitiveSpinCSecondSphereWitnessValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Fin.reduceFinMk] at hZero hOne hTwo hThree hFour
  have hCoefficientZero : coefficients 0 = 0 := by
    linarith
  have hCoefficientFourRaw :
      coefficients ((2 : Fin 3).succ.succ) = 0 := by
    linarith
  have hCoefficientFour : coefficients 4 = 0 := by
    simpa using hCoefficientFourRaw
  have hCoefficientOne : coefficients 1 = 0 := by
    linarith
  have hCoefficientTwo : coefficients 2 = 0 := by
    linarith
  have hCoefficientThreeRaw :
      coefficients ((2 : Fin 4).succ) = 0 := by
    linarith
  have hCoefficientThree : coefficients 3 = 0 := by
    simpa using hCoefficientThreeRaw
  fin_cases multiplicity
  · exact hCoefficientZero
  · exact hCoefficientOne
  · exact hCoefficientTwo
  · exact hCoefficientThree
  · exact hCoefficientFour

/-- Canonical first-order Dirac seed generated by one concrete quadratic
Lichnerowicz seed. -/
def primitiveSpinCSecondPositiveHarmonicDiracSeed
    (multiplicity : Fin 5)
    (sector : NormalRootChoice) (circleMode : Int) :
    PrimitiveSpinCHarmonicDiracSeed4D
      period hPeriod 1 sector circleMode :=
  (primitiveSpinCSecondPositiveScalarHarmonicLichnerowiczSeed
    period hPeriod multiplicity).toDiracSeed sector circleMode

theorem primitiveSpinCSecondPositiveHarmonicDiracSeed_positive_eigen
    (multiplicity : Fin 5)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCSecondPositiveHarmonicDiracSeed
          period hPeriod multiplicity sector circleMode).positiveSection =
      primitiveSpinCHarmonicDiracFrequency
          period 1 sector circleMode •
        (primitiveSpinCSecondPositiveHarmonicDiracSeed
          period hPeriod multiplicity sector circleMode).positiveSection :=
  (primitiveSpinCSecondPositiveHarmonicDiracSeed
    period hPeriod multiplicity sector circleMode).positiveSection_eigen

theorem primitiveSpinCSecondPositiveHarmonicDiracSeed_negative_eigen
    (multiplicity : Fin 5)
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCSecondPositiveHarmonicDiracSeed
          period hPeriod multiplicity sector circleMode).negativeSection =
      (-primitiveSpinCHarmonicDiracFrequency
          period 1 sector circleMode) •
        (primitiveSpinCSecondPositiveHarmonicDiracSeed
          period hPeriod multiplicity sector circleMode).negativeSection :=
  (primitiveSpinCSecondPositiveHarmonicDiracSeed
    period hPeriod multiplicity sector circleMode).negativeSection_eigen

/-- Consolidated unconditional certificate for the complete concrete
`p = 2` scalar packet. -/
structure PrimitiveSpinCSecondPositiveSpherePacketCertificate4D where
  harmonic :
    Fin 5 →
      PrimitiveSpinCScalarHarmonicLichnerowiczSeed4D
        period hPeriod 1
  scalar_linearIndependent :
    LinearIndependent Real (fun multiplicity => (harmonic multiplicity).scalar)
  section_linearIndependent :
    ∀ (sector : NormalRootChoice) (mode : Int),
      LinearIndependent Real
        (fun multiplicity : Fin 5 =>
          primitiveSpinCHopfSecondSphereTraceFreeSection
            period hPeriod multiplicity sector mode)
  degeneracy : primitiveSphereModeDegeneracy 2 = 5

def primitiveSpinCSecondPositiveSpherePacketCertificate4D :
    PrimitiveSpinCSecondPositiveSpherePacketCertificate4D
      period hPeriod where
  harmonic :=
    primitiveSpinCSecondPositiveScalarHarmonicLichnerowiczSeed
      period hPeriod
  scalar_linearIndependent :=
    primitiveSpinCSecondSphereTraceFreeScalar_linearIndependent
      period hPeriod
  section_linearIndependent :=
    primitiveSpinCHopfSecondSphereTraceFreeSection_linearIndependent
      period hPeriod
  degeneracy := primitiveSphereModeDegeneracy_two

theorem primitiveSpinCSecondPositiveSpherePacket_gate :
    Nonempty
      (PrimitiveSpinCSecondPositiveSpherePacketCertificate4D
        period hPeriod) :=
  ⟨primitiveSpinCSecondPositiveSpherePacketCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
end JanusFormal
