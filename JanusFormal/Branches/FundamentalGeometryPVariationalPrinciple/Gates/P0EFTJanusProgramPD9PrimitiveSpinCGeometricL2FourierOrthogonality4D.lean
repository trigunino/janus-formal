import Mathlib.Analysis.InnerProductSpace.Orthogonal
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCZeroModeOrthogonality4D

/-!
# Fourier orthogonality in the intrinsic primitive SpinC L² product

The canonical quotient measure is first reduced to its round-sphere/time
fundamental domain.  The exact moving-frame factor then proves that blocks
with distinct circle modes in one normal-root sector are geometrically
orthogonal, independently of their sphere levels.  The explicit Hopf
half-spinor planes additionally prove exact orthogonality of the two
normal-root sectors for arbitrary levels and circle modes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Interval Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelFullSpectralSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeOrthogonality4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

/-- The same-sector Fourier cancellation on the unoriented canonical
half-open fundamental interval. -/
theorem normalRootSpinFrameExponential_fundamentalDomain_orthogonal
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (first second : Int)
    (hModes : first ≠ second) :
    (∫ time,
      (starRingEnd Complex)
          (normalRootSpinFrameExponential period choice first time) *
        normalRootSpinFrameExponential period choice second time
      ∂(volume.restrict (canonicalLatitudeTimeInterval period))) = 0 := by
  by_cases hPositive : 0 < period
  · have hIntegral :=
      normalRootSpinFrameExponential_orthogonal
        period hPeriod choice first second hModes
    rw [intervalIntegral.integral_of_le (le_of_lt hPositive)] at hIntegral
    simpa [canonicalLatitudeTimeInterval,
      min_eq_left (le_of_lt hPositive),
      max_eq_right (le_of_lt hPositive)] using hIntegral
  · have hNegative : period < 0 :=
      lt_of_le_of_ne (le_of_not_gt hPositive) hPeriod
    have hIntegral :=
      normalRootSpinFrameExponential_orthogonal
        period hPeriod choice first second hModes
    have hReversed :
        (∫ time in period..(0 : Real),
          (starRingEnd Complex)
              (normalRootSpinFrameExponential period choice first time) *
            normalRootSpinFrameExponential period choice second time) = 0 := by
      rw [intervalIntegral.integral_symm, hIntegral]
      simp
    rw [intervalIntegral.integral_of_le (le_of_lt hNegative)] at hReversed
    simpa [canonicalLatitudeTimeInterval,
      min_eq_right (le_of_lt hNegative),
      max_eq_left (le_of_lt hNegative)] using hReversed

private abbrev ThroatData :=
  fixedEquatorData period hPeriod

private abbrev ThroatBase :=
  MappingTorus (ThroatData period hPeriod)

private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance throatBaseMeasurableSpace :
    MeasurableSpace (ThroatBase period hPeriod) :=
  borel _

local instance throatBaseBorelSpace :
    BorelSpace (ThroatBase period hPeriod) where
  measurable_eq := rfl

@[simp]
theorem canonicalLatitudeThroatMap_eq_nullPacketMovingWitnessBase
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeThroatMap period hPeriod base =
      primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod base.1 base.2 := by
  rfl

/-- The moving cover representative equipped with either monopole chart. -/
def primitiveSpinCNullPacketMovingWitnessIndexAt
    (point : MonopoleSphere) (time : Real) (chart : MonopoleChart) :
    D9PrimitiveSpinCIndex period hPeriod :=
  (primitiveSpinCNullPacketMovingWitnessCover
    period hPeriod point time, chart)

theorem primitiveSpinCNullPacketMovingWitnessBase_mem_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (time : Real) :
    primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time ∈
      d9PrimitiveSpinCBaseSet period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart) := by
  constructor
  · exact ((mappingTorusMk_isCoveringMap
      (ThroatData period hPeriod)).isLocalHomeomorph)
      |>.apply_self_mem_localInverseAt_source
  · change
      d9ThroatMonopoleSphereProjection period hPeriod
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time) ∈
        monopoleChartDomain chart
    rw [primitiveSpinCNullPacketMovingWitnessBase,
      d9ThroatMonopoleSphereProjection_mk,
      primitiveSpinCNullPacketMovingWitnessCover_sphere]
    exact hChart

/-- Intrinsic pointwise pairing evaluated in one common installed local
coordinate. -/
theorem d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (first second : SmoothSection period hPeriod) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter first second base =
      d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base first)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod index base second) := by
  rw [
    primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
      period hPeriod index base hBase first,
    primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
      period hPeriod index base hBase second,
    d9PrimitiveSpinCPointwiseHermitianPairing_eq_coordChange
      period hPeriod .positiveQuarter index first second base]
  rfl

/-- The Hopf seed has the same exact moving Fourier factor in either
monopole chart. -/
theorem primitiveSpinCHopfZeroModeLocalCoordinate_moving_factor_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (mode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode)) := by
  let phase :=
    normalRootSpinFrameExponential period sector mode time
  let zeroMode :=
    primitiveSpinCNormalModeDoubledLift period hPeriod sector mode
      (primitiveSpinCNullPacketMovingWitnessCover
        period hPeriod point 0)
  have hFirst :
      d9PrimitiveSpinCHopfFirstFrameCLM sector
          (d9PrimitiveSpinCComplexActionCLM phase zeroMode) =
        d9PrimitiveSpinCComplexActionCLM phase
          (d9PrimitiveSpinCHopfFirstFrameCLM sector zeroMode) := by
    simp only [d9PrimitiveSpinCHopfFirstFrameCLM_apply]
    rw [← d9PrimitiveSpinCComplexAction_clifford,
      ← d9PrimitiveSpinCComplexAction_imaginary, map_sub]
  have hSecond :
      d9PrimitiveSpinCHopfSecondFrameCLM sector
          (d9PrimitiveSpinCComplexActionCLM phase zeroMode) =
        d9PrimitiveSpinCComplexActionCLM phase
          (d9PrimitiveSpinCHopfSecondFrameCLM sector zeroMode) := by
    simp only [d9PrimitiveSpinCHopfSecondFrameCLM_apply]
    rw [← d9PrimitiveSpinCComplexAction_clifford,
      ← d9PrimitiveSpinCComplexAction_imaginary, map_add]
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod sector mode
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point time chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart time),
    primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod sector mode
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point 0 chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point 0)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart 0)]
  change
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode).localValue
        (primitiveSpinCNullPacketMovingWitnessCover
          period hPeriod point time, chart)
        (mappingTorusMk (ThroatData period hPeriod)
          (primitiveSpinCNullPacketMovingWitnessCover
            period hPeriod point time)) =
      d9PrimitiveSpinCComplexActionCLM phase
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (primitiveSpinCNullPacketMovingWitnessCover
              period hPeriod point 0, chart)
            (mappingTorusMk (ThroatData period hPeriod)
              (primitiveSpinCNullPacketMovingWitnessCover
                period hPeriod point 0)))
  rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    primitiveSpinCNullPacketMovingWitnessCover_sphere,
    primitiveSpinCNullPacketMovingWitnessCover_sphere,
    primitiveSpinCNormalModeDoubledLift_moving_factor]
  change
    d9PrimitiveSpinCComplexActionCLM
          (primitiveMonopoleZeroLocalValue chart point)
          (d9PrimitiveSpinCHopfFirstFrameCLM sector
            (d9PrimitiveSpinCComplexActionCLM phase zeroMode)) +
        d9PrimitiveSpinCComplexActionCLM
          (primitiveMonopoleZeroComplementLocalValue chart point)
          (d9PrimitiveSpinCHopfSecondFrameCLM sector
            (d9PrimitiveSpinCComplexActionCLM phase zeroMode)) =
      d9PrimitiveSpinCComplexActionCLM phase
        (d9PrimitiveSpinCComplexActionCLM
            (primitiveMonopoleZeroLocalValue chart point)
            (d9PrimitiveSpinCHopfFirstFrameCLM sector zeroMode) +
          d9PrimitiveSpinCComplexActionCLM
            (primitiveMonopoleZeroComplementLocalValue chart point)
            (d9PrimitiveSpinCHopfSecondFrameCLM sector zeroMode))
  rw [hFirst, hSecond, map_add,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul]
  congr 1 <;> ring

theorem primitiveSpinCNormalModeDoubledLift_halfSpinor
    (sector : NormalRootChoice) (mode : Int)
    (point : MappingTorusCover (ThroatData period hPeriod)) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point) =
      match sector with
      | .positiveQuarter =>
          (normalRootSpinFramePhase period hPeriod sector mode point •
            ambientHalfGammaPositiveEigenvector, 0)
      | .negativeQuarter =>
          (0, normalRootSpinFramePhase period hPeriod sector mode point •
            ambientHalfGammaPositiveEigenvector) := by
  have zero_apply (choice : NormalRootChoice) :
      (0 : SmoothThroatMatterSpinorLift period hPeriod choice) point = 0 :=
    rfl
  cases sector <;>
    apply Prod.ext <;>
    funext index <;>
    fin_cases index <;>
    simp [primitiveSpinCNormalModeDoubledLift,
      normalRootMatterModeLift, normalRootMatterModeValue,
      d9MatterGammaPositiveEigenlineCLM_apply,
      d9MatterComplexAction, d9MatterGammaPositiveEigenvector,
      ambientHalfGammaPositiveEigenvector, zero_apply]

def ambientHalfGammaTransverseVector : AmbientHalfSpinor2 :=
  ![1, -Complex.I]

@[simp]
theorem d9DoubledMatterFiberHalfSpinorLinearEquiv_imaginaryAction
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9PrimitiveSpinCImaginaryAction matter) =
      Complex.I • d9DoubledMatterFiberHalfSpinorLinearEquiv matter := by
  unfold d9PrimitiveSpinCImaginaryAction
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9PrimitiveSpinCImaginaryPhase_coe]

@[simp]
theorem d9DoubledMatterFiberHalfSpinorLinearEquiv_imaginaryGammaTwo
    (matter : D9DoubledMatterFiber) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) =
      Complex.I • d9DoubledMatterSpinorCliffordGamma 2
        (d9DoubledMatterFiberHalfSpinorLinearEquiv matter) := by
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_imaginaryAction,
    d9DoubledMatterFiberCliffordGammaCLM_apply,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma]

theorem primitiveSpinCHopfZeroModeLocalCoordinate_positive_halfSpinor
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (mode : Int) (time : Real) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod .positiveQuarter mode)) =
      ((((primitiveMonopoleZeroLocalValue chart point +
              primitiveMonopoleZeroComplementLocalValue chart point) *
            normalRootSpinFramePhase period hPeriod .positiveQuarter mode
              (primitiveSpinCNullPacketMovingWitnessCover
                period hPeriod point time)) •
          ambientHalfGammaPositiveEigenvector),
        ((Complex.I *
              (primitiveMonopoleZeroLocalValue chart point -
                primitiveMonopoleZeroComplementLocalValue chart point) *
              normalRootSpinFramePhase period hPeriod .positiveQuarter mode
                (primitiveSpinCNullPacketMovingWitnessCover
                  period hPeriod point time)) •
          ambientHalfGammaTransverseVector)) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod .positiveQuarter mode
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point time chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart time)]
  change
    d9DoubledMatterFiberHalfSpinorLinearEquiv
      ((primitiveSpinCHopfZeroModeLocalGaugeFamily
        period hPeriod .positiveQuarter mode).localValue
          (primitiveSpinCNullPacketMovingWitnessCover
            period hPeriod point time, chart)
          (mappingTorusMk (ThroatData period hPeriod)
            (primitiveSpinCNullPacketMovingWitnessCover
              period hPeriod point time))) = _
  rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    primitiveSpinCNullPacketMovingWitnessCover_sphere, map_add]
  simp only [
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9PrimitiveSpinCHopfFirstFrameCLM_apply,
    d9PrimitiveSpinCHopfSecondFrameCLM_apply,
    map_sub, map_add,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_imaginaryGammaTwo,
    d9DoubledMatterSpinorCliffordGamma_two,
    primitiveSpinCNormalModeDoubledLift_halfSpinor]
  apply Prod.ext <;>
    funext coordinate <;>
    fin_cases coordinate <;>
    simp [ambientHalfGammaPositiveEigenvector,
      ambientHalfGammaTransverseVector] <;>
    ring

theorem primitiveSpinCHopfZeroModeLocalCoordinate_negative_halfSpinor
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (mode : Int) (time : Real) :
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod .negativeQuarter mode)) =
      (((Complex.I *
              (primitiveMonopoleZeroComplementLocalValue chart point -
                primitiveMonopoleZeroLocalValue chart point) *
              normalRootSpinFramePhase period hPeriod .negativeQuarter mode
                (primitiveSpinCNullPacketMovingWitnessCover
                  period hPeriod point time)) •
          ambientHalfGammaTransverseVector),
        (((primitiveMonopoleZeroLocalValue chart point +
              primitiveMonopoleZeroComplementLocalValue chart point) *
            normalRootSpinFramePhase period hPeriod .negativeQuarter mode
              (primitiveSpinCNullPacketMovingWitnessCover
                period hPeriod point time)) •
          ambientHalfGammaPositiveEigenvector)) := by
  rw [primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
      period hPeriod .negativeQuarter mode
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point time chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart time)]
  change
    d9DoubledMatterFiberHalfSpinorLinearEquiv
      ((primitiveSpinCHopfZeroModeLocalGaugeFamily
        period hPeriod .negativeQuarter mode).localValue
          (primitiveSpinCNullPacketMovingWitnessCover
            period hPeriod point time, chart)
          (mappingTorusMk (ThroatData period hPeriod)
            (primitiveSpinCNullPacketMovingWitnessCover
              period hPeriod point time))) = _
  rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    primitiveSpinCNullPacketMovingWitnessCover_sphere, map_add]
  simp only [
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9PrimitiveSpinCHopfFirstFrameCLM_apply,
    d9PrimitiveSpinCHopfSecondFrameCLM_apply,
    map_sub, map_add,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_imaginaryGammaTwo,
    d9DoubledMatterSpinorCliffordGamma_two,
    primitiveSpinCNormalModeDoubledLift_halfSpinor]
  apply Prod.ext <;>
    funext coordinate <;>
    fin_cases coordinate <;>
    simp [ambientHalfGammaPositiveEigenvector,
      ambientHalfGammaTransverseVector] <;>
    ring

/-- The two explicit Hopf half-spinor planes are Hermitian orthogonal. -/
theorem d9DoubledMatterSpinorHermitianPairing_sectorPlanes_eq_zero
    (positive negative : D9DoubledMatterFiber)
    (positiveFirst positiveSecond negativeFirst negativeSecond : Complex)
    (hPositive :
      d9DoubledMatterFiberHalfSpinorLinearEquiv positive =
        (positiveFirst • ambientHalfGammaPositiveEigenvector,
          positiveSecond • ambientHalfGammaTransverseVector))
    (hNegative :
      d9DoubledMatterFiberHalfSpinorLinearEquiv negative =
        (negativeFirst • ambientHalfGammaTransverseVector,
          negativeSecond • ambientHalfGammaPositiveEigenvector)) :
    d9DoubledMatterSpinorHermitianPairing positive negative = 0 := by
  have hPositiveFirst :
      matterFiberHalfSpinorLinearEquiv positive.1 =
        positiveFirst • ambientHalfGammaPositiveEigenvector := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.fst hPositive
  have hPositiveSecond :
      matterFiberHalfSpinorLinearEquiv positive.2 =
        positiveSecond • ambientHalfGammaTransverseVector := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.snd hPositive
  have hNegativeFirst :
      matterFiberHalfSpinorLinearEquiv negative.1 =
        negativeFirst • ambientHalfGammaTransverseVector := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.fst hNegative
  have hNegativeSecond :
      matterFiberHalfSpinorLinearEquiv negative.2 =
        negativeSecond • ambientHalfGammaPositiveEigenvector := by
    simpa [d9DoubledMatterFiberHalfSpinorLinearEquiv_apply]
      using congrArg Prod.snd hNegative
  unfold d9DoubledMatterSpinorHermitianPairing
    d9MatterSpinorHermitianPairing
  rw [hPositiveFirst, hPositiveSecond, hNegativeFirst, hNegativeSecond]
  have hOrthogonal (left right : Complex) :
      (starRingEnd Complex) left * right +
          (starRingEnd Complex) left * Complex.I *
            (right * Complex.I) =
        0 := by
    calc
      _ = (starRingEnd Complex) left * right *
          (1 + Complex.I * Complex.I) := by ring
      _ = 0 := by rw [Complex.I_mul_I]; simp
  simp [ambientHalfSpinorHermitianPairing,
    ambientPinCSpinorHermitianPairing, ambientHalfSpinorEmbed,
    ambientHalfGammaPositiveEigenvector, ambientHalfGammaTransverseVector,
    Fin.sum_univ_succ]
  rw [hOrthogonal, hOrthogonal, add_zero]

/-- Hopf zero modes from opposite normal-root sectors are pointwise
orthogonal in any common monopole chart. -/
theorem primitiveSpinCHopfZeroModeLocalCoordinate_sectors_orthogonal
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (positiveMode negativeMode : Int) (time : Real) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod .positiveQuarter positiveMode))
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod .negativeQuarter negativeMode)) =
      0 := by
  apply d9DoubledMatterSpinorHermitianPairing_sectorPlanes_eq_zero
    (positiveFirst :=
      (primitiveMonopoleZeroLocalValue chart point +
          primitiveMonopoleZeroComplementLocalValue chart point) *
        normalRootSpinFramePhase period hPeriod .positiveQuarter
          positiveMode
          (primitiveSpinCNullPacketMovingWitnessCover
            period hPeriod point time))
    (positiveSecond :=
      Complex.I *
        (primitiveMonopoleZeroLocalValue chart point -
          primitiveMonopoleZeroComplementLocalValue chart point) *
        normalRootSpinFramePhase period hPeriod .positiveQuarter
          positiveMode
          (primitiveSpinCNullPacketMovingWitnessCover
            period hPeriod point time))
    (negativeFirst :=
      Complex.I *
        (primitiveMonopoleZeroComplementLocalValue chart point -
          primitiveMonopoleZeroLocalValue chart point) *
        normalRootSpinFramePhase period hPeriod .negativeQuarter
          negativeMode
          (primitiveSpinCNullPacketMovingWitnessCover
            period hPeriod point time))
    (negativeSecond :=
      (primitiveMonopoleZeroLocalValue chart point +
          primitiveMonopoleZeroComplementLocalValue chart point) *
        normalRootSpinFramePhase period hPeriod .negativeQuarter
          negativeMode
          (primitiveSpinCNullPacketMovingWitnessCover
            period hPeriod point time))
  · exact primitiveSpinCHopfZeroModeLocalCoordinate_positive_halfSpinor
      period hPeriod point chart hChart positiveMode time
  · exact primitiveSpinCHopfZeroModeLocalCoordinate_negative_halfSpinor
      period hPeriod point chart hChart negativeMode time

/-- Local null multiplication is chart-independent. -/
theorem primitiveSpinCNullMultiplicationLocalCoordinate_moving_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (time : Real) (parameter : Complex)
    (state : SmoothSection period hPeriod) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullMultiplicationLinearMap
          period hPeriod parameter state) =
      d9PrimitiveSpinCComplexActionCLM
        (primitiveSpinCNullSphereScalar parameter point)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          state) := by
  rw [primitiveSpinCNullMultiplicationLinearMap_apply, map_sum]
  simp_rw [
    primitiveSpinCGeometricSectionLocalCoordinate_complexScalar_eq_action
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point time chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart time),
    primitiveSpinCCoordinateMultiplicationLinearMap_apply,
    primitiveSpinCGeometricSectionLocalCoordinate_realScalarMul,
    primitiveSpinCNullPacketMovingWitnessBase_coordinate]
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  rw [map_sum,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction]
  simp_rw [
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    map_smul]
  unfold primitiveSpinCNullSphereScalar
  simp_rw [← Complex.coe_smul, smul_smul]
  rw [← Finset.sum_smul]

/-- A null power is pointwise a scalar multiple of its sector Hopf seed. -/
theorem primitiveSpinCNullPowerLocalCoordinate_eq_hopf_scalar_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (time : Real) (parameter : Complex)
    (sector : NormalRootChoice) (mode : Int) (degree : Nat) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullPowerSection
          period hPeriod parameter sector mode degree) =
      d9PrimitiveSpinCComplexActionCLM
        ((primitiveSpinCNullSphereScalar parameter point) ^ degree)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector mode)) := by
  induction degree with
  | zero =>
      simp only [primitiveSpinCNullPowerSection_zero, pow_zero]
      rw [d9PrimitiveSpinCComplexAction_one]
  | succ degree inductionHypothesis =>
      rw [primitiveSpinCNullPowerSection_succ,
        primitiveSpinCNullMultiplicationLocalCoordinate_moving_at
          period hPeriod point chart hChart time parameter,
        inductionHypothesis,
        ← d9PrimitiveSpinCComplexAction_mul]
      congr 1
      simp [pow_succ, mul_comm]

/-- Arbitrary null powers from opposite normal-root sectors remain
pointwise orthogonal. -/
theorem primitiveSpinCNullPowerLocalCoordinate_sectors_orthogonal
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (time : Real)
    (positiveParameter negativeParameter : Complex)
    (positiveMode negativeMode : Int)
    (positiveDegree negativeDegree : Nat) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCNullPowerSection
            period hPeriod positiveParameter .positiveQuarter
              positiveMode positiveDegree))
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCNullPowerSection
            period hPeriod negativeParameter .negativeQuarter
              negativeMode negativeDegree)) =
      0 := by
  rw [
    primitiveSpinCNullPowerLocalCoordinate_eq_hopf_scalar_at
      period hPeriod point chart hChart time positiveParameter,
    primitiveSpinCNullPowerLocalCoordinate_eq_hopf_scalar_at
      period hPeriod point chart hChart time negativeParameter,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right,
    primitiveSpinCHopfZeroModeLocalCoordinate_sectors_orthogonal
      period hPeriod point chart hChart positiveMode negativeMode time,
    mul_zero, mul_zero]

/-- Every null-power section has one common Fourier factor in either
monopole chart. -/
theorem primitiveSpinCNullPowerLocalCoordinate_moving_factor_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (parameter : Complex)
    (sector : NormalRootChoice) (mode : Int)
    (degree : Nat) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullPowerSection
          period hPeriod parameter sector mode degree) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector mode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCNullPowerSection
            period hPeriod parameter sector mode degree)) := by
  induction degree with
  | zero =>
      simpa only [primitiveSpinCNullPowerSection_zero] using
        primitiveSpinCHopfZeroModeLocalCoordinate_moving_factor_at
          period hPeriod point chart hChart sector mode time
  | succ degree inductionHypothesis =>
      rw [primitiveSpinCNullPowerSection_succ,
        primitiveSpinCNullMultiplicationLocalCoordinate_moving_at
          period hPeriod point chart hChart time,
        primitiveSpinCNullMultiplicationLocalCoordinate_moving_at
          period hPeriod point chart hChart 0,
        inductionHypothesis,
        ← d9PrimitiveSpinCComplexAction_mul,
        ← d9PrimitiveSpinCComplexAction_mul,
        mul_comm]

/-- Every raw all-level block vector has exactly one moving-frame Fourier
factor in a common local coordinate. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_moving_factor
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (sphereLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int)
    (multiplicity : Fin (primitiveSphereModeDegeneracy sphereLevel))
    (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point time)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod sphereLevel sector circleMode multiplicity) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector circleMode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndex
            period hPeriod point 0)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod sphereLevel sector circleMode multiplicity)) := by
  let index : PrimitiveSpinCAllFullJointIndex :=
    ⟨(sector, circleMode), ⟨sphereLevel, multiplicity⟩⟩
  change
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndex
          period hPeriod point time)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCAllModeNullHarmonicRealSection
          period hPeriod
          (primitiveSpinCAllFullJointIndexEquiv index)) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector circleMode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndex
            period hPeriod point 0)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCAllModeNullHarmonicRealSection
            period hPeriod
            (primitiveSpinCAllFullJointIndexEquiv index)))
  rw [← primitiveSpinCAllFullJointFamily_eq_allMode]
  exact primitiveSpinCNullPowerLocalCoordinate_moving_factor
    period hPeriod point hNorth
    (primitiveSpinCFullLevelNullGeometricParameter
      sphereLevel multiplicity)
    sector circleMode sphereLevel time

theorem primitiveSpinCGeometricL2RawBlockFamily_moving_factor_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sphereLevel : Nat) (sector : NormalRootChoice)
    (circleMode : Int)
    (multiplicity : Fin (primitiveSphereModeDegeneracy sphereLevel))
    (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod sphereLevel sector circleMode multiplicity) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector circleMode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod sphereLevel sector circleMode multiplicity)) := by
  let index : PrimitiveSpinCAllFullJointIndex :=
    ⟨(sector, circleMode), ⟨sphereLevel, multiplicity⟩⟩
  change
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCAllModeNullHarmonicRealSection
          period hPeriod
          (primitiveSpinCAllFullJointIndexEquiv index)) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector circleMode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCAllModeNullHarmonicRealSection
            period hPeriod
            (primitiveSpinCAllFullJointIndexEquiv index)))
  rw [← primitiveSpinCAllFullJointFamily_eq_allMode]
  exact primitiveSpinCNullPowerLocalCoordinate_moving_factor_at
    period hPeriod point chart hChart
    (primitiveSpinCFullLevelNullGeometricParameter
      sphereLevel multiplicity)
    sector circleMode sphereLevel time

/-- Raw vectors from opposite normal-root sectors are pointwise orthogonal,
with arbitrary levels, modes and multiplicities. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_local_sectors_orthogonal
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (firstLevel secondLevel : Nat)
    (positiveMode negativeMode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel))
    (time : Real) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel .positiveQuarter positiveMode
              firstMultiplicity))
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod secondLevel .negativeQuarter negativeMode
              secondMultiplicity)) =
      0 := by
  let positiveIndex : PrimitiveSpinCAllFullJointIndex :=
    ⟨(.positiveQuarter, positiveMode),
      ⟨firstLevel, firstMultiplicity⟩⟩
  let negativeIndex : PrimitiveSpinCAllFullJointIndex :=
    ⟨(.negativeQuarter, negativeMode),
      ⟨secondLevel, secondMultiplicity⟩⟩
  change
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCAllModeNullHarmonicRealSection
            period hPeriod
            (primitiveSpinCAllFullJointIndexEquiv positiveIndex)))
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          (primitiveSpinCAllModeNullHarmonicRealSection
            period hPeriod
            (primitiveSpinCAllFullJointIndexEquiv negativeIndex))) =
      0
  rw [← primitiveSpinCAllFullJointFamily_eq_allMode,
    ← primitiveSpinCAllFullJointFamily_eq_allMode]
  exact
    primitiveSpinCNullPowerLocalCoordinate_sectors_orthogonal
      period hPeriod point chart hChart time
      (primitiveSpinCFullLevelNullGeometricParameter
        firstLevel firstMultiplicity)
      (primitiveSpinCFullLevelNullGeometricParameter
        secondLevel secondMultiplicity)
      positiveMode negativeMode firstLevel secondLevel

/-- The intrinsic pairing of two raw vectors in one sector separates into
the exact Fourier character and a time-zero sphere factor. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_pointwise_moving_factor
    (point : MonopoleSphere)
    (hNorth : point ∈ monopoleChartDomain .north)
    (firstLevel secondLevel : Nat) (sector : NormalRootChoice)
    (firstMode secondMode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel))
    (time : Real) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel sector firstMode firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel sector secondMode secondMultiplicity)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      ((starRingEnd Complex)
          (normalRootSpinFrameExponential
            period sector firstMode time) *
        normalRootSpinFrameExponential
          period sector secondMode time) *
      d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel sector firstMode firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel sector secondMode secondMultiplicity)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point 0) := by
  rw [
    d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndex
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem
        period hPeriod point hNorth time),
    primitiveSpinCGeometricL2RawBlockFamily_moving_factor
      period hPeriod point hNorth firstLevel sector firstMode
        firstMultiplicity time,
    primitiveSpinCGeometricL2RawBlockFamily_moving_factor
      period hPeriod point hNorth secondLevel sector secondMode
        secondMultiplicity time,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right,
    ← d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndex
        period hPeriod point 0)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point 0)
      (primitiveSpinCNullPacketMovingWitnessBase_mem
        period hPeriod point hNorth 0)]
  ring

theorem primitiveSpinCGeometricL2RawBlockFamily_pointwise_moving_factor_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (firstLevel secondLevel : Nat) (sector : NormalRootChoice)
    (firstMode secondMode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel))
    (time : Real) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel sector firstMode firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel sector secondMode secondMultiplicity)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      ((starRingEnd Complex)
          (normalRootSpinFrameExponential
            period sector firstMode time) *
        normalRootSpinFrameExponential
          period sector secondMode time) *
      d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel sector firstMode firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel sector secondMode secondMultiplicity)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point 0) := by
  rw [
    d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point time chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart time),
    primitiveSpinCGeometricL2RawBlockFamily_moving_factor_at
      period hPeriod point chart hChart firstLevel sector firstMode
        firstMultiplicity time,
    primitiveSpinCGeometricL2RawBlockFamily_moving_factor_at
      period hPeriod point chart hChart secondLevel sector secondMode
        secondMultiplicity time,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right,
    ← d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point 0 chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point 0)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart 0)]
  ring

theorem primitiveSpinCGeometricL2RawBlockFamily_pointwise_moving_factor_all
    (point : MonopoleSphere)
    (firstLevel secondLevel : Nat) (sector : NormalRootChoice)
    (firstMode secondMode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel))
    (time : Real) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel sector firstMode firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel sector secondMode secondMultiplicity)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      ((starRingEnd Complex)
          (normalRootSpinFrameExponential
            period sector firstMode time) *
        normalRootSpinFrameExponential
          period sector secondMode time) *
      d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel sector firstMode firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel sector secondMode secondMultiplicity)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point 0) := by
  obtain ⟨chart, hChart⟩ := monopoleChartDomain_cover point
  exact
    primitiveSpinCGeometricL2RawBlockFamily_pointwise_moving_factor_at
      period hPeriod point chart hChart firstLevel secondLevel sector
      firstMode secondMode firstMultiplicity secondMultiplicity time

/-- Opposite-sector raw vectors are intrinsically pointwise orthogonal. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_pointwise_sectors_orthogonal
    (point : MonopoleSphere)
    (firstLevel secondLevel : Nat)
    (positiveMode negativeMode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel))
    (time : Real) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel .positiveQuarter positiveMode
            firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel .negativeQuarter negativeMode
            secondMultiplicity)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      0 := by
  obtain ⟨chart, hChart⟩ := monopoleChartDomain_cover point
  rw [d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
    period hPeriod
    (primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart)
    (primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time)
    (primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time)]
  exact
    primitiveSpinCGeometricL2RawBlockFamily_local_sectors_orthogonal
      period hPeriod point chart hChart firstLevel secondLevel
      positiveMode negativeMode firstMultiplicity secondMultiplicity time

/-- Opposite normal-root sectors are exactly orthogonal in the independently
integrated geometric `L²` product. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_sectors_orthogonal
    (firstLevel secondLevel : Nat)
    (positiveMode negativeMode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel)) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel .positiveQuarter positiveMode
            firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel .negativeQuarter negativeMode
            secondMultiplicity) =
      0 := by
  rw [d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun base => by
    change
      d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel .positiveQuarter positiveMode
              firstMultiplicity)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod secondLevel .negativeQuarter negativeMode
              secondMultiplicity)
          (canonicalLatitudeThroatMap period hPeriod base) =
        0
    rw [canonicalLatitudeThroatMap_eq_nullPacketMovingWitnessBase]
    exact
      primitiveSpinCGeometricL2RawBlockFamily_pointwise_sectors_orthogonal
        period hPeriod base.1 firstLevel secondLevel positiveMode negativeMode
        firstMultiplicity secondMultiplicity base.2

/-- Raw multiplicity vectors with distinct circle modes in one sector are
orthogonal in the independently integrated geometric L² product. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_circleMode_orthogonal
    (firstLevel secondLevel : Nat) (sector : NormalRootChoice)
    (firstMode secondMode : Int) (hModes : firstMode ≠ secondMode)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel)) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel sector firstMode firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel sector secondMode secondMultiplicity) =
      0 := by
  rw [d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral]
  have hIntrinsic :=
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod .positiveQuarter
      (primitiveSpinCGeometricL2RawBlockFamily
        period hPeriod firstLevel sector firstMode firstMultiplicity)
      (primitiveSpinCGeometricL2RawBlockFamily
        period hPeriod secondLevel sector secondMode secondMultiplicity)
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
    at hIntrinsic
  have hPullback :
      Integrable
        (fun base : CanonicalLatitudeBase =>
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector firstMode firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector secondMode
                secondMultiplicity)
            (canonicalLatitudeThroatMap period hPeriod base))
        (canonicalLatitudeBaseMeasure period) := by
    simpa [Function.comp_def] using
      hIntrinsic.comp_measurable
        (canonicalLatitudeThroatMap_continuous
          period hPeriod).measurable
  unfold canonicalLatitudeBaseMeasure at hPullback ⊢
  rw [integral_prod _ hPullback]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun point => by
    change
      (∫ time,
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel sector firstMode firstMultiplicity)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod secondLevel sector secondMode secondMultiplicity)
          (canonicalLatitudeThroatMap period hPeriod (point, time))
        ∂(volume.restrict (canonicalLatitudeTimeInterval period))) = 0
    rw [show
        (fun time : Real =>
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector firstMode firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector secondMode
                secondMultiplicity)
            (canonicalLatitudeThroatMap period hPeriod (point, time))) =
          fun time : Real =>
            ((starRingEnd Complex)
                (normalRootSpinFrameExponential
                  period sector firstMode time) *
              normalRootSpinFrameExponential
                period sector secondMode time) *
            d9PrimitiveSpinCPointwiseHermitianPairing
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricL2RawBlockFamily
                period hPeriod firstLevel sector firstMode firstMultiplicity)
              (primitiveSpinCGeometricL2RawBlockFamily
                period hPeriod secondLevel sector secondMode
                  secondMultiplicity)
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point 0) by
      funext time
      rw [canonicalLatitudeThroatMap_eq_nullPacketMovingWitnessBase]
      exact
        primitiveSpinCGeometricL2RawBlockFamily_pointwise_moving_factor_all
          period hPeriod point firstLevel secondLevel sector
          firstMode secondMode firstMultiplicity secondMultiplicity time]
    rw [integral_mul_const,
      normalRootSpinFrameExponential_fundamentalDomain_orthogonal
        period hPeriod sector firstMode secondMode hModes]
    simp

/-- The complete finite multiplicity spans remain orthogonal across
distinct same-sector circle modes. -/
theorem primitiveSpinCGeometricL2RawBlockSpans_circleMode_isOrtho
    (firstLevel secondLevel : Nat) (sector : NormalRootChoice)
    (firstMode secondMode : Int) (hModes : firstMode ≠ secondMode) :
    Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel sector firstMode)) ⟂
      Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod secondLevel sector secondMode)) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro first hFirst second hSecond
  refine Submodule.span_induction
    (p := fun first _ => inner Complex first second = 0)
    ?_ (by simp) ?_ ?_ hFirst
  · rintro _ ⟨firstMultiplicity, rfl⟩
    refine Submodule.span_induction
      (p := fun second _ =>
        inner Complex
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel sector firstMode firstMultiplicity)
          second = 0)
      ?_ (by simp) ?_ ?_ hSecond
    · rintro _ ⟨secondMultiplicity, rfl⟩
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector firstMode firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector secondMode
                secondMultiplicity) = 0
      exact
        primitiveSpinCGeometricL2RawBlockFamily_circleMode_orthogonal
          period hPeriod firstLevel secondLevel sector firstMode secondMode
          hModes firstMultiplicity secondMultiplicity
    · intro left right _ _ hLeft hRight
      rw [inner_add_right, hLeft, hRight, add_zero]
    · intro scalar state _ hState
      rw [inner_smul_right, hState, mul_zero]
  · intro left right _ _ hLeft hRight
    rw [inner_add_left, hLeft, hRight, add_zero]
  · intro scalar state _ hState
    rw [inner_smul_left, hState, mul_zero]

/-- The complete finite multiplicity spans of the two normal-root sectors
are orthogonal. -/
theorem primitiveSpinCGeometricL2RawBlockSpans_sectors_isOrtho
    (firstLevel secondLevel : Nat)
    (positiveMode negativeMode : Int) :
    Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel .positiveQuarter positiveMode)) ⟂
      Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod secondLevel .negativeQuarter negativeMode)) := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro first hFirst second hSecond
  refine Submodule.span_induction
    (p := fun first _ => inner Complex first second = 0)
    ?_ (by simp) ?_ ?_ hFirst
  · rintro _ ⟨firstMultiplicity, rfl⟩
    refine Submodule.span_induction
      (p := fun second _ =>
        inner Complex
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel .positiveQuarter positiveMode
              firstMultiplicity)
          second = 0)
      ?_ (by simp) ?_ ?_ hSecond
    · rintro _ ⟨secondMultiplicity, rfl⟩
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel .positiveQuarter positiveMode
                firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel .negativeQuarter negativeMode
                secondMultiplicity) =
          0
      exact
        primitiveSpinCGeometricL2RawBlockFamily_sectors_orthogonal
          period hPeriod firstLevel secondLevel positiveMode negativeMode
          firstMultiplicity secondMultiplicity
    · intro left right _ _ hLeft hRight
      rw [inner_add_right, hLeft, hRight, add_zero]
    · intro scalar state _ hState
      rw [inner_smul_right, hState, mul_zero]
  · intro left right _ _ hLeft hRight
    rw [inner_add_left, hLeft, hRight, add_zero]
  · intro scalar state _ hState
    rw [inner_smul_left, hState, mul_zero]

theorem primitiveSpinCGeometricL2OrthonormalBlockFamily_circleMode_orthogonal
    (firstLevel secondLevel : Nat) (sector : NormalRootChoice)
    (firstMode secondMode : Int) (hModes : firstMode ≠ secondMode)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel)) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod firstLevel sector firstMode firstMultiplicity)
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod secondLevel sector secondMode secondMultiplicity) =
      0 := by
  have hFirst :
      primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod firstLevel sector firstMode firstMultiplicity ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector firstMode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span]
    exact Submodule.subset_span (Set.mem_range_self firstMultiplicity)
  have hSecond :
      primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod secondLevel sector secondMode secondMultiplicity ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector secondMode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span]
    exact Submodule.subset_span (Set.mem_range_self secondMultiplicity)
  have hOrthogonal :=
    (primitiveSpinCGeometricL2RawBlockSpans_circleMode_isOrtho
      period hPeriod firstLevel secondLevel sector firstMode secondMode
      hModes).inner_eq hFirst hSecond
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod firstLevel sector firstMode firstMultiplicity)
        (primitiveSpinCGeometricL2OrthonormalBlockFamily
          period hPeriod secondLevel sector secondMode secondMultiplicity) =
      0 at hOrthogonal
  exact hOrthogonal

/-- Arbitrary finite normalized block syntheses are orthogonal across
distinct same-sector circle modes. -/
theorem primitiveSpinCGeometricL2OrthonormalBlockSynthesis_circleMode_orthogonal
    (firstLevel secondLevel : Nat) (sector : NormalRootChoice)
    (firstMode secondMode : Int) (hModes : firstMode ≠ secondMode)
    (first :
      EuclideanSpace Complex
        (Fin (primitiveSphereModeDegeneracy firstLevel)))
    (second :
      EuclideanSpace Complex
        (Fin (primitiveSphereModeDegeneracy secondLevel))) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel sector firstMode first)
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel sector secondMode second) = 0 := by
  have hFirst :
      primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel sector firstMode first ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector firstMode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span]
    change
      (∑ multiplicity,
        first multiplicity •
          primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod firstLevel sector firstMode multiplicity) ∈ _
    apply Submodule.sum_mem
    intro multiplicity _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self multiplicity))
  have hSecond :
      primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel sector secondMode second ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector secondMode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span]
    change
      (∑ multiplicity,
        second multiplicity •
          primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod secondLevel sector secondMode multiplicity) ∈ _
    apply Submodule.sum_mem
    intro multiplicity _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self multiplicity))
  have hOrthogonal :=
    (primitiveSpinCGeometricL2RawBlockSpans_circleMode_isOrtho
      period hPeriod firstLevel secondLevel sector firstMode secondMode
      hModes).inner_eq hFirst hSecond
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel sector firstMode first)
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel sector secondMode second) = 0
    at hOrthogonal
  exact hOrthogonal

/-- Arbitrary finite normalized block syntheses from opposite sectors are
orthogonal, with no restriction on levels or circle modes. -/
theorem primitiveSpinCGeometricL2OrthonormalBlockSynthesis_sectors_orthogonal
    (firstLevel secondLevel : Nat)
    (positiveMode negativeMode : Int)
    (first :
      EuclideanSpace Complex
        (Fin (primitiveSphereModeDegeneracy firstLevel)))
    (second :
      EuclideanSpace Complex
        (Fin (primitiveSphereModeDegeneracy secondLevel))) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel .positiveQuarter positiveMode first)
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel .negativeQuarter negativeMode second) =
      0 := by
  have hFirst :
      primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel .positiveQuarter positiveMode first ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel .positiveQuarter positiveMode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span]
    change
      (∑ multiplicity,
        first multiplicity •
          primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod firstLevel .positiveQuarter positiveMode
              multiplicity) ∈ _
    apply Submodule.sum_mem
    intro multiplicity _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self multiplicity))
  have hSecond :
      primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel .negativeQuarter negativeMode second ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel .negativeQuarter negativeMode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span]
    change
      (∑ multiplicity,
        second multiplicity •
          primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod secondLevel .negativeQuarter negativeMode
              multiplicity) ∈ _
    apply Submodule.sum_mem
    intro multiplicity _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self multiplicity))
  have hOrthogonal :=
    (primitiveSpinCGeometricL2RawBlockSpans_sectors_isOrtho
      period hPeriod firstLevel secondLevel positiveMode negativeMode
      ).inner_eq hFirst hSecond
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod firstLevel .positiveQuarter positiveMode first)
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod secondLevel .negativeQuarter negativeMode second) =
      0 at hOrthogonal
  exact hOrthogonal

/-- Assumption-free certificate for the exact Fourier part of the
independent geometric `L²` comparison. -/
structure ProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonalityCertificate4D
    where
  fundamentalDomainReduction :
    ∀ (choice : NormalRootChoice)
      (first second :
        D9PrimitiveSpinCSmoothSection period hPeriod choice),
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod choice first second =
        ∫ base : CanonicalLatitudeBase,
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod choice first second
            (canonicalLatitudeThroatMap period hPeriod base)
          ∂(canonicalLatitudeBaseMeasure period)
  rawCircleModeOrthogonal :
    ∀ (firstLevel secondLevel : Nat) (sector : NormalRootChoice)
      (firstMode secondMode : Int), firstMode ≠ secondMode →
      ∀ (firstMultiplicity :
          Fin (primitiveSphereModeDegeneracy firstLevel))
        (secondMultiplicity :
          Fin (primitiveSphereModeDegeneracy secondLevel)),
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod firstLevel sector firstMode firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod secondLevel sector secondMode
                secondMultiplicity) =
          0
  rawSectorOrthogonal :
    ∀ (firstLevel secondLevel : Nat)
      (positiveMode negativeMode : Int)
      (firstMultiplicity :
        Fin (primitiveSphereModeDegeneracy firstLevel))
      (secondMultiplicity :
        Fin (primitiveSphereModeDegeneracy secondLevel)),
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod firstLevel .positiveQuarter positiveMode
              firstMultiplicity)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod secondLevel .negativeQuarter negativeMode
              secondMultiplicity) =
        0
  normalizedCircleModeOrthogonal :
    ∀ (firstLevel secondLevel : Nat) (sector : NormalRootChoice)
      (firstMode secondMode : Int), firstMode ≠ secondMode →
      ∀ (first :
          EuclideanSpace Complex
            (Fin (primitiveSphereModeDegeneracy firstLevel)))
        (second :
          EuclideanSpace Complex
            (Fin (primitiveSphereModeDegeneracy secondLevel))),
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
              period hPeriod firstLevel sector firstMode first)
            (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
              period hPeriod secondLevel sector secondMode second) =
          0
  normalizedSectorOrthogonal :
    ∀ (firstLevel secondLevel : Nat)
      (positiveMode negativeMode : Int)
      (first :
        EuclideanSpace Complex
          (Fin (primitiveSphereModeDegeneracy firstLevel)))
      (second :
        EuclideanSpace Complex
          (Fin (primitiveSphereModeDegeneracy secondLevel))),
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
            period hPeriod firstLevel .positiveQuarter positiveMode first)
          (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
            period hPeriod secondLevel .negativeQuarter negativeMode second) =
        0

def programPD9PrimitiveSpinCGeometricL2FourierOrthogonalityCertificate4D :
    ProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonalityCertificate4D
      period hPeriod where
  fundamentalDomainReduction :=
    d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral
      period hPeriod
  rawCircleModeOrthogonal :=
    primitiveSpinCGeometricL2RawBlockFamily_circleMode_orthogonal
      period hPeriod
  rawSectorOrthogonal :=
    primitiveSpinCGeometricL2RawBlockFamily_sectors_orthogonal
      period hPeriod
  normalizedCircleModeOrthogonal :=
    primitiveSpinCGeometricL2OrthonormalBlockSynthesis_circleMode_orthogonal
      period hPeriod
  normalizedSectorOrthogonal :=
    primitiveSpinCGeometricL2OrthonormalBlockSynthesis_sectors_orthogonal
      period hPeriod

theorem primitiveSpinCGeometricL2FourierOrthogonality_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonalityCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2FourierOrthogonalityCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D
end JanusFormal
