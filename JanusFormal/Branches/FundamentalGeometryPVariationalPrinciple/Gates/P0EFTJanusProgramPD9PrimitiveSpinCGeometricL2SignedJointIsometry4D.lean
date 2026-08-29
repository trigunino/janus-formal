import Mathlib.Analysis.InnerProductSpace.l2Space
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2JointIsometry4D

/-!
# Signed joint geometric L² isometry for the primitive SpinC tower

This module separates the complete positive-level signed packets along the
three commuting spectral labels, assembles their Hilbert direct sum, and
identifies its exact closed range in the independent geometric completion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D

set_option autoImplicit false
noncomputable section

open Bundle MeasureTheory Module Set
open scoped BigOperators ENNReal lp Manifold ContDiff
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelHarmonicDiagonalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelJointFourierSynthesis4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelNullHarmonicDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCFirstPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2BlockOrthonormalization4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2FourierOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2GradientCasimir4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2JointIsometry4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2LevelOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2RadialOrthogonality4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedBranchCompletion4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedMultiplicity4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexFiberAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexStructure4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSpectralRealization4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSecondPositiveSphereDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCZeroModeFourierSynthesis4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)
private abbrev SmoothSection :=
  D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter
private abbrev EuclideanR3 := EuclideanSpace Real (Fin 3)
private abbrev SphereMeasure : Measure MonopoleSphere :=
  (volume : Measure EuclideanR3).toSphere

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

/-! ## Fourier behavior of the gradient packet -/

/-- Every tangential Hopf partner carries the same normal Fourier factor as
its zero-mode seed, in either monopole chart. -/
theorem primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_moving_factor_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (circleMode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector circleMode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCHopfFirstSphereTangentialSection
            period hPeriod coordinate sector circleMode)) := by
  let timeIndex :=
    primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart
  let zeroIndex :=
    primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point 0 chart
  let timeBase :=
    primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time
  let zeroBase :=
    primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point 0
  let phase :=
    normalRootSpinFrameExponential
      period sector circleMode time
  let timeZeroCoordinate :=
    primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod timeIndex timeBase
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector circleMode)
  let zeroZeroCoordinate :=
    primitiveSpinCGeometricSectionLocalCoordinate
      period hPeriod zeroIndex zeroBase
      (primitiveSpinCHopfZeroModeSection
        period hPeriod sector circleMode)
  have hTimeMem :
      timeBase ∈ d9PrimitiveSpinCBaseSet period hPeriod timeIndex :=
    primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time
  have hZeroMem :
      zeroBase ∈ d9PrimitiveSpinCBaseSet period hPeriod zeroIndex :=
    primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart 0
  have hZeroFactor :
      timeZeroCoordinate =
        d9PrimitiveSpinCComplexActionCLM phase zeroZeroCoordinate := by
    exact
      primitiveSpinCHopfZeroModeLocalCoordinate_moving_factor_at
        period hPeriod point chart hChart sector circleMode time
  have hRadial :
      d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod coordinate timeBase =
        d9PrimitiveSpinCBaseUnitRadialCoordinate
          period hPeriod coordinate zeroBase := by
    simp [timeBase, zeroBase, d9PrimitiveSpinCBaseUnitRadialCoordinate,
      primitiveSpinCNullPacketMovingWitnessBase_coordinate]
  have hGamma :
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          (d9PrimitiveSpinCComplexActionCLM phase zeroZeroCoordinate) =
        d9PrimitiveSpinCComplexActionCLM phase
          (d9DoubledMatterFiberCliffordGammaCLM
            coordinate zeroZeroCoordinate) := by
    rw [← d9PrimitiveSpinCComplexAction_clifford]
  have hImaginary :
      d9PrimitiveSpinCImaginaryAction
          (d9PrimitiveSpinCComplexActionCLM phase zeroZeroCoordinate) =
        d9PrimitiveSpinCComplexActionCLM phase
          (d9PrimitiveSpinCImaginaryAction zeroZeroCoordinate) := by
    rw [← d9PrimitiveSpinCComplexAction_imaginary]
  calc
    _ =
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector circleMode).localValue
          timeIndex timeBase := by
      unfold primitiveSpinCHopfFirstSphereTangentialSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod timeIndex timeBase hTimeMem]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector circleMode)
        timeIndex timeBase hTimeMem
    _ =
        d9DoubledMatterFiberCliffordGammaCLM coordinate timeZeroCoordinate -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod coordinate timeBase •
            d9PrimitiveSpinCImaginaryAction timeZeroCoordinate := by
      rw [primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily_localValue]
      rw [← primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
        period hPeriod sector circleMode timeIndex timeBase hTimeMem]
    _ =
        d9PrimitiveSpinCComplexActionCLM phase
            (d9DoubledMatterFiberCliffordGammaCLM
              coordinate zeroZeroCoordinate) -
          d9PrimitiveSpinCBaseUnitRadialCoordinate
              period hPeriod coordinate zeroBase •
            d9PrimitiveSpinCComplexActionCLM phase
              (d9PrimitiveSpinCImaginaryAction zeroZeroCoordinate) := by
      rw [hZeroFactor, hGamma, hImaginary, hRadial]
    _ =
        d9PrimitiveSpinCComplexActionCLM phase
          (d9DoubledMatterFiberCliffordGammaCLM
              coordinate zeroZeroCoordinate -
            d9PrimitiveSpinCBaseUnitRadialCoordinate
                period hPeriod coordinate zeroBase •
              d9PrimitiveSpinCImaginaryAction zeroZeroCoordinate) := by
      rw [map_sub, map_smul]
    _ =
        d9PrimitiveSpinCComplexActionCLM phase
          ((primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
            period hPeriod coordinate sector circleMode).localValue
            zeroIndex zeroBase) := by
      congr 1
      rw [primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily_localValue]
      rw [← primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
        period hPeriod sector circleMode zeroIndex zeroBase hZeroMem]
    _ = _ := by
      congr 1
      unfold primitiveSpinCHopfFirstSphereTangentialSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod zeroIndex zeroBase hZeroMem]
      exact
        (primitiveSpinCBundleSection_localTriv
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
            period hPeriod coordinate sector circleMode)
          zeroIndex zeroBase hZeroMem).symm

/-- Local tangential evaluation is the pointwise projected Clifford
generator applied to the local Hopf seed. -/
theorem primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_eq
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (circleMode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode) =
      d9DoubledMatterFiberCliffordGammaCLM coordinate
          (primitiveSpinCGeometricSectionLocalCoordinate
            period hPeriod
            (primitiveSpinCNullPacketMovingWitnessIndexAt
              period hPeriod point time chart)
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode)) -
        d9PrimitiveSpinCBaseUnitRadialCoordinate
            period hPeriod coordinate
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time) •
          d9PrimitiveSpinCImaginaryAction
            (primitiveSpinCGeometricSectionLocalCoordinate
              period hPeriod
              (primitiveSpinCNullPacketMovingWitnessIndexAt
                period hPeriod point time chart)
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point time)
              (primitiveSpinCHopfZeroModeSection
                period hPeriod sector circleMode)) := by
  let index :=
    primitiveSpinCNullPacketMovingWitnessIndexAt
      period hPeriod point time chart
  let base :=
    primitiveSpinCNullPacketMovingWitnessBase
      period hPeriod point time
  have hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    primitiveSpinCNullPacketMovingWitnessBase_mem_at
      period hPeriod point chart hChart time
  calc
    _ =
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector circleMode).localValue
          index base := by
      unfold primitiveSpinCHopfFirstSphereTangentialSection
      rw [primitiveSpinCGeometricSectionLocalCoordinate_apply_of_mem
        period hPeriod index base hBase]
      exact primitiveSpinCBundleSection_localTriv
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily
          period hPeriod coordinate sector circleMode)
        index base hBase
    _ = _ := by
      rw [primitiveSpinCHopfFirstSphereTangentialLocalGaugeFamily_localValue]
      rw [← primitiveSpinCGeometricSectionLocalCoordinate_hopfZeroMode
        period hPeriod sector circleMode index base hBase]

/-- Fiberwise sector plane used by both the scalar and tangential packets. -/
def PrimitiveSpinCGeometricSectorPlane
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) : Prop :=
  match sector with
  | .positiveQuarter =>
      ∃ first second : Complex,
        d9DoubledMatterFiberHalfSpinorLinearEquiv matter =
          (first • ambientHalfGammaPositiveEigenvector,
            second • ambientHalfGammaTransverseVector)
  | .negativeQuarter =>
      ∃ first second : Complex,
        d9DoubledMatterFiberHalfSpinorLinearEquiv matter =
          (first • ambientHalfGammaTransverseVector,
            second • ambientHalfGammaPositiveEigenvector)

theorem primitiveSpinCGeometricSectorPlane_zero
    (sector : NormalRootChoice) :
    PrimitiveSpinCGeometricSectorPlane sector 0 := by
  cases sector <;>
    refine ⟨0, 0, ?_⟩ <;>
    simp

theorem primitiveSpinCGeometricSectorPlane_add
    (sector : NormalRootChoice) (first second : D9DoubledMatterFiber)
    (hFirst : PrimitiveSpinCGeometricSectorPlane sector first)
    (hSecond : PrimitiveSpinCGeometricSectorPlane sector second) :
    PrimitiveSpinCGeometricSectorPlane sector (first + second) := by
  cases sector with
  | positiveQuarter =>
      rcases hFirst with ⟨firstOne, firstTwo, hFirst⟩
      rcases hSecond with ⟨secondOne, secondTwo, hSecond⟩
      refine ⟨firstOne + secondOne, firstTwo + secondTwo, ?_⟩
      rw [map_add, hFirst, hSecond]
      simp [add_smul]
  | negativeQuarter =>
      rcases hFirst with ⟨firstOne, firstTwo, hFirst⟩
      rcases hSecond with ⟨secondOne, secondTwo, hSecond⟩
      refine ⟨firstOne + secondOne, firstTwo + secondTwo, ?_⟩
      rw [map_add, hFirst, hSecond]
      simp [add_smul]

theorem primitiveSpinCGeometricSectorPlane_complexAction
    (sector : NormalRootChoice) (scalar : Complex)
    (matter : D9DoubledMatterFiber)
    (hMatter : PrimitiveSpinCGeometricSectorPlane sector matter) :
    PrimitiveSpinCGeometricSectorPlane sector
      (d9PrimitiveSpinCComplexActionCLM scalar matter) := by
  cases sector with
  | positiveQuarter =>
      rcases hMatter with ⟨first, second, hMatter⟩
      refine ⟨scalar * first, scalar * second, ?_⟩
      rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction, hMatter]
      simp [smul_smul]
  | negativeQuarter =>
      rcases hMatter with ⟨first, second, hMatter⟩
      refine ⟨scalar * first, scalar * second, ?_⟩
      rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction, hMatter]
      simp [smul_smul]

theorem primitiveSpinCGeometricSectorPlane_real_smul
    (sector : NormalRootChoice) (scalar : Real)
    (matter : D9DoubledMatterFiber)
    (hMatter : PrimitiveSpinCGeometricSectorPlane sector matter) :
    PrimitiveSpinCGeometricSectorPlane sector (scalar • matter) := by
  have hAction :
      scalar • matter =
        d9PrimitiveSpinCComplexActionCLM (scalar : Complex) matter := by
    rw [d9PrimitiveSpinCComplexActionCLM_eq_re_add_im]
    simp
  rw [hAction]
  exact primitiveSpinCGeometricSectorPlane_complexAction
    sector (scalar : Complex) matter hMatter

/-- Projected Clifford multiplication preserves each of the two explicit
sector planes. -/
theorem primitiveSpinCGeometricSectorPlane_tangential
    (sector : NormalRootChoice) (coordinate : Fin 3) (radial : Real)
    (matter : D9DoubledMatterFiber)
    (hMatter : PrimitiveSpinCGeometricSectorPlane sector matter) :
    PrimitiveSpinCGeometricSectorPlane sector
      (d9DoubledMatterFiberCliffordGammaCLM coordinate matter -
        radial • d9PrimitiveSpinCImaginaryAction matter) := by
  cases sector with
  | positiveQuarter =>
      rcases hMatter with ⟨first, second, hMatter⟩
      refine
        ⟨![
            Complex.I * first -
              (radial : Complex) * Complex.I * first,
            -Complex.I * second -
              (radial : Complex) * Complex.I * first,
            second - (radial : Complex) * Complex.I * first] coordinate,
          ![
            -Complex.I * second -
              (radial : Complex) * Complex.I * second,
            -Complex.I * first -
              (radial : Complex) * Complex.I * second,
            -first -
              (radial : Complex) * Complex.I * second] coordinate,
          ?_⟩
      fin_cases coordinate
      all_goals
        rw [map_sub, map_smul,
          d9DoubledMatterFiberCliffordGammaCLM_apply,
          d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
          d9DoubledMatterFiberHalfSpinorLinearEquiv_imaginaryAction,
          hMatter]
        apply Prod.ext <;> funext index <;> fin_cases index <;>
          simp [d9DoubledMatterSpinorCliffordGamma_zero,
            d9DoubledMatterSpinorCliffordGamma_one,
            d9DoubledMatterSpinorCliffordGamma_two,
            ambientHalfGammaPositiveEigenvector,
            ambientHalfGammaTransverseVector] <;>
          ring_nf <;>
          rw [Complex.I_sq] <;>
          ring
  | negativeQuarter =>
      rcases hMatter with ⟨first, second, hMatter⟩
      refine
        ⟨![
            -Complex.I * first -
              (radial : Complex) * Complex.I * first,
            Complex.I * second -
              (radial : Complex) * Complex.I * first,
            second - (radial : Complex) * Complex.I * first] coordinate,
          ![
            Complex.I * second -
              (radial : Complex) * Complex.I * second,
            Complex.I * first -
              (radial : Complex) * Complex.I * second,
            -first -
              (radial : Complex) * Complex.I * second] coordinate,
          ?_⟩
      fin_cases coordinate
      all_goals
        rw [map_sub, map_smul,
          d9DoubledMatterFiberCliffordGammaCLM_apply,
          d9DoubledMatterFiberHalfSpinorLinearEquiv_gamma,
          d9DoubledMatterFiberHalfSpinorLinearEquiv_imaginaryAction,
          hMatter]
        apply Prod.ext <;> funext index <;> fin_cases index <;>
          simp [d9DoubledMatterSpinorCliffordGamma_zero,
            d9DoubledMatterSpinorCliffordGamma_one,
            d9DoubledMatterSpinorCliffordGamma_two,
            ambientHalfGammaPositiveEigenvector,
            ambientHalfGammaTransverseVector] <;>
          ring_nf <;>
          rw [Complex.I_sq] <;>
          ring

/-- Every installed Hopf zero mode lies in its explicit sector plane in
every common monopole chart. -/
theorem primitiveSpinCHopfZeroModeLocalCoordinate_sectorPlane
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    PrimitiveSpinCGeometricSectorPlane sector
      (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode)) := by
  cases sector with
  | positiveQuarter =>
      exact
        ⟨(primitiveMonopoleZeroLocalValue chart point +
              primitiveMonopoleZeroComplementLocalValue chart point) *
            normalRootSpinFramePhase period hPeriod .positiveQuarter
              circleMode
              (primitiveSpinCNullPacketMovingWitnessCover
                period hPeriod point time),
          Complex.I *
            (primitiveMonopoleZeroLocalValue chart point -
              primitiveMonopoleZeroComplementLocalValue chart point) *
            normalRootSpinFramePhase period hPeriod .positiveQuarter
              circleMode
              (primitiveSpinCNullPacketMovingWitnessCover
                period hPeriod point time),
          primitiveSpinCHopfZeroModeLocalCoordinate_positive_halfSpinor
            period hPeriod point chart hChart circleMode time⟩
  | negativeQuarter =>
      exact
        ⟨Complex.I *
            (primitiveMonopoleZeroComplementLocalValue chart point -
              primitiveMonopoleZeroLocalValue chart point) *
            normalRootSpinFramePhase period hPeriod .negativeQuarter
              circleMode
              (primitiveSpinCNullPacketMovingWitnessCover
                period hPeriod point time),
          (primitiveMonopoleZeroLocalValue chart point +
              primitiveMonopoleZeroComplementLocalValue chart point) *
            normalRootSpinFramePhase period hPeriod .negativeQuarter
              circleMode
              (primitiveSpinCNullPacketMovingWitnessCover
                period hPeriod point time),
          primitiveSpinCHopfZeroModeLocalCoordinate_negative_halfSpinor
            period hPeriod point chart hChart circleMode time⟩

/-- Every tangential Hopf partner remains in the same normal-root sector
plane as its scalar seed. -/
theorem primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_sectorPlane
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (coordinate : Fin 3) (sector : NormalRootChoice)
    (circleMode : Int) (time : Real) :
    PrimitiveSpinCGeometricSectorPlane sector
      (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCHopfFirstSphereTangentialSection
          period hPeriod coordinate sector circleMode)) := by
  rw [primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_eq
    period hPeriod point chart hChart]
  exact primitiveSpinCGeometricSectorPlane_tangential sector coordinate
    (d9PrimitiveSpinCBaseUnitRadialCoordinate
      period hPeriod coordinate
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time))
    _ (primitiveSpinCHopfZeroModeLocalCoordinate_sectorPlane
      period hPeriod point chart hChart sector circleMode time)

/-- The local null gradient of a Hopf seed remains in its normal-root
sector plane. -/
theorem primitiveSpinCNullGradientZeroModeLocalCoordinate_sectorPlane
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (parameter : Complex) (sector : NormalRootChoice)
    (circleMode : Int) (time : Real) :
    PrimitiveSpinCGeometricSectorPlane sector
      (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullGradientLinearMap
          period hPeriod parameter
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode))) := by
  rw [primitiveSpinCNullGradientLinearMap_apply, map_sum]
  apply Finset.sum_induction
  · intro first second hFirst hSecond
    exact primitiveSpinCGeometricSectorPlane_add
      sector first second hFirst hSecond
  · exact primitiveSpinCGeometricSectorPlane_zero sector
  · intro coordinate _
    rw [primitiveSpinCCoordinateGradient_zeroMode,
      primitiveSpinCGeometricSectionLocalCoordinate_complexScalar_eq_action
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullPacketMovingWitnessBase_mem_at
          period hPeriod point chart hChart time)]
    exact primitiveSpinCGeometricSectorPlane_complexAction sector
      (primitiveSpinCSolidNullVector parameter coordinate) _
      (primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_sectorPlane
        period hPeriod point chart hChart coordinate sector circleMode time)

/-- Null multiplication preserves the sector plane, so every auxiliary
gradient power remains in that plane. -/
theorem primitiveSpinCNullGradientPowerLocalCoordinate_sectorPlane
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (parameter : Complex) (sector : NormalRootChoice)
    (circleMode : Int) (degree : Nat) (time : Real) :
    PrimitiveSpinCGeometricSectorPlane sector
      (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullGradientPowerSection
          period hPeriod parameter sector circleMode degree)) := by
  induction degree with
  | zero =>
      rw [primitiveSpinCNullGradientPowerSection_zero]
      exact primitiveSpinCNullGradientZeroModeLocalCoordinate_sectorPlane
        period hPeriod point chart hChart parameter sector circleMode time
  | succ degree inductionHypothesis =>
      rw [primitiveSpinCNullGradientPowerSection_succ,
        primitiveSpinCNullMultiplicationLocalCoordinate_moving_at
          period hPeriod point chart hChart time]
      exact primitiveSpinCGeometricSectorPlane_complexAction sector
        (primitiveSpinCNullSphereScalar parameter point) _
        inductionHypothesis

/-- Every reconstructed all-level gradient lies in its explicit
normal-root sector plane. -/
theorem primitiveSpinCAllLevelNullHarmonicGradientLocalCoordinate_sectorPlane
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    PrimitiveSpinCGeometricSectorPlane sector
      (primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel multiplicity sector circleMode
          |>.gradientSection)) := by
  rw [show
      ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode
        |>.gradientSection) =
        (primitiveSpinCAllLevelNullHarmonicSquaredSeed
          period hPeriod positiveLevel multiplicity sector circleMode
          |>.gradientSection) by rfl,
    primitiveSpinCAllLevelNullHarmonicSquaredSeed_gradientSection,
    map_smul]
  exact primitiveSpinCGeometricSectorPlane_real_smul sector
    ((positiveLevel + 1 : Nat) : Real) _
    (primitiveSpinCNullGradientPowerLocalCoordinate_sectorPlane
      period hPeriod point chart hChart
      (primitiveSpinCNullGeometricParameter positiveLevel multiplicity)
      sector circleMode positiveLevel time)

/-- The two explicit sector-plane predicates are Hermitian orthogonal. -/
theorem d9DoubledMatterSpinorHermitianPairing_geometricSectorPlanes_eq_zero
    (positive negative : D9DoubledMatterFiber)
    (hPositive :
      PrimitiveSpinCGeometricSectorPlane .positiveQuarter positive)
    (hNegative :
      PrimitiveSpinCGeometricSectorPlane .negativeQuarter negative) :
    d9DoubledMatterSpinorHermitianPairing positive negative = 0 := by
  rcases hPositive with
    ⟨positiveFirst, positiveSecond, hPositive⟩
  rcases hNegative with
    ⟨negativeFirst, negativeSecond, hNegative⟩
  exact d9DoubledMatterSpinorHermitianPairing_sectorPlanes_eq_zero
    positive negative positiveFirst positiveSecond negativeFirst
    negativeSecond hPositive hNegative

/-- Positive- and negative-sector all-level gradients are pointwise
orthogonal in every common monopole chart. -/
theorem primitiveSpinCAllLevelNullHarmonicGradientLocalCoordinate_sectors_orthogonal
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (positiveCircleMode negativeCircleMode : Int) (time : Real) :
    d9DoubledMatterSpinorHermitianPairing
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              firstPositiveLevel firstMultiplicity .positiveQuarter
                positiveCircleMode
            |>.gradientSection))
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point time chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              secondPositiveLevel secondMultiplicity .negativeQuarter
                negativeCircleMode
            |>.gradientSection)) = 0 := by
  apply
    d9DoubledMatterSpinorHermitianPairing_geometricSectorPlanes_eq_zero
  · exact
      primitiveSpinCAllLevelNullHarmonicGradientLocalCoordinate_sectorPlane
        period hPeriod point chart hChart firstPositiveLevel
        firstMultiplicity .positiveQuarter positiveCircleMode time
  · exact
      primitiveSpinCAllLevelNullHarmonicGradientLocalCoordinate_sectorPlane
        period hPeriod point chart hChart secondPositiveLevel
        secondMultiplicity .negativeQuarter negativeCircleMode time

/-- Opposite normal-root sectors give intrinsically pointwise orthogonal
all-level gradients. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_pointwise_sectors_orthogonal
    (point : MonopoleSphere)
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (positiveCircleMode negativeCircleMode : Int) (time : Real) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity .positiveQuarter
              positiveCircleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity .negativeQuarter
              negativeCircleMode
          |>.gradientSection)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) = 0 := by
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
    primitiveSpinCAllLevelNullHarmonicGradientLocalCoordinate_sectors_orthogonal
      period hPeriod point chart hChart
      firstPositiveLevel secondPositiveLevel
      firstMultiplicity secondMultiplicity
      positiveCircleMode negativeCircleMode time

/-- Opposite normal-root sectors give globally orthogonal all-level
gradients in the independently integrated geometric product. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_sectors_orthogonal
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (positiveCircleMode negativeCircleMode : Int) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity .positiveQuarter
              positiveCircleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity .negativeQuarter
              negativeCircleMode
          |>.gradientSection) = 0 := by
  rw [d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun base => by
    change
      d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              firstPositiveLevel firstMultiplicity .positiveQuarter
                positiveCircleMode
            |>.gradientSection)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              secondPositiveLevel secondMultiplicity .negativeQuarter
                negativeCircleMode
            |>.gradientSection)
          (canonicalLatitudeThroatMap period hPeriod base) = 0
    rw [canonicalLatitudeThroatMap_eq_nullPacketMovingWitnessBase]
    exact
      primitiveSpinCAllLevelNullHarmonicGradient_pointwise_sectors_orthogonal
        period hPeriod base.1 firstPositiveLevel secondPositiveLevel
        firstMultiplicity secondMultiplicity positiveCircleMode
        negativeCircleMode base.2

/-- The null gradient of a Hopf seed has the same normal Fourier factor as
the seed and all three tangential partners. -/
theorem primitiveSpinCNullGradientZeroModeLocalCoordinate_moving_factor_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (parameter : Complex) (sector : NormalRootChoice)
    (circleMode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullGradientLinearMap
          period hPeriod parameter
          (primitiveSpinCHopfZeroModeSection
            period hPeriod sector circleMode)) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector circleMode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCNullGradientLinearMap
            period hPeriod parameter
            (primitiveSpinCHopfZeroModeSection
              period hPeriod sector circleMode))) := by
  rw [primitiveSpinCNullGradientLinearMap_apply, map_sum, map_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [primitiveSpinCCoordinateGradient_zeroMode,
    primitiveSpinCGeometricSectionLocalCoordinate_complexScalar_eq_action
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point time chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart time),
    primitiveSpinCGeometricSectionLocalCoordinate_complexScalar_eq_action
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point 0 chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point 0)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart 0)]
  rw [
    primitiveSpinCHopfFirstSphereTangentialLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart]
  rw [← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul]
  congr 1
  ring

/-- Every auxiliary gradient power carries one common normal Fourier
factor in either monopole chart. -/
theorem primitiveSpinCNullGradientPowerLocalCoordinate_moving_factor_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (parameter : Complex) (sector : NormalRootChoice)
    (circleMode : Int) (degree : Nat) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        (primitiveSpinCNullGradientPowerSection
          period hPeriod parameter sector circleMode degree) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector circleMode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          (primitiveSpinCNullGradientPowerSection
            period hPeriod parameter sector circleMode degree)) := by
  induction degree with
  | zero =>
      simpa only [primitiveSpinCNullGradientPowerSection_zero] using
        primitiveSpinCNullGradientZeroModeLocalCoordinate_moving_factor_at
          period hPeriod point chart hChart parameter sector circleMode time
  | succ degree inductionHypothesis =>
      rw [primitiveSpinCNullGradientPowerSection_succ,
        primitiveSpinCNullMultiplicationLocalCoordinate_moving_at
          period hPeriod point chart hChart time,
        primitiveSpinCNullMultiplicationLocalCoordinate_moving_at
          period hPeriod point chart hChart 0,
        inductionHypothesis,
        ← d9PrimitiveSpinCComplexAction_mul,
        ← d9PrimitiveSpinCComplexAction_mul,
        mul_comm]

/-- The reconstructed all-level gradient packet has one exact normal
Fourier factor in either monopole chart. -/
theorem primitiveSpinCAllLevelNullHarmonicGradientLocalCoordinate_moving_factor_at
    (point : MonopoleSphere) (chart : MonopoleChart)
    (hChart : point ∈ monopoleChartDomain chart)
    (positiveLevel : Nat)
    (multiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    primitiveSpinCGeometricSectionLocalCoordinate
        period hPeriod
        (primitiveSpinCNullPacketMovingWitnessIndexAt
          period hPeriod point time chart)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel multiplicity sector circleMode
          |>.gradientSection) =
      d9PrimitiveSpinCComplexActionCLM
        (normalRootSpinFrameExponential period sector circleMode time)
        (primitiveSpinCGeometricSectionLocalCoordinate
          period hPeriod
          (primitiveSpinCNullPacketMovingWitnessIndexAt
            period hPeriod point 0 chart)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point 0)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel multiplicity sector circleMode
            |>.gradientSection)) := by
  rw [show
      ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
        period hPeriod).seed
          positiveLevel multiplicity sector circleMode
        |>.gradientSection) =
        (primitiveSpinCAllLevelNullHarmonicSquaredSeed
          period hPeriod positiveLevel multiplicity sector circleMode
          |>.gradientSection) by rfl,
    primitiveSpinCAllLevelNullHarmonicSquaredSeed_gradientSection,
    map_smul,
    map_smul,
    primitiveSpinCNullGradientPowerLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart,
    map_smul]

/-- The intrinsic pairing of two gradient packets in one sector separates
into the exact Fourier character and its time-zero sphere factor. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_pointwise_moving_factor_all
    (point : MonopoleSphere)
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (sector : NormalRootChoice)
    (firstCircleMode secondCircleMode : Int) (time : Real) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity sector firstCircleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity sector secondCircleMode
          |>.gradientSection)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      ((starRingEnd Complex)
          (normalRootSpinFrameExponential
            period sector firstCircleMode time) *
        normalRootSpinFrameExponential
          period sector secondCircleMode time) *
      d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity sector firstCircleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity sector secondCircleMode
          |>.gradientSection)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point 0) := by
  obtain ⟨chart, hChart⟩ := monopoleChartDomain_cover point
  rw [
    d9PrimitiveSpinCPointwiseHermitianPairing_eq_localCoordinate
      period hPeriod
      (primitiveSpinCNullPacketMovingWitnessIndexAt
        period hPeriod point time chart)
      (primitiveSpinCNullPacketMovingWitnessBase
        period hPeriod point time)
      (primitiveSpinCNullPacketMovingWitnessBase_mem_at
        period hPeriod point chart hChart time),
    primitiveSpinCAllLevelNullHarmonicGradientLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart firstPositiveLevel
        firstMultiplicity sector firstCircleMode time,
    primitiveSpinCAllLevelNullHarmonicGradientLocalCoordinate_moving_factor_at
      period hPeriod point chart hChart secondPositiveLevel
        secondMultiplicity sector secondCircleMode time,
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

/-- Gradient packets with distinct circle modes in one normal-root sector
are orthogonal for the independently integrated geometric product. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_circleMode_orthogonal
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (sector : NormalRootChoice)
    (firstCircleMode secondCircleMode : Int)
    (hModes : firstCircleMode ≠ secondCircleMode) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity sector firstCircleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity sector secondCircleMode
          |>.gradientSection) = 0 := by
  let firstGradient : SmoothSection period hPeriod :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        firstPositiveLevel firstMultiplicity sector firstCircleMode
      |>.gradientSection)
  let secondGradient : SmoothSection period hPeriod :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        secondPositiveLevel secondMultiplicity sector secondCircleMode
      |>.gradientSection)
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter firstGradient secondGradient = 0
  rw [d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral]
  have hIntrinsic :=
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod .positiveQuarter firstGradient secondGradient
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
    at hIntrinsic
  have hPullback :
      Integrable
        (fun base : CanonicalLatitudeBase =>
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter firstGradient secondGradient
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
          period hPeriod .positiveQuarter firstGradient secondGradient
          (canonicalLatitudeThroatMap period hPeriod (point, time))
        ∂(volume.restrict (canonicalLatitudeTimeInterval period))) = 0
    rw [show
        (fun time : Real =>
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter firstGradient secondGradient
            (canonicalLatitudeThroatMap period hPeriod (point, time))) =
          fun time : Real =>
            ((starRingEnd Complex)
                (normalRootSpinFrameExponential
                  period sector firstCircleMode time) *
              normalRootSpinFrameExponential
                period sector secondCircleMode time) *
            d9PrimitiveSpinCPointwiseHermitianPairing
              period hPeriod .positiveQuarter firstGradient secondGradient
              (primitiveSpinCNullPacketMovingWitnessBase
                period hPeriod point 0) by
      funext time
      rw [canonicalLatitudeThroatMap_eq_nullPacketMovingWitnessBase]
      dsimp only [firstGradient, secondGradient]
      exact
        primitiveSpinCAllLevelNullHarmonicGradient_pointwise_moving_factor_all
          period hPeriod point firstPositiveLevel secondPositiveLevel
          firstMultiplicity secondMultiplicity sector firstCircleMode
          secondCircleMode time]
    rw [integral_mul_const,
      normalRootSpinFrameExponential_fundamentalDomain_orthogonal
        period hPeriod sector firstCircleMode secondCircleMode hModes]
    simp

/-! ## Cross-level gradient/Casimir identities -/

/-- Integration by parts between an ambient derivative of one degree and an
angular derivative of an arbitrary second degree. -/
theorem primitiveSpinCNullSpherePowerAmbientDerivative_angular_ipp_cross
    (coordinate : Fin 3) (firstDegree secondDegree : Nat)
    (firstParameter secondParameter : Complex) :
    (∫ point,
        star
            (primitiveSpinCNullSpherePowerAmbientDerivative
              firstDegree firstParameter coordinate point) *
          primitiveSpinCNullSpherePowerAngularDerivative
            coordinate secondDegree secondParameter point
        ∂SphereMeasure) =
      -∫ point,
        star
            (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
              firstDegree firstParameter coordinate point) *
          primitiveSpinCNullSpherePower
            secondDegree secondParameter point
        ∂SphereMeasure := by
  let coefficient : Complex :=
    (firstDegree : Complex) *
      primitiveSpinCSolidNullVector firstParameter coordinate
  have hIPP :
      (∫ point,
          star
              (primitiveSpinCNullSpherePower
                (firstDegree - 1) firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              coordinate secondDegree secondParameter point
          ∂SphereMeasure) =
        -∫ point,
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                coordinate (firstDegree - 1) firstParameter point) *
            primitiveSpinCNullSpherePower
              secondDegree secondParameter point
          ∂SphereMeasure := by
    simpa only [] using
      primitiveSpinCNullSpherePower_angular_ipp
        coordinate (firstDegree - 1) secondDegree
        firstParameter secondParameter
  change
    (∫ point,
        star
            (coefficient *
              primitiveSpinCNullSpherePower
                (firstDegree - 1) firstParameter point) *
          primitiveSpinCNullSpherePowerAngularDerivative
            coordinate secondDegree secondParameter point
        ∂SphereMeasure) =
      -∫ point,
        star
            (coefficient *
              primitiveSpinCNullSpherePowerAngularDerivative
                coordinate (firstDegree - 1) firstParameter point) *
          primitiveSpinCNullSpherePower
            secondDegree secondParameter point
        ∂SphereMeasure
  have hLeftFactor :
      (∫ point,
          star
              (coefficient *
                primitiveSpinCNullSpherePower
                  (firstDegree - 1) firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              coordinate secondDegree secondParameter point
          ∂SphereMeasure) =
        star coefficient *
          ∫ point,
            star
                (primitiveSpinCNullSpherePower
                  (firstDegree - 1) firstParameter point) *
              primitiveSpinCNullSpherePowerAngularDerivative
                coordinate secondDegree secondParameter point
            ∂SphereMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with point
    simp only [Complex.star_def, map_mul]
    ring
  have hRightFactor :
      (∫ point,
          star
              (coefficient *
                primitiveSpinCNullSpherePowerAngularDerivative
                  coordinate (firstDegree - 1) firstParameter point) *
            primitiveSpinCNullSpherePower
              secondDegree secondParameter point
          ∂SphereMeasure) =
        star coefficient *
          ∫ point,
            star
                (primitiveSpinCNullSpherePowerAngularDerivative
                  coordinate (firstDegree - 1) firstParameter point) *
              primitiveSpinCNullSpherePower
                secondDegree secondParameter point
            ∂SphereMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with point
    simp only [Complex.star_def, map_mul]
    ring
  rw [hLeftFactor, hRightFactor, hIPP]
  ring

/-- The mixed ambient/angular contribution vanishes for arbitrary degrees. -/
theorem primitiveSpinCNullSpherePowerAmbientDerivative_angular_sum_zero_cross
    (firstDegree secondDegree : Nat)
    (firstParameter secondParameter : Complex) :
    (∫ point,
        ∑ coordinate : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAmbientDerivative
                firstDegree firstParameter coordinate point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              coordinate secondDegree secondParameter point
        ∂SphereMeasure) = 0 := by
  have hLeftIntegrable (coordinate : Fin 3) :
      Integrable
        (fun point =>
          star
              (primitiveSpinCNullSpherePowerAmbientDerivative
                firstDegree firstParameter coordinate point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              coordinate secondDegree secondParameter point)
        SphereMeasure :=
    ((primitiveSpinCNullSpherePowerAmbientDerivative_continuous
      firstDegree firstParameter coordinate).star.mul
        (primitiveSpinCNullSpherePowerAngularDerivative_continuous
          coordinate secondDegree secondParameter))
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hRightIntegrable (coordinate : Fin 3) :
      Integrable
        (fun point =>
          star
              (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
                firstDegree firstParameter coordinate point) *
            primitiveSpinCNullSpherePower
              secondDegree secondParameter point)
        SphereMeasure :=
    ((primitiveSpinCNullSpherePowerAmbientDivergenceDerivative_continuous
      firstDegree firstParameter coordinate).star.mul
        (primitiveSpinCNullSpherePower_continuous
          secondDegree secondParameter))
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hRightPointwise :
      (fun point =>
        ∑ coordinate : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
                firstDegree firstParameter coordinate point) *
            primitiveSpinCNullSpherePower
              secondDegree secondParameter point) = 0 := by
    funext point
    change
      (∑ coordinate : Fin 3,
        (starRingEnd Complex)
            (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
              firstDegree firstParameter coordinate point) *
          primitiveSpinCNullSpherePower
            secondDegree secondParameter point) = (0 : Complex)
    rw [← Finset.sum_mul, ← map_sum,
      primitiveSpinCNullSpherePowerAmbientDivergenceDerivative_sum]
    simp
  calc
    (∫ point,
        ∑ coordinate : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAmbientDerivative
                firstDegree firstParameter coordinate point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              coordinate secondDegree secondParameter point
        ∂SphereMeasure) =
        ∑ coordinate : Fin 3,
          ∫ point,
            star
                (primitiveSpinCNullSpherePowerAmbientDerivative
                  firstDegree firstParameter coordinate point) *
              primitiveSpinCNullSpherePowerAngularDerivative
                coordinate secondDegree secondParameter point
            ∂SphereMeasure := by
      rw [integral_finsetSum]
      intro coordinate _
      exact hLeftIntegrable coordinate
    _ = ∑ coordinate : Fin 3,
        -∫ point,
          star
              (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
                firstDegree firstParameter coordinate point) *
            primitiveSpinCNullSpherePower
              secondDegree secondParameter point
          ∂SphereMeasure := by
      apply Finset.sum_congr rfl
      intro coordinate _
      exact primitiveSpinCNullSpherePowerAmbientDerivative_angular_ipp_cross
        coordinate firstDegree secondDegree firstParameter secondParameter
    _ = -(∫ point,
        ∑ coordinate : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAmbientDivergenceDerivative
                firstDegree firstParameter coordinate point) *
            primitiveSpinCNullSpherePower
              secondDegree secondParameter point
        ∂SphereMeasure) := by
      rw [integral_finsetSum]
      · simp
      · intro coordinate _
        exact hRightIntegrable coordinate
    _ = 0 := by
      rw [hRightPointwise]
      simp

/-- The cross-degree Dirichlet pairing transfers the Casimir eigenvalue of
the second null power. -/
theorem primitiveSpinCNullSpherePower_angular_energy_eq_casimir_cross
    (firstDegree secondDegree : Nat)
    (firstParameter secondParameter : Complex) :
    (∫ point,
        ∑ axis : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                axis firstDegree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              axis secondDegree secondParameter point
        ∂SphereMeasure) =
      ((secondDegree : Complex) * (secondDegree + 1 : Nat)) *
        ∫ point,
          star
              (primitiveSpinCNullSpherePower
                firstDegree firstParameter point) *
            primitiveSpinCNullSpherePower
              secondDegree secondParameter point
          ∂SphereMeasure := by
  have hEnergyIntegrable (axis : Fin 3) :
      Integrable
        (fun point =>
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                axis firstDegree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              axis secondDegree secondParameter point)
        SphereMeasure :=
    ((primitiveSpinCNullSpherePowerAngularDerivative_continuous
      axis firstDegree firstParameter).star.mul
        (primitiveSpinCNullSpherePowerAngularDerivative_continuous
          axis secondDegree secondParameter))
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hSecondIntegrable (axis : Fin 3) :
      Integrable
        (fun point =>
          star
              (primitiveSpinCNullSpherePower
                firstDegree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularSecondDerivative
              axis secondDegree secondParameter point)
        SphereMeasure :=
    ((primitiveSpinCNullSpherePower_continuous
      firstDegree firstParameter).star.mul
        (primitiveSpinCNullSpherePowerAngularSecondDerivative_continuous
          axis secondDegree secondParameter))
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hAxis (axis : Fin 3) :
      (∫ point,
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                axis firstDegree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              axis secondDegree secondParameter point
          ∂SphereMeasure) =
        -∫ point,
          star
              (primitiveSpinCNullSpherePower
                firstDegree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularSecondDerivative
              axis secondDegree secondParameter point
          ∂SphereMeasure := by
    have hIPP := sphere_integral_star_mul_derivative_eq_neg axis
      (primitiveSpinCNullSpherePower firstDegree firstParameter)
      (primitiveSpinCNullSpherePowerAngularDerivative
        axis secondDegree secondParameter)
      (primitiveSpinCNullSpherePowerAngularDerivative
        axis firstDegree firstParameter)
      (primitiveSpinCNullSpherePowerAngularSecondDerivative
        axis secondDegree secondParameter)
      (primitiveSpinCNullSpherePower_continuous
        firstDegree firstParameter)
      (primitiveSpinCNullSpherePowerAngularDerivative_continuous
        axis secondDegree secondParameter)
      (primitiveSpinCNullSpherePowerAngularDerivative_continuous
        axis firstDegree firstParameter)
      (primitiveSpinCNullSpherePowerAngularSecondDerivative_continuous
        axis secondDegree secondParameter)
      (fun angle point =>
        primitiveSpinCNullSpherePower_rotation_hasDerivAt
          axis firstDegree firstParameter point angle)
      (fun angle point =>
        primitiveSpinCNullSpherePowerAngularDerivative_rotation_hasDerivAt
          axis secondDegree secondParameter point angle)
    linear_combination hIPP
  calc
    (∫ point,
        ∑ axis : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                axis firstDegree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              axis secondDegree secondParameter point
        ∂SphereMeasure) =
        ∑ axis : Fin 3,
          ∫ point,
            star
                (primitiveSpinCNullSpherePowerAngularDerivative
                  axis firstDegree firstParameter point) *
              primitiveSpinCNullSpherePowerAngularDerivative
                axis secondDegree secondParameter point
            ∂SphereMeasure := by
      rw [integral_finsetSum]
      intro axis _
      exact hEnergyIntegrable axis
    _ = ∑ axis : Fin 3,
        -∫ point,
          star
              (primitiveSpinCNullSpherePower
                firstDegree firstParameter point) *
            primitiveSpinCNullSpherePowerAngularSecondDerivative
              axis secondDegree secondParameter point
          ∂SphereMeasure := by
      apply Finset.sum_congr rfl
      intro axis _
      exact hAxis axis
    _ = ∫ point,
        star
            (primitiveSpinCNullSpherePower
              firstDegree firstParameter point) *
          primitiveSpinCNullSpherePowerRotationCasimir
            secondDegree secondParameter point
        ∂SphereMeasure := by
      rw [show
          (∑ axis : Fin 3,
              -∫ point,
                star
                    (primitiveSpinCNullSpherePower
                      firstDegree firstParameter point) *
                  primitiveSpinCNullSpherePowerAngularSecondDerivative
                    axis secondDegree secondParameter point
                ∂SphereMeasure) =
            -∫ point,
              ∑ axis : Fin 3,
                star
                    (primitiveSpinCNullSpherePower
                      firstDegree firstParameter point) *
                  primitiveSpinCNullSpherePowerAngularSecondDerivative
                    axis secondDegree secondParameter point
              ∂SphereMeasure by
            rw [integral_finsetSum]
            · simp
            · intro axis _
              exact hSecondIntegrable axis]
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with point
      simp [primitiveSpinCNullSpherePowerRotationCasimir,
        Finset.mul_sum]
    _ = ((secondDegree : Complex) * (secondDegree + 1 : Nat)) *
        ∫ point,
          star
              (primitiveSpinCNullSpherePower
                firstDegree firstParameter point) *
            primitiveSpinCNullSpherePower
              secondDegree secondParameter point
          ∂SphereMeasure := by
      simp_rw [primitiveSpinCNullSpherePowerRotationCasimir_eq]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with point
      ring

/-- Pointwise scalar pairing between arbitrary positive sphere levels in one
sector and circle mode. -/
theorem primitiveSpinCAllLevelNullHarmonicScalar_pointwise_pairing_cross
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int)
    (point : MonopoleSphere) (time : Real) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity sector circleMode
          |>.scalarSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity sector circleMode
          |>.scalarSection)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      8 *
        star
            (primitiveSpinCNullSpherePower
              (firstPositiveLevel + 1)
              (primitiveSpinCNullGeometricParameter
                firstPositiveLevel firstMultiplicity) point) *
          primitiveSpinCNullSpherePower
            (secondPositiveLevel + 1)
            (primitiveSpinCNullGeometricParameter
              secondPositiveLevel secondMultiplicity) point := by
  unfold d9PrimitiveSpinCPointwiseHermitianPairing
  change
    d9DoubledMatterSpinorHermitianPairing
        (show D9DoubledMatterFiber from
          primitiveSpinCNullPowerSection
            period hPeriod
            (primitiveSpinCNullGeometricParameter
              firstPositiveLevel firstMultiplicity)
            sector circleMode (firstPositiveLevel + 1)
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time))
        (show D9DoubledMatterFiber from
          primitiveSpinCNullPowerSection
            period hPeriod
            (primitiveSpinCNullGeometricParameter
              secondPositiveLevel secondMultiplicity)
            sector circleMode (secondPositiveLevel + 1)
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)) = _
  rw [
    primitiveSpinCNullPowerSection_apply_movingWitness
      period hPeriod,
    primitiveSpinCNullPowerSection_apply_movingWitness
      period hPeriod,
    d9DoubledMatterSpinorHermitianPairing_complexAction_left,
    d9DoubledMatterSpinorHermitianPairing_complexAction_right,
    primitiveSpinCHopfZeroMode_pointwise_self_eq_eight
      period hPeriod sector circleMode point time]
  simp only [primitiveSpinCNullSpherePower, starRingEnd_apply]
  ring

/-- Pointwise gradient pairing between arbitrary positive sphere levels in
one sector and circle mode. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_pointwise_pairing_cross
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int)
    (point : MonopoleSphere) (time : Real) :
    d9PrimitiveSpinCPointwiseHermitianPairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity sector circleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity sector circleMode
          |>.gradientSection)
        (primitiveSpinCNullPacketMovingWitnessBase
          period hPeriod point time) =
      8 *
        ((∑ axis : Fin 3,
          star
              (primitiveSpinCNullSpherePowerAngularDerivative
                axis (firstPositiveLevel + 1)
                (primitiveSpinCNullGeometricParameter
                  firstPositiveLevel firstMultiplicity) point) *
            primitiveSpinCNullSpherePowerAngularDerivative
              axis (secondPositiveLevel + 1)
              (primitiveSpinCNullGeometricParameter
                secondPositiveLevel secondMultiplicity) point) +
          Complex.I *
            (∑ coordinate : Fin 3,
              star
                  (primitiveSpinCNullSpherePowerAmbientDerivative
                    (firstPositiveLevel + 1)
                    (primitiveSpinCNullGeometricParameter
                      firstPositiveLevel firstMultiplicity)
                    coordinate point) *
                primitiveSpinCNullSpherePowerAngularDerivative
                  coordinate (secondPositiveLevel + 1)
                  (primitiveSpinCNullGeometricParameter
                    secondPositiveLevel secondMultiplicity) point)) := by
  unfold d9PrimitiveSpinCPointwiseHermitianPairing
  rw [
    primitiveSpinCAllLevelNullHarmonicGradient_apply_movingWitness
      period hPeriod firstPositiveLevel firstMultiplicity sector circleMode
        point time,
    primitiveSpinCAllLevelNullHarmonicGradient_apply_movingWitness
      period hPeriod secondPositiveLevel secondMultiplicity sector circleMode
        point time,
    primitiveSpinCHopfTangentialCombination_pairing
      period hPeriod,
    primitiveSpinCNullSpherePower_tangentialMatrix_contraction_cross
      period hPeriod,
    primitiveSpinCHopfZeroMode_pointwise_self_eq_eight
      period hPeriod sector circleMode point time]
  ring

/-- At each circle time, the cross-level sphere pairing of gradients is the
second Casimir eigenvalue times the scalar pairing. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_sphere_pairing_eq_casimir_cross
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) (time : Real) :
    (∫ point,
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              firstPositiveLevel firstMultiplicity sector circleMode
            |>.gradientSection)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              secondPositiveLevel secondMultiplicity sector circleMode
            |>.gradientSection)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
        ∂SphereMeasure) =
      (primitiveSpinCHarmonicSphereEnergy secondPositiveLevel : Complex) *
        ∫ point,
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                firstPositiveLevel firstMultiplicity sector circleMode
              |>.scalarSection)
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                secondPositiveLevel secondMultiplicity sector circleMode
              |>.scalarSection)
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)
          ∂SphereMeasure := by
  let firstParameter :=
    primitiveSpinCNullGeometricParameter
      firstPositiveLevel firstMultiplicity
  let secondParameter :=
    primitiveSpinCNullGeometricParameter
      secondPositiveLevel secondMultiplicity
  let firstDegree := firstPositiveLevel + 1
  let secondDegree := secondPositiveLevel + 1
  let angularIntegrand : MonopoleSphere → Complex := fun point =>
    ∑ axis : Fin 3,
      star
          (primitiveSpinCNullSpherePowerAngularDerivative
            axis firstDegree firstParameter point) *
        primitiveSpinCNullSpherePowerAngularDerivative
          axis secondDegree secondParameter point
  let mixedIntegrand : MonopoleSphere → Complex := fun point =>
    ∑ coordinate : Fin 3,
      star
          (primitiveSpinCNullSpherePowerAmbientDerivative
            firstDegree firstParameter coordinate point) *
        primitiveSpinCNullSpherePowerAngularDerivative
          coordinate secondDegree secondParameter point
  let scalarIntegrand : MonopoleSphere → Complex := fun point =>
    star
        (primitiveSpinCNullSpherePower
          firstDegree firstParameter point) *
      primitiveSpinCNullSpherePower
        secondDegree secondParameter point
  have hAngularIntegrable :
      Integrable angularIntegrand SphereMeasure :=
    integrable_finsetSum _ fun axis _ =>
      ((primitiveSpinCNullSpherePowerAngularDerivative_continuous
        axis firstDegree firstParameter).star.mul
          (primitiveSpinCNullSpherePowerAngularDerivative_continuous
            axis secondDegree secondParameter))
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  have hMixedIntegrable :
      Integrable mixedIntegrand SphereMeasure :=
    integrable_finsetSum _ fun coordinate _ =>
      ((primitiveSpinCNullSpherePowerAmbientDerivative_continuous
        firstDegree firstParameter coordinate).star.mul
          (primitiveSpinCNullSpherePowerAngularDerivative_continuous
            coordinate secondDegree secondParameter))
        |>.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  calc
    (∫ point,
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              firstPositiveLevel firstMultiplicity sector circleMode
            |>.gradientSection)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              secondPositiveLevel secondMultiplicity sector circleMode
            |>.gradientSection)
          (primitiveSpinCNullPacketMovingWitnessBase
            period hPeriod point time)
        ∂SphereMeasure) =
        ∫ point,
          8 * (angularIntegrand point +
            Complex.I * mixedIntegrand point)
          ∂SphereMeasure := by
      apply integral_congr_ae
      filter_upwards with point
      rw [primitiveSpinCAllLevelNullHarmonicGradient_pointwise_pairing_cross
        period hPeriod firstPositiveLevel secondPositiveLevel
        firstMultiplicity secondMultiplicity sector circleMode point time]
    _ = 8 * ((∫ point, angularIntegrand point ∂SphereMeasure) +
        Complex.I * ∫ point, mixedIntegrand point ∂SphereMeasure) := by
      rw [integral_const_mul,
        integral_add hAngularIntegrable
          (hMixedIntegrable.const_mul Complex.I),
        integral_const_mul]
    _ = 8 *
        (((secondDegree : Complex) * (secondDegree + 1 : Nat)) *
            (∫ point, scalarIntegrand point ∂SphereMeasure) +
          Complex.I * 0) := by
      rw [
        show (∫ point, angularIntegrand point ∂SphereMeasure) =
            ((secondDegree : Complex) * (secondDegree + 1 : Nat)) *
              ∫ point, scalarIntegrand point ∂SphereMeasure by
          exact
            primitiveSpinCNullSpherePower_angular_energy_eq_casimir_cross
              firstDegree secondDegree firstParameter secondParameter,
        show (∫ point, mixedIntegrand point ∂SphereMeasure) = 0 by
          exact
            primitiveSpinCNullSpherePowerAmbientDerivative_angular_sum_zero_cross
              firstDegree secondDegree firstParameter secondParameter]
    _ = (primitiveSpinCHarmonicSphereEnergy secondPositiveLevel : Complex) *
        ∫ point, 8 * scalarIntegrand point ∂SphereMeasure := by
      rw [integral_const_mul, primitiveSpinCHarmonicSphereEnergy_eq]
      dsimp only [secondDegree]
      push_cast
      ring
    _ = (primitiveSpinCHarmonicSphereEnergy secondPositiveLevel : Complex) *
        ∫ point,
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                firstPositiveLevel firstMultiplicity sector circleMode
              |>.scalarSection)
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                secondPositiveLevel secondMultiplicity sector circleMode
              |>.scalarSection)
            (primitiveSpinCNullPacketMovingWitnessBase
              period hPeriod point time)
          ∂SphereMeasure := by
      congr 1
      apply integral_congr_ae
      filter_upwards with point
      rw [primitiveSpinCAllLevelNullHarmonicScalar_pointwise_pairing_cross
        period hPeriod firstPositiveLevel secondPositiveLevel
        firstMultiplicity secondMultiplicity sector circleMode point time]
      dsimp only [scalarIntegrand, firstDegree, secondDegree,
        firstParameter, secondParameter]
      ring

/-- The global geometric L² cross-level gradient pairing transfers the
second sphere Casimir. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_pairing_eq_casimir_cross
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity sector circleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity sector circleMode
          |>.gradientSection) =
      (primitiveSpinCHarmonicSphereEnergy secondPositiveLevel : Complex) *
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              firstPositiveLevel firstMultiplicity sector circleMode
            |>.scalarSection)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              secondPositiveLevel secondMultiplicity sector circleMode
            |>.scalarSection) := by
  let firstGradient : SmoothSection period hPeriod :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        firstPositiveLevel firstMultiplicity sector circleMode
      |>.gradientSection)
  let secondGradient : SmoothSection period hPeriod :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        secondPositiveLevel secondMultiplicity sector circleMode
      |>.gradientSection)
  let firstScalar : SmoothSection period hPeriod :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        firstPositiveLevel firstMultiplicity sector circleMode
      |>.scalarSection)
  let secondScalar : SmoothSection period hPeriod :=
    ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
      period hPeriod).seed
        secondPositiveLevel secondMultiplicity sector circleMode
      |>.scalarSection)
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter firstGradient secondGradient =
      (primitiveSpinCHarmonicSphereEnergy secondPositiveLevel : Complex) *
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter firstScalar secondScalar
  rw [
    d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral
      period hPeriod .positiveQuarter firstGradient secondGradient,
    d9PrimitiveSpinCGeometricL2Pairing_eq_latitudeBaseIntegral
      period hPeriod .positiveQuarter firstScalar secondScalar]
  have hGradientIntrinsic :=
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod .positiveQuarter firstGradient secondGradient
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
    at hGradientIntrinsic
  have hGradientPullback :
      Integrable
        (fun base : CanonicalLatitudeBase =>
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter firstGradient secondGradient
            (canonicalLatitudeThroatMap period hPeriod base))
        (canonicalLatitudeBaseMeasure period) := by
    simpa [Function.comp_def] using
      hGradientIntrinsic.comp_measurable
        (canonicalLatitudeThroatMap_continuous
          period hPeriod).measurable
  have hScalarIntrinsic :=
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod .positiveQuarter firstScalar secondScalar
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
    at hScalarIntrinsic
  have hScalarPullback :
      Integrable
        (fun base : CanonicalLatitudeBase =>
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter firstScalar secondScalar
            (canonicalLatitudeThroatMap period hPeriod base))
        (canonicalLatitudeBaseMeasure period) := by
    simpa [Function.comp_def] using
      hScalarIntrinsic.comp_measurable
        (canonicalLatitudeThroatMap_continuous
          period hPeriod).measurable
  unfold canonicalLatitudeBaseMeasure at hGradientPullback hScalarPullback ⊢
  rw [integral_prod_symm _ hGradientPullback,
    integral_prod_symm _ hScalarPullback,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with time
  change
    (∫ point,
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter firstGradient secondGradient
          (canonicalLatitudeThroatMap period hPeriod (point, time))
        ∂SphereMeasure) =
      (primitiveSpinCHarmonicSphereEnergy secondPositiveLevel : Complex) *
        ∫ point,
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter firstScalar secondScalar
            (canonicalLatitudeThroatMap period hPeriod (point, time))
          ∂SphereMeasure
  simp_rw [canonicalLatitudeThroatMap_eq_nullPacketMovingWitnessBase]
  exact
    primitiveSpinCAllLevelNullHarmonicGradient_sphere_pairing_eq_casimir_cross
      period hPeriod firstPositiveLevel secondPositiveLevel
      firstMultiplicity secondMultiplicity sector circleMode time

/-- Gradients belonging to distinct sphere levels are orthogonal. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_level_orthogonal
    (firstPositiveLevel secondPositiveLevel : Nat)
    (hLevels : firstPositiveLevel ≠ secondPositiveLevel)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (sector : NormalRootChoice) (circleMode : Int) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity sector circleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity sector circleMode
          |>.gradientSection) = 0 := by
  rw [primitiveSpinCAllLevelNullHarmonicGradient_pairing_eq_casimir_cross
    period hPeriod firstPositiveLevel secondPositiveLevel
    firstMultiplicity secondMultiplicity sector circleMode]
  have hShifted :
      firstPositiveLevel + 1 ≠ secondPositiveLevel + 1 := by
    omega
  have hScalar :=
    primitiveSpinCGeometricL2RawBlockFamily_level_orthogonal
      period hPeriod (firstPositiveLevel + 1) (secondPositiveLevel + 1)
      hShifted sector circleMode firstMultiplicity secondMultiplicity
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity sector circleMode
          |>.scalarSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity sector circleMode
          |>.scalarSection) = 0 at hScalar
  rw [hScalar, mul_zero]

/-! ## Orthogonality of distinct signed spectral labels -/

/-- Arbitrary scalar raw blocks are orthogonal whenever at least one of
their three spectral labels differs. -/
theorem primitiveSpinCGeometricL2RawBlockFamily_labels_orthogonal
    (firstLevel secondLevel : Nat)
    (firstSector secondSector : NormalRootChoice)
    (firstCircleMode secondCircleMode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy firstLevel))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy secondLevel))
    (hLabels :
      firstLevel ≠ secondLevel ∨
        firstSector ≠ secondSector ∨
        firstCircleMode ≠ secondCircleMode) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod firstLevel firstSector firstCircleMode
            firstMultiplicity)
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod secondLevel secondSector secondCircleMode
            secondMultiplicity) = 0 := by
  by_cases hSectors : firstSector = secondSector
  · subst secondSector
    by_cases hModes : firstCircleMode = secondCircleMode
    · subst secondCircleMode
      have hLevels : firstLevel ≠ secondLevel := by
        intro hLevels
        subst secondLevel
        exact hLabels.elim (fun h => h rfl)
          (fun h => h.elim (fun h => h rfl) (fun h => h rfl))
      exact
        primitiveSpinCGeometricL2RawBlockFamily_level_orthogonal
          period hPeriod firstLevel secondLevel hLevels firstSector
          firstCircleMode firstMultiplicity secondMultiplicity
    · exact
        primitiveSpinCGeometricL2RawBlockFamily_circleMode_orthogonal
          period hPeriod firstLevel secondLevel firstSector firstCircleMode
          secondCircleMode hModes firstMultiplicity secondMultiplicity
  · cases firstSector <;> cases secondSector
    · exact (hSectors rfl).elim
    · exact
        primitiveSpinCGeometricL2RawBlockFamily_sectors_orthogonal
          period hPeriod firstLevel secondLevel firstCircleMode
          secondCircleMode firstMultiplicity secondMultiplicity
    · have hForward :
          d9PrimitiveSpinCGeometricL2Pairing
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricL2RawBlockFamily
                period hPeriod secondLevel .positiveQuarter
                  secondCircleMode secondMultiplicity)
              (primitiveSpinCGeometricL2RawBlockFamily
                period hPeriod firstLevel .negativeQuarter
                  firstCircleMode firstMultiplicity) = 0 :=
        primitiveSpinCGeometricL2RawBlockFamily_sectors_orthogonal
          period hPeriod secondLevel firstLevel secondCircleMode
          firstCircleMode secondMultiplicity firstMultiplicity
      rw [← d9PrimitiveSpinCGeometricL2Pairing_conj_symm
        period hPeriod .positiveQuarter, hForward]
      simp
    · exact (hSectors rfl).elim

/-- The sphere-level-zero raw block is the Hopf seed and has positive
radial Clifford parity. -/
theorem primitiveSpinCGeometricL2RawZeroBlockFamily_mem_positiveRadial
    (sector : NormalRootChoice) (circleMode : Int)
    (multiplicity : Fin (primitiveSphereModeDegeneracy 0)) :
    primitiveSpinCGeometricL2RawBlockFamily
        period hPeriod 0 sector circleMode multiplicity ∈
      primitiveSpinCGeometricL2PositiveRadialSubmodule
        period hPeriod := by
  intro base
  change
    d9PrimitiveSpinCBaseUnitRadialClifford period hPeriod base
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode base) =
      d9PrimitiveSpinCImaginaryAction
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector circleMode base)
  exact primitiveSpinCHopfZeroModeSection_baseUnitRadial_eigen
    period hPeriod sector circleMode base

/-- A sphere-level-zero scalar packet is orthogonal to every positive-level
gradient packet, independently of sector and circle labels. -/
theorem primitiveSpinCGeometricL2RawZeroBlockFamily_gradient_orthogonal
    (zeroSector positiveSector : NormalRootChoice)
    (zeroCircleMode positiveCircleMode : Int)
    (zeroMultiplicity : Fin (primitiveSphereModeDegeneracy 0))
    (positiveLevel : Nat)
    (positiveMultiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod 0 zeroSector zeroCircleMode zeroMultiplicity)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel positiveMultiplicity positiveSector
              positiveCircleMode
          |>.gradientSection) = 0 := by
  change
    inner Complex
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod 0 zeroSector zeroCircleMode zeroMultiplicity)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel positiveMultiplicity positiveSector
              positiveCircleMode
          |>.gradientSection) = 0
  exact
    Submodule.isOrtho_iff_inner_eq.mp
      (primitiveSpinCGeometricL2RadialSubmodules_isOrtho
        period hPeriod)
      _
      (primitiveSpinCGeometricL2RawZeroBlockFamily_mem_positiveRadial
        period hPeriod zeroSector zeroCircleMode zeroMultiplicity)
      _
      (primitiveSpinCAllLevelNullHarmonicGradient_mem_negativeRadial
        period hPeriod positiveLevel positiveMultiplicity positiveSector
        positiveCircleMode)

/-- Every zero packet is orthogonal to every positive-level signed raw
eigensection. -/
theorem primitiveSpinCGeometricL2RawZeroBlockFamily_signedRaw_orthogonal
    (zeroSector positiveSector : NormalRootChoice)
    (zeroCircleMode positiveCircleMode : Int)
    (zeroMultiplicity : Fin (primitiveSphereModeDegeneracy 0))
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch)
    (positiveMultiplicity :
      Fin (primitiveSphereModeDegeneracy (positiveLevel + 1))) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod 0 zeroSector zeroCircleMode zeroMultiplicity)
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod positiveLevel branch positiveSector
            positiveCircleMode positiveMultiplicity) = 0 := by
  rw [
    primitiveSpinCGeometricL2SignedBranchRawFamily_eq_radial_components]
  change
    inner Complex
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod 0 zeroSector zeroCircleMode zeroMultiplicity)
        (primitiveSpinCGeometricL2SignedBranchScalarCoefficient
              period positiveLevel branch positiveSector positiveCircleMode •
            ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
              period hPeriod).seed
                positiveLevel positiveMultiplicity positiveSector
                  positiveCircleMode
              |>.scalarSection) +
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel positiveMultiplicity positiveSector
                positiveCircleMode
            |>.gradientSection)) = 0
  rw [inner_add_right, inner_smul_right]
  have hScalar :
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod 0 zeroSector zeroCircleMode zeroMultiplicity)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel positiveMultiplicity positiveSector
                positiveCircleMode
            |>.scalarSection) = 0 := by
    change
      d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod 0 zeroSector zeroCircleMode zeroMultiplicity)
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod (positiveLevel + 1) positiveSector
              positiveCircleMode positiveMultiplicity) = 0
    exact
      primitiveSpinCGeometricL2RawBlockFamily_labels_orthogonal
        period hPeriod 0 (positiveLevel + 1) zeroSector positiveSector
        zeroCircleMode positiveCircleMode zeroMultiplicity
        positiveMultiplicity (Or.inl (by omega))
  have hGradient :=
    primitiveSpinCGeometricL2RawZeroBlockFamily_gradient_orthogonal
      period hPeriod zeroSector positiveSector zeroCircleMode
      positiveCircleMode zeroMultiplicity positiveLevel
      positiveMultiplicity
  change
    primitiveSpinCGeometricL2SignedBranchScalarCoefficient
          period positiveLevel branch positiveSector positiveCircleMode *
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod 0 zeroSector zeroCircleMode zeroMultiplicity)
          ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
            period hPeriod).seed
              positiveLevel positiveMultiplicity positiveSector
                positiveCircleMode
            |>.scalarSection) +
      d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2RawBlockFamily
          period hPeriod 0 zeroSector zeroCircleMode zeroMultiplicity)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            positiveLevel positiveMultiplicity positiveSector
              positiveCircleMode
          |>.gradientSection) = 0
  rw [hScalar, hGradient]
  simp

/-- The complete zero scalar block is orthogonal to one positive signed
branch block. -/
theorem primitiveSpinCGeometricL2RawZeroBlockSpan_signedBranch_isOrtho
    (zeroSector positiveSector : NormalRootChoice)
    (zeroCircleMode positiveCircleMode : Int)
    (positiveLevel : Nat) (branch : PrimitiveSpinCDiracBranch) :
    Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod 0 zeroSector zeroCircleMode)) ⟂
      primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod positiveLevel branch positiveSector
          positiveCircleMode := by
  unfold primitiveSpinCGeometricL2SignedBranchBlock
  rw [Submodule.isOrtho_iff_inner_eq]
  intro first hFirst second hSecond
  refine Submodule.span_induction
    (p := fun first _ => inner Complex first second = 0)
    ?_ (by simp) ?_ ?_ hFirst
  · rintro _ ⟨zeroMultiplicity, rfl⟩
    refine Submodule.span_induction
      (p := fun second _ =>
        inner Complex
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod 0 zeroSector zeroCircleMode zeroMultiplicity)
          second = 0)
      ?_ (by simp) ?_ ?_ hSecond
    · rintro _ ⟨positiveMultiplicity, rfl⟩
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod 0 zeroSector zeroCircleMode zeroMultiplicity)
            (primitiveSpinCGeometricL2SignedBranchRawFamily
              period hPeriod positiveLevel branch positiveSector
                positiveCircleMode positiveMultiplicity) = 0
      exact
        primitiveSpinCGeometricL2RawZeroBlockFamily_signedRaw_orthogonal
          period hPeriod zeroSector positiveSector zeroCircleMode
          positiveCircleMode zeroMultiplicity positiveLevel branch
          positiveMultiplicity
    · intro left right _ _ hLeft hRight
      rw [inner_add_right, hLeft, hRight, add_zero]
    · intro scalar state _ hState
      rw [inner_smul_right, hState, mul_zero]
  · intro left right _ _ hLeft hRight
    rw [inner_add_left, hLeft, hRight, add_zero]
  · intro scalar state _ hState
    rw [inner_smul_left, hState, mul_zero]

/-- The complete zero scalar block is orthogonal to the positive two-sign
block. -/
theorem primitiveSpinCGeometricL2RawZeroBlockSpan_signedBlock_isOrtho
    (zeroSector positiveSector : NormalRootChoice)
    (zeroCircleMode positiveCircleMode : Int)
    (positiveLevel : Nat) :
    Submodule.span Complex
        (Set.range
          (primitiveSpinCGeometricL2RawBlockFamily
            period hPeriod 0 zeroSector zeroCircleMode)) ⟂
      primitiveSpinCGeometricL2SignedBlock
        period hPeriod positiveLevel positiveSector positiveCircleMode := by
  rw [primitiveSpinCGeometricL2SignedBlock,
    Submodule.isOrtho_sup_right]
  exact
    ⟨primitiveSpinCGeometricL2RawZeroBlockSpan_signedBranch_isOrtho
        period hPeriod zeroSector positiveSector zeroCircleMode
        positiveCircleMode positiveLevel .positive,
      primitiveSpinCGeometricL2RawZeroBlockSpan_signedBranch_isOrtho
        period hPeriod zeroSector positiveSector zeroCircleMode
        positiveCircleMode positiveLevel .negative⟩

/-- Scalar packets are orthogonal whenever at least one of their sphere,
sector, or circle labels differs. -/
theorem primitiveSpinCAllLevelNullHarmonicScalar_labels_orthogonal
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (firstSector secondSector : NormalRootChoice)
    (firstCircleMode secondCircleMode : Int)
    (hLabels :
      firstPositiveLevel ≠ secondPositiveLevel ∨
        firstSector ≠ secondSector ∨
        firstCircleMode ≠ secondCircleMode) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity firstSector firstCircleMode
          |>.scalarSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity secondSector
              secondCircleMode
          |>.scalarSection) = 0 := by
  by_cases hSectors : firstSector = secondSector
  · subst secondSector
    by_cases hModes : firstCircleMode = secondCircleMode
    · subst secondCircleMode
      have hLevels : firstPositiveLevel ≠ secondPositiveLevel := by
        intro hLevels
        subst secondPositiveLevel
        exact hLabels.elim (fun h => h rfl)
          (fun h => h.elim (fun h => h rfl) (fun h => h rfl))
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod (firstPositiveLevel + 1) firstSector
                firstCircleMode firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod (secondPositiveLevel + 1) firstSector
                firstCircleMode secondMultiplicity) = 0
      exact
        primitiveSpinCGeometricL2RawBlockFamily_level_orthogonal
          period hPeriod (firstPositiveLevel + 1)
          (secondPositiveLevel + 1) (by omega) firstSector
          firstCircleMode firstMultiplicity secondMultiplicity
    · change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod (firstPositiveLevel + 1) firstSector
                firstCircleMode firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod (secondPositiveLevel + 1) firstSector
                secondCircleMode secondMultiplicity) = 0
      exact
        primitiveSpinCGeometricL2RawBlockFamily_circleMode_orthogonal
          period hPeriod (firstPositiveLevel + 1)
          (secondPositiveLevel + 1) firstSector firstCircleMode
          secondCircleMode hModes firstMultiplicity secondMultiplicity
  · cases firstSector <;> cases secondSector
    · exact (hSectors rfl).elim
    · change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod (firstPositiveLevel + 1) .positiveQuarter
                firstCircleMode firstMultiplicity)
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod (secondPositiveLevel + 1) .negativeQuarter
                secondCircleMode secondMultiplicity) = 0
      exact
        primitiveSpinCGeometricL2RawBlockFamily_sectors_orthogonal
          period hPeriod (firstPositiveLevel + 1)
          (secondPositiveLevel + 1) firstCircleMode secondCircleMode
          firstMultiplicity secondMultiplicity
    · have hForward :
          d9PrimitiveSpinCGeometricL2Pairing
              period hPeriod .positiveQuarter
              ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
                period hPeriod).seed
                  secondPositiveLevel secondMultiplicity .positiveQuarter
                    secondCircleMode
                |>.scalarSection)
              ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
                period hPeriod).seed
                  firstPositiveLevel firstMultiplicity .negativeQuarter
                    firstCircleMode
                |>.scalarSection) = 0 := by
        change
          d9PrimitiveSpinCGeometricL2Pairing
              period hPeriod .positiveQuarter
              (primitiveSpinCGeometricL2RawBlockFamily
                period hPeriod (secondPositiveLevel + 1) .positiveQuarter
                  secondCircleMode secondMultiplicity)
              (primitiveSpinCGeometricL2RawBlockFamily
                period hPeriod (firstPositiveLevel + 1) .negativeQuarter
                  firstCircleMode firstMultiplicity) = 0
        exact
          primitiveSpinCGeometricL2RawBlockFamily_sectors_orthogonal
            period hPeriod (secondPositiveLevel + 1)
            (firstPositiveLevel + 1) secondCircleMode firstCircleMode
            secondMultiplicity firstMultiplicity
      rw [← d9PrimitiveSpinCGeometricL2Pairing_conj_symm
        period hPeriod .positiveQuarter, hForward]
      simp
    · exact (hSectors rfl).elim

/-- Gradient packets obey the same exact three-label orthogonality. -/
theorem primitiveSpinCAllLevelNullHarmonicGradient_labels_orthogonal
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (firstSector secondSector : NormalRootChoice)
    (firstCircleMode secondCircleMode : Int)
    (hLabels :
      firstPositiveLevel ≠ secondPositiveLevel ∨
        firstSector ≠ secondSector ∨
        firstCircleMode ≠ secondCircleMode) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            firstPositiveLevel firstMultiplicity firstSector firstCircleMode
          |>.gradientSection)
        ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
          period hPeriod).seed
            secondPositiveLevel secondMultiplicity secondSector
              secondCircleMode
          |>.gradientSection) = 0 := by
  by_cases hSectors : firstSector = secondSector
  · subst secondSector
    by_cases hModes : firstCircleMode = secondCircleMode
    · subst secondCircleMode
      have hLevels : firstPositiveLevel ≠ secondPositiveLevel := by
        intro hLevels
        subst secondPositiveLevel
        exact hLabels.elim (fun h => h rfl)
          (fun h => h.elim (fun h => h rfl) (fun h => h rfl))
      exact
        primitiveSpinCAllLevelNullHarmonicGradient_level_orthogonal
          period hPeriod firstPositiveLevel secondPositiveLevel hLevels
          firstMultiplicity secondMultiplicity firstSector firstCircleMode
    · exact
        primitiveSpinCAllLevelNullHarmonicGradient_circleMode_orthogonal
          period hPeriod firstPositiveLevel secondPositiveLevel
          firstMultiplicity secondMultiplicity firstSector firstCircleMode
          secondCircleMode hModes
  · cases firstSector <;> cases secondSector
    · exact (hSectors rfl).elim
    · exact
        primitiveSpinCAllLevelNullHarmonicGradient_sectors_orthogonal
          period hPeriod firstPositiveLevel secondPositiveLevel
          firstMultiplicity secondMultiplicity firstCircleMode
          secondCircleMode
    · have hForward :
          d9PrimitiveSpinCGeometricL2Pairing
              period hPeriod .positiveQuarter
              ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
                period hPeriod).seed
                  secondPositiveLevel secondMultiplicity .positiveQuarter
                    secondCircleMode
                |>.gradientSection)
              ((primitiveSpinCAllLevelNullHarmonicDiracSeedTower
                period hPeriod).seed
                  firstPositiveLevel firstMultiplicity .negativeQuarter
                    firstCircleMode
                |>.gradientSection) = 0 :=
        primitiveSpinCAllLevelNullHarmonicGradient_sectors_orthogonal
          period hPeriod secondPositiveLevel firstPositiveLevel
          secondMultiplicity firstMultiplicity secondCircleMode
          firstCircleMode
      rw [← d9PrimitiveSpinCGeometricL2Pairing_conj_symm
        period hPeriod .positiveQuarter, hForward]
      simp
    · exact (hSectors rfl).elim

/-- Signed raw eigensections are orthogonal whenever their unsigned
sphere/sector/circle labels differ, independently of branch signs. -/
theorem primitiveSpinCGeometricL2SignedBranchRawFamily_labels_orthogonal
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstBranch secondBranch : PrimitiveSpinCDiracBranch)
    (firstSector secondSector : NormalRootChoice)
    (firstCircleMode secondCircleMode : Int)
    (firstMultiplicity :
      Fin (primitiveSphereModeDegeneracy (firstPositiveLevel + 1)))
    (secondMultiplicity :
      Fin (primitiveSphereModeDegeneracy (secondPositiveLevel + 1)))
    (hLabels :
      firstPositiveLevel ≠ secondPositiveLevel ∨
        firstSector ≠ secondSector ∨
        firstCircleMode ≠ secondCircleMode) :
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod firstPositiveLevel firstBranch firstSector
            firstCircleMode firstMultiplicity)
        (primitiveSpinCGeometricL2SignedBranchRawFamily
          period hPeriod secondPositiveLevel secondBranch secondSector
            secondCircleMode secondMultiplicity) = 0 := by
  rw [
    primitiveSpinCGeometricL2SignedBranchRawFamily_pairing_eq_diagonal,
    primitiveSpinCAllLevelNullHarmonicScalar_labels_orthogonal
      period hPeriod firstPositiveLevel secondPositiveLevel
      firstMultiplicity secondMultiplicity firstSector secondSector
      firstCircleMode secondCircleMode hLabels,
    primitiveSpinCAllLevelNullHarmonicGradient_labels_orthogonal
      period hPeriod firstPositiveLevel secondPositiveLevel
      firstMultiplicity secondMultiplicity firstSector secondSector
      firstCircleMode secondCircleMode hLabels]
  ring

/-- Distinct fixed-label signed branch spans are mutually orthogonal. -/
theorem primitiveSpinCGeometricL2SignedBranchBlocks_labels_isOrtho
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstBranch secondBranch : PrimitiveSpinCDiracBranch)
    (firstSector secondSector : NormalRootChoice)
    (firstCircleMode secondCircleMode : Int)
    (hLabels :
      firstPositiveLevel ≠ secondPositiveLevel ∨
        firstSector ≠ secondSector ∨
        firstCircleMode ≠ secondCircleMode) :
    primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod firstPositiveLevel firstBranch firstSector
          firstCircleMode ⟂
      primitiveSpinCGeometricL2SignedBranchBlock
        period hPeriod secondPositiveLevel secondBranch secondSector
          secondCircleMode := by
  unfold primitiveSpinCGeometricL2SignedBranchBlock
  rw [Submodule.isOrtho_iff_inner_eq]
  intro first hFirst second hSecond
  refine Submodule.span_induction
    (p := fun first _ => inner Complex first second = 0)
    ?_ (by simp) ?_ ?_ hFirst
  · rintro _ ⟨firstMultiplicity, rfl⟩
    refine Submodule.span_induction
      (p := fun second _ =>
        inner Complex
          (primitiveSpinCGeometricL2SignedBranchRawFamily
            period hPeriod firstPositiveLevel firstBranch firstSector
              firstCircleMode firstMultiplicity)
          second = 0)
      ?_ (by simp) ?_ ?_ hSecond
    · rintro _ ⟨secondMultiplicity, rfl⟩
      change
        d9PrimitiveSpinCGeometricL2Pairing
            period hPeriod .positiveQuarter
            (primitiveSpinCGeometricL2SignedBranchRawFamily
              period hPeriod firstPositiveLevel firstBranch firstSector
                firstCircleMode firstMultiplicity)
            (primitiveSpinCGeometricL2SignedBranchRawFamily
              period hPeriod secondPositiveLevel secondBranch secondSector
                secondCircleMode secondMultiplicity) = 0
      exact
        primitiveSpinCGeometricL2SignedBranchRawFamily_labels_orthogonal
          period hPeriod firstPositiveLevel secondPositiveLevel
          firstBranch secondBranch firstSector secondSector
          firstCircleMode secondCircleMode firstMultiplicity
          secondMultiplicity hLabels
    · intro left right _ _ hLeft hRight
      rw [inner_add_right, hLeft, hRight, add_zero]
    · intro scalar state _ hState
      rw [inner_smul_right, hState, mul_zero]
  · intro left right _ _ hLeft hRight
    rw [inner_add_left, hLeft, hRight, add_zero]
  · intro scalar state _ hState
    rw [inner_smul_left, hState, mul_zero]

/-- The complete two-sign blocks are orthogonal across distinct spectral
labels. -/
theorem primitiveSpinCGeometricL2SignedBlocks_labels_isOrtho
    (firstPositiveLevel secondPositiveLevel : Nat)
    (firstSector secondSector : NormalRootChoice)
    (firstCircleMode secondCircleMode : Int)
    (hLabels :
      firstPositiveLevel ≠ secondPositiveLevel ∨
        firstSector ≠ secondSector ∨
        firstCircleMode ≠ secondCircleMode) :
    primitiveSpinCGeometricL2SignedBlock
        period hPeriod firstPositiveLevel firstSector firstCircleMode ⟂
      primitiveSpinCGeometricL2SignedBlock
        period hPeriod secondPositiveLevel secondSector secondCircleMode := by
  rw [primitiveSpinCGeometricL2SignedBlock,
    primitiveSpinCGeometricL2SignedBlock,
    Submodule.isOrtho_sup_left, Submodule.isOrtho_sup_right,
    Submodule.isOrtho_sup_right]
  exact
    ⟨⟨primitiveSpinCGeometricL2SignedBranchBlocks_labels_isOrtho
          period hPeriod firstPositiveLevel secondPositiveLevel
          .positive .positive firstSector secondSector firstCircleMode
          secondCircleMode hLabels,
        primitiveSpinCGeometricL2SignedBranchBlocks_labels_isOrtho
          period hPeriod firstPositiveLevel secondPositiveLevel
          .positive .negative firstSector secondSector firstCircleMode
          secondCircleMode hLabels⟩,
      primitiveSpinCGeometricL2SignedBranchBlocks_labels_isOrtho
        period hPeriod firstPositiveLevel secondPositiveLevel
        .negative .positive firstSector secondSector firstCircleMode
        secondCircleMode hLabels,
      primitiveSpinCGeometricL2SignedBranchBlocks_labels_isOrtho
        period hPeriod firstPositiveLevel secondPositiveLevel
        .negative .negative firstSector secondSector firstCircleMode
        secondCircleMode hLabels⟩

/-! ## Positive signed Hilbert sum and exact exhaustion of its range -/

/-- One complete positive-level two-sign geometric spectral block. -/
structure PrimitiveSpinCGeometricL2SignedPositiveBlockIndex where
  positiveLevel : Nat
  sector : NormalRootChoice
  circleMode : Int
deriving DecidableEq

/-- Euclidean coordinates of one complete two-sign block. -/
abbrev PrimitiveSpinCGeometricL2SignedPositiveBlockCoefficients
    (block : PrimitiveSpinCGeometricL2SignedPositiveBlockIndex) :=
  PrimitiveSpinCGeometricL2SignedBlockCoefficients
    period hPeriod block.positiveLevel block.sector block.circleMode

/-- Completed Parseval map of one complete two-sign block. -/
def primitiveSpinCGeometricL2CompletedSignedPositiveBlockIsometry
    (block : PrimitiveSpinCGeometricL2SignedPositiveBlockIndex) :
    PrimitiveSpinCGeometricL2SignedPositiveBlockCoefficients
        period hPeriod block →ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  primitiveSpinCGeometricL2CompletedSignedBlockIsometry
    period hPeriod block.positiveLevel block.sector block.circleMode

@[simp]
theorem primitiveSpinCGeometricL2CompletedSignedPositiveBlockIsometry_apply
    (block : PrimitiveSpinCGeometricL2SignedPositiveBlockIndex)
    (coefficients :
      PrimitiveSpinCGeometricL2SignedPositiveBlockCoefficients
        period hPeriod block) :
    primitiveSpinCGeometricL2CompletedSignedPositiveBlockIsometry
        period hPeriod block coefficients =
      (primitiveSpinCGeometricL2SignedBlockSynthesis
        period hPeriod block.positiveLevel block.sector block.circleMode
        coefficients :
          D9PrimitiveSpinCGeometricL2Completion
            period hPeriod .positiveQuarter) := by
  rfl

/-- Distinct complete signed positive blocks have orthogonal images. -/
theorem primitiveSpinCGeometricL2CompletedSignedPositiveBlocks_orthogonalFamily :
    OrthogonalFamily Complex
      (PrimitiveSpinCGeometricL2SignedPositiveBlockCoefficients
        period hPeriod)
      (primitiveSpinCGeometricL2CompletedSignedPositiveBlockIsometry
        period hPeriod) := by
  rintro ⟨firstLevel, firstSector, firstMode⟩
    ⟨secondLevel, secondSector, secondMode⟩ hBlocks first second
  simp only [
    primitiveSpinCGeometricL2CompletedSignedPositiveBlockIsometry_apply,
    UniformSpace.Completion.inner_coe]
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod firstLevel firstSector firstMode first)
        (primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod secondLevel secondSector secondMode second) = 0
  have hLabels :
      firstLevel ≠ secondLevel ∨
        firstSector ≠ secondSector ∨
        firstMode ≠ secondMode := by
    by_contra hEqual
    push Not at hEqual
    rcases hEqual with ⟨hLevel, hSector, hMode⟩
    subst secondLevel
    subst secondSector
    subst secondMode
    exact hBlocks rfl
  have hFirst :
      primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod firstLevel firstSector firstMode first ∈
        primitiveSpinCGeometricL2SignedBlock
          period hPeriod firstLevel firstSector firstMode := by
    change
      (∑ index,
        first index •
          primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
            period hPeriod firstLevel firstSector firstMode index) ∈ _
    apply Submodule.sum_mem
    intro index _
    exact Submodule.smul_mem _ _
      (primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
        period hPeriod firstLevel firstSector firstMode index).property
  have hSecond :
      primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod secondLevel secondSector secondMode second ∈
        primitiveSpinCGeometricL2SignedBlock
          period hPeriod secondLevel secondSector secondMode := by
    change
      (∑ index,
        second index •
          primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
            period hPeriod secondLevel secondSector secondMode index) ∈ _
    apply Submodule.sum_mem
    intro index _
    exact Submodule.smul_mem _ _
      (primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
        period hPeriod secondLevel secondSector secondMode index).property
  exact
    Submodule.isOrtho_iff_inner_eq.mp
      (primitiveSpinCGeometricL2SignedBlocks_labels_isOrtho
        period hPeriod firstLevel secondLevel firstSector secondSector
        firstMode secondMode hLabels)
      _ hFirst _ hSecond

/-- Hilbert direct sum of all complete positive-level signed blocks. -/
abbrev PrimitiveSpinCGeometricL2SignedPositiveJointCoefficients :=
  lp
    (PrimitiveSpinCGeometricL2SignedPositiveBlockCoefficients
      period hPeriod) 2

/-- Canonical signed synthesis over every positive level, sector, circle
mode and both first-order branches. -/
def primitiveSpinCGeometricL2SignedPositiveJointSynthesis :
    PrimitiveSpinCGeometricL2SignedPositiveJointCoefficients
        period hPeriod →ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  (primitiveSpinCGeometricL2CompletedSignedPositiveBlocks_orthogonalFamily
    period hPeriod).linearIsometry

@[simp]
theorem primitiveSpinCGeometricL2SignedPositiveJointSynthesis_single
    (block : PrimitiveSpinCGeometricL2SignedPositiveBlockIndex)
    (coefficients :
      PrimitiveSpinCGeometricL2SignedPositiveBlockCoefficients
        period hPeriod block) :
    primitiveSpinCGeometricL2SignedPositiveJointSynthesis period hPeriod
        (lp.single 2 block coefficients) =
      primitiveSpinCGeometricL2CompletedSignedPositiveBlockIsometry
        period hPeriod block coefficients := by
  exact
    (primitiveSpinCGeometricL2CompletedSignedPositiveBlocks_orthogonalFamily
      period hPeriod).linearIsometry_apply_single coefficients

/-- Exact closed range of the positive signed Hilbert sum. -/
theorem primitiveSpinCGeometricL2SignedPositiveJointSynthesis_range :
    LinearMap.range
        (primitiveSpinCGeometricL2SignedPositiveJointSynthesis
          period hPeriod).toLinearMap =
      (⨆ block : PrimitiveSpinCGeometricL2SignedPositiveBlockIndex,
        LinearMap.range
          (primitiveSpinCGeometricL2CompletedSignedPositiveBlockIsometry
            period hPeriod block).toLinearMap).topologicalClosure := by
  exact
    (primitiveSpinCGeometricL2CompletedSignedPositiveBlocks_orthogonalFamily
      period hPeriod).range_linearIsometry

/-- The globally assembled positive signed spectral closed span. -/
abbrev PrimitiveSpinCGeometricL2SignedPositiveSpectralRange :=
  (primitiveSpinCGeometricL2SignedPositiveJointSynthesis
    period hPeriod).range

/-- Unconditional unitary exhaustion of the complete positive signed
spectral range. -/
def primitiveSpinCGeometricL2SignedPositiveSpectralUnitary :
    PrimitiveSpinCGeometricL2SignedPositiveJointCoefficients
        period hPeriod ≃ₗᵢ[Complex]
      PrimitiveSpinCGeometricL2SignedPositiveSpectralRange
        period hPeriod :=
  (primitiveSpinCGeometricL2SignedPositiveJointSynthesis
    period hPeriod).equivRange

/-! ## Global zero-plus-signed-positive Hilbert sum -/

/-- The global signed block labels consist of the scalar zero tower and all
complete two-sign positive-level blocks. -/
inductive PrimitiveSpinCGeometricL2SignedGlobalBlockIndex where
  | zero (sector : NormalRootChoice) (circleMode : Int)
  | positive (block : PrimitiveSpinCGeometricL2SignedPositiveBlockIndex)
deriving DecidableEq

/-- Dimension of one global signed block. -/
def primitiveSpinCGeometricL2SignedGlobalBlockDimension :
    PrimitiveSpinCGeometricL2SignedGlobalBlockIndex → Nat
  | .zero _ _ => primitiveSphereModeDegeneracy 0
  | .positive positiveBlock =>
      finrank Complex
        (primitiveSpinCGeometricL2SignedBlock
          period hPeriod positiveBlock.positiveLevel positiveBlock.sector
            positiveBlock.circleMode)

/-- Coefficients of one global signed block.  The uniform Euclidean-space
presentation keeps all dependent Hilbert-space instances canonical. -/
abbrev PrimitiveSpinCGeometricL2SignedGlobalBlockCoefficients
    (block : PrimitiveSpinCGeometricL2SignedGlobalBlockIndex) :=
  EuclideanSpace Complex
    (Fin
      (primitiveSpinCGeometricL2SignedGlobalBlockDimension
        period hPeriod block))

/-- Completed Parseval map of one global signed block. -/
def primitiveSpinCGeometricL2CompletedSignedGlobalBlockIsometry :
    (block : PrimitiveSpinCGeometricL2SignedGlobalBlockIndex) →
      PrimitiveSpinCGeometricL2SignedGlobalBlockCoefficients
          period hPeriod block →ₗᵢ[Complex]
        D9PrimitiveSpinCGeometricL2Completion
          period hPeriod .positiveQuarter
  | .zero sector circleMode =>
      primitiveSpinCGeometricL2CompletedBlockIsometry
        period hPeriod ⟨0, sector, circleMode⟩
  | .positive positiveBlock =>
      primitiveSpinCGeometricL2CompletedSignedPositiveBlockIsometry
        period hPeriod positiveBlock

/-- Every completed zero block is orthogonal to every completed positive
two-sign block. -/
theorem primitiveSpinCGeometricL2CompletedZero_positiveSigned_inner
    (zeroSector : NormalRootChoice) (zeroCircleMode : Int)
    (positiveBlock : PrimitiveSpinCGeometricL2SignedPositiveBlockIndex)
    (zeroCoefficients :
      PrimitiveSpinCGeometricL2BlockCoefficients
        ⟨0, zeroSector, zeroCircleMode⟩)
    (positiveCoefficients :
      PrimitiveSpinCGeometricL2SignedPositiveBlockCoefficients
        period hPeriod positiveBlock) :
    inner Complex
        (primitiveSpinCGeometricL2CompletedBlockIsometry
          period hPeriod ⟨0, zeroSector, zeroCircleMode⟩ zeroCoefficients)
        (primitiveSpinCGeometricL2CompletedSignedPositiveBlockIsometry
          period hPeriod positiveBlock positiveCoefficients) = 0 := by
  simp only [
    primitiveSpinCGeometricL2CompletedBlockIsometry_apply,
    primitiveSpinCGeometricL2CompletedSignedPositiveBlockIsometry_apply,
    UniformSpace.Completion.inner_coe]
  change
    d9PrimitiveSpinCGeometricL2Pairing
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod 0 zeroSector zeroCircleMode zeroCoefficients)
        (primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod positiveBlock.positiveLevel positiveBlock.sector
            positiveBlock.circleMode positiveCoefficients) = 0
  have hZero :
      primitiveSpinCGeometricL2OrthonormalBlockSynthesis
          period hPeriod 0 zeroSector zeroCircleMode zeroCoefficients ∈
        Submodule.span Complex
          (Set.range
            (primitiveSpinCGeometricL2RawBlockFamily
              period hPeriod 0 zeroSector zeroCircleMode)) := by
    rw [← primitiveSpinCGeometricL2OrthonormalBlockFamily_span
      period hPeriod 0 zeroSector zeroCircleMode]
    change
      (∑ index,
        zeroCoefficients index •
          primitiveSpinCGeometricL2OrthonormalBlockFamily
            period hPeriod 0 zeroSector zeroCircleMode index) ∈ _
    apply Submodule.sum_mem
    intro index _
    exact
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self index))
  have hPositive :
      primitiveSpinCGeometricL2SignedBlockSynthesis
          period hPeriod positiveBlock.positiveLevel positiveBlock.sector
            positiveBlock.circleMode positiveCoefficients ∈
        primitiveSpinCGeometricL2SignedBlock
          period hPeriod positiveBlock.positiveLevel positiveBlock.sector
            positiveBlock.circleMode := by
    change
      (∑ index,
        positiveCoefficients index •
          primitiveSpinCGeometricL2SignedBlockOrthonormalFamily
            period hPeriod positiveBlock.positiveLevel positiveBlock.sector
              positiveBlock.circleMode index) ∈ _
    apply Submodule.sum_mem
    intro index _
    exact
      Submodule.smul_mem _ _
        (primitiveSpinCGeometricL2SignedBlockOrthonormalBasis
          period hPeriod positiveBlock.positiveLevel positiveBlock.sector
            positiveBlock.circleMode index).property
  exact
    Submodule.isOrtho_iff_inner_eq.mp
      (primitiveSpinCGeometricL2RawZeroBlockSpan_signedBlock_isOrtho
        period hPeriod zeroSector positiveBlock.sector zeroCircleMode
          positiveBlock.circleMode positiveBlock.positiveLevel)
      _ hZero _ hPositive

/-- All global zero and positive signed blocks form one orthogonal family. -/
theorem primitiveSpinCGeometricL2CompletedSignedGlobalBlocks_orthogonalFamily :
    OrthogonalFamily Complex
      (PrimitiveSpinCGeometricL2SignedGlobalBlockCoefficients
        period hPeriod)
      (primitiveSpinCGeometricL2CompletedSignedGlobalBlockIsometry
        period hPeriod) := by
  intro firstBlock secondBlock hBlocks firstCoefficients secondCoefficients
  cases firstBlock with
  | zero firstSector firstMode =>
      cases secondBlock with
      | zero secondSector secondMode =>
          apply
            primitiveSpinCGeometricL2CompletedBlocks_orthogonalFamily
              period hPeriod
          intro hScalarBlocks
          have hSectors :
              firstSector = secondSector :=
            congrArg PrimitiveSpinCGeometricL2BlockIndex.sector hScalarBlocks
          have hModes :
              firstMode = secondMode :=
            congrArg PrimitiveSpinCGeometricL2BlockIndex.circleMode
              hScalarBlocks
          subst secondSector
          subst secondMode
          exact hBlocks rfl
      | positive secondPositiveBlock =>
          exact
            primitiveSpinCGeometricL2CompletedZero_positiveSigned_inner
              period hPeriod firstSector firstMode secondPositiveBlock
                firstCoefficients secondCoefficients
  | positive firstPositiveBlock =>
      cases secondBlock with
      | zero secondSector secondMode =>
          rw [inner_eq_zero_symm]
          exact
            primitiveSpinCGeometricL2CompletedZero_positiveSigned_inner
              period hPeriod secondSector secondMode firstPositiveBlock
                secondCoefficients firstCoefficients
      | positive secondPositiveBlock =>
          apply
            primitiveSpinCGeometricL2CompletedSignedPositiveBlocks_orthogonalFamily
              period hPeriod
          intro hPositiveBlocks
          subst secondPositiveBlock
          exact hBlocks rfl

/-- Hilbert direct sum of the zero tower and all complete signed positive
blocks. -/
abbrev PrimitiveSpinCGeometricL2SignedGlobalJointCoefficients :=
  lp
    (PrimitiveSpinCGeometricL2SignedGlobalBlockCoefficients
      period hPeriod) 2

/-- Canonical global signed synthesis, including the zero tower. -/
def primitiveSpinCGeometricL2SignedGlobalJointSynthesis :
    PrimitiveSpinCGeometricL2SignedGlobalJointCoefficients
        period hPeriod →ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  (primitiveSpinCGeometricL2CompletedSignedGlobalBlocks_orthogonalFamily
    period hPeriod).linearIsometry

@[simp]
theorem primitiveSpinCGeometricL2SignedGlobalJointSynthesis_single
    (block : PrimitiveSpinCGeometricL2SignedGlobalBlockIndex)
    (coefficients :
      PrimitiveSpinCGeometricL2SignedGlobalBlockCoefficients
        period hPeriod block) :
    primitiveSpinCGeometricL2SignedGlobalJointSynthesis period hPeriod
        (lp.single 2 block coefficients) =
      primitiveSpinCGeometricL2CompletedSignedGlobalBlockIsometry
        period hPeriod block coefficients := by
  exact
    (primitiveSpinCGeometricL2CompletedSignedGlobalBlocks_orthogonalFamily
      period hPeriod).linearIsometry_apply_single coefficients

/-- The global signed range is exactly the closed span of every zero and
positive signed block. -/
theorem primitiveSpinCGeometricL2SignedGlobalJointSynthesis_range :
    LinearMap.range
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod).toLinearMap =
      (⨆ block : PrimitiveSpinCGeometricL2SignedGlobalBlockIndex,
        LinearMap.range
          (primitiveSpinCGeometricL2CompletedSignedGlobalBlockIsometry
            period hPeriod block).toLinearMap).topologicalClosure := by
  exact
    (primitiveSpinCGeometricL2CompletedSignedGlobalBlocks_orthogonalFamily
      period hPeriod).range_linearIsometry

/-- The exact globally assembled signed spectral closed range. -/
abbrev PrimitiveSpinCGeometricL2SignedGlobalSpectralRange :=
  (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
    period hPeriod).range

/-- Assumption-free unitary exhaustion of the exact global signed spectral
range. -/
def primitiveSpinCGeometricL2SignedGlobalSpectralUnitary :
    PrimitiveSpinCGeometricL2SignedGlobalJointCoefficients
        period hPeriod ≃ₗᵢ[Complex]
      PrimitiveSpinCGeometricL2SignedGlobalSpectralRange
        period hPeriod :=
  (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
    period hPeriod).equivRange

/-- The sole residual statement for an ambient, rather than range-valued,
global unitary is density of the explicit signed family. -/
def PrimitiveSpinCGeometricL2SignedGlobalDensity : Prop :=
  DenseRange
    (primitiveSpinCGeometricL2SignedGlobalJointSynthesis period hPeriod)

theorem
    primitiveSpinCGeometricL2SignedGlobalJointSynthesis_denseRange_iff_surjective :
    PrimitiveSpinCGeometricL2SignedGlobalDensity period hPeriod ↔
      Function.Surjective
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod) := by
  constructor
  · intro hDense
    have hClosed :
        IsClosed
          (Set.range
            (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
              period hPeriod)) :=
      (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
        period hPeriod).isometry
        |>.isUniformInducing.isComplete_range.isClosed
    have hClosure :
        closure
            (Set.range
              (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
                period hPeriod)) =
          Set.univ :=
      dense_iff_closure_eq.mp hDense
    have hRange :
        Set.range
            (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
              period hPeriod) =
          Set.univ := by
      rw [← hClosed.closure_eq, hClosure]
    exact Set.range_eq_univ.mp hRange
  · exact Function.Surjective.denseRange

/-- Conditional ambient unitary.  No unproved completeness premise is hidden:
the only input is the explicit signed-family density theorem. -/
def primitiveSpinCGeometricL2SignedGlobalUnitary
    (hDensity :
      PrimitiveSpinCGeometricL2SignedGlobalDensity period hPeriod) :
    PrimitiveSpinCGeometricL2SignedGlobalJointCoefficients
        period hPeriod ≃ₗᵢ[Complex]
      D9PrimitiveSpinCGeometricL2Completion
        period hPeriod .positiveQuarter :=
  LinearIsometryEquiv.ofSurjective
    (primitiveSpinCGeometricL2SignedGlobalJointSynthesis period hPeriod)
    ((primitiveSpinCGeometricL2SignedGlobalJointSynthesis_denseRange_iff_surjective
      period hPeriod).mp hDensity)

/-- Assumption-free certificate for signed orthogonality, joint Parseval and
unitary exhaustion of the exact signed spectral range. -/
structure ProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometryCertificate4D
    where
  blocksOrthogonal :
    OrthogonalFamily Complex
      (PrimitiveSpinCGeometricL2SignedGlobalBlockCoefficients
        period hPeriod)
      (primitiveSpinCGeometricL2CompletedSignedGlobalBlockIsometry
        period hPeriod)
  jointRange :
    LinearMap.range
        (primitiveSpinCGeometricL2SignedGlobalJointSynthesis
          period hPeriod).toLinearMap =
      (⨆ block : PrimitiveSpinCGeometricL2SignedGlobalBlockIndex,
        LinearMap.range
          (primitiveSpinCGeometricL2CompletedSignedGlobalBlockIsometry
            period hPeriod block).toLinearMap).topologicalClosure
  spectralUnitary :
    PrimitiveSpinCGeometricL2SignedGlobalJointCoefficients
        period hPeriod ≃ₗᵢ[Complex]
      PrimitiveSpinCGeometricL2SignedGlobalSpectralRange
        period hPeriod

def programPD9PrimitiveSpinCGeometricL2SignedJointIsometryCertificate4D :
    ProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometryCertificate4D
      period hPeriod where
  blocksOrthogonal :=
    primitiveSpinCGeometricL2CompletedSignedGlobalBlocks_orthogonalFamily
      period hPeriod
  jointRange :=
    primitiveSpinCGeometricL2SignedGlobalJointSynthesis_range
      period hPeriod
  spectralUnitary :=
    primitiveSpinCGeometricL2SignedGlobalSpectralUnitary
      period hPeriod

theorem primitiveSpinCGeometricL2SignedJointIsometry_gate :
    Nonempty
      (ProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometryCertificate4D
        period hPeriod) :=
  ⟨programPD9PrimitiveSpinCGeometricL2SignedJointIsometryCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2SignedJointIsometry4D
end JanusFormal
