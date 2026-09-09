import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterFiniteModeMeasurableGaugeSupport4D

/-!
# T05 intrinsic SpinC L1 completion

Fixed-fiber SpinC coordinates still lack a measurable gauge selector.  Their
real pointwise Hermitian pairing is nevertheless intrinsic: on the finite
signed-mode core it is integrable and its integral is the coefficient Hilbert
pairing.  Its L1 norm is bounded by the product of the two coefficient norms.

This module extends that scalar L1 pairing twice from the dense finite core.
It therefore gives every maximal graph state an L1 density whose integral is
the exact graph action.  It does not construct a measurable vector-valued L2
representative of the completed SpinC field.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05SpinCMatterIntrinsicL1Completion4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal lp
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05SpinCMatterMaximalLpDensityBridge4D
open P0EFTJanusProgramPT05SpinCMatterFiniteCoreLpExtensionSupport4D
open P0EFTJanusProgramPT05SpinCMatterFiniteCoreMeasurableLpSupport4D
open P0EFTJanusProgramPT05SpinCMatterFiniteModeMeasurableGaugeSupport4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCMatterL1 :=
  Lp Real 1 (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

local instance spinCMatterIntrinsicL1MeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance spinCMatterIntrinsicL1BorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance spinCMatterIntrinsicL1FiniteMeasure :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance spinCMatterIntrinsicL1HilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

local instance spinCMatterIntrinsicL1FiberRealInnerProductSpace :
    InnerProductSpace Real ProgramPT05SpinCMatterPointwiseFiber :=
  InnerProductSpace.complexToReal

/-- The finite coefficient inclusion viewed over the real scalars of the
action. -/
def programPT05SpinCMatterFiniteHilbertEmbeddingReal :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      ProgramPPrimitiveSpinCMatterHilbert :=
  programPPrimitiveSpinCMatterFiniteHilbertEmbedding.restrictScalars Real

/-- The real finite coefficient inclusion still has dense range. -/
theorem programPT05SpinCMatterFiniteHilbertEmbeddingReal_denseRange :
    DenseRange
      (programPT05SpinCMatterFiniteHilbertEmbeddingReal :
        ProgramPPrimitiveSpinCMatterFiniteCoefficients →
          ProgramPPrimitiveSpinCMatterHilbert) := by
  have hCoe :
      (programPT05SpinCMatterFiniteHilbertEmbeddingReal :
          ProgramPPrimitiveSpinCMatterFiniteCoefficients →
            ProgramPPrimitiveSpinCMatterHilbert) =
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding :
          ProgramPPrimitiveSpinCMatterFiniteCoefficients →
            ProgramPPrimitiveSpinCMatterHilbert) := by
    funext coefficients
    rfl
  rw [hCoe]
  exact programPT05SpinCMatterFiniteHilbertEmbedding_denseRange

private def programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      EffectiveThroat period hPeriod → ProgramPT05SpinCMatterPointwiseFiber :=
  (programPT05SpinCMatterFiniteCorePointwiseCoordinatesLinearMap
    period hPeriod).restrictScalars Real

/-- Gauge-independent real scalar pairing of two finite smooth syntheses. -/
def programPT05SpinCMatterFiniteCoreIntrinsicPairing
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (base : EffectiveThroat period hPeriod) : Real :=
  inner Real
    (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
      first base)
    (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
      second base)

/-- The scalar pairing is the real part of the intrinsic doubled-fiber
Hermitian pairing. -/
theorem programPT05SpinCMatterFiniteCoreIntrinsicPairing_eq_intrinsic
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (base : EffectiveThroat period hPeriod) :
    programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        first second base =
      (∑ sector : Sector,
        d9DoubledMatterSpinorHermitianPairing
          (show D9DoubledMatterFiber from
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              first sector base)
          (show D9DoubledMatterFiber from
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              second sector base)).re := by
  unfold programPT05SpinCMatterFiniteCoreIntrinsicPairing
    programPT05SpinCMatterFiniteCorePointwiseCoordinates
  rw [real_inner_eq_re_inner,
    programPT05SpinCMatterPointwiseCoordinates_inner]
  rw [RCLike.re_eq_complex_re]

private theorem programPT05SpinCMatterFiniteCoreIntrinsicPairing_add_left
    (first second third : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        (first + second) third =
      programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
          first third +
        programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
          second third := by
  funext base
  change inner Real
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        (first + second) base)
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        third base) =
    inner Real
        (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
          first base)
        (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
          third base) +
      inner Real
        (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
          second base)
        (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
          third base)
  rw [map_add]
  simp only [Pi.add_apply, inner_add_left]

private theorem programPT05SpinCMatterFiniteCoreIntrinsicPairing_smul_left
    (scalar : Real)
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        (scalar • first) second =
      scalar • programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        first second := by
  funext base
  change inner Real
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        (scalar • first) base)
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        second base) =
    scalar * inner Real
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        first base)
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        second base)
  rw [map_smul]
  simp only [Pi.smul_apply, real_inner_smul_left]

private theorem programPT05SpinCMatterFiniteCoreIntrinsicPairing_add_right
    (first second third : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        first (second + third) =
      programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
          first second +
        programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
          first third := by
  funext base
  change inner Real
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        first base)
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        (second + third) base) =
    inner Real
        (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
          first base)
        (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
          second base) +
      inner Real
        (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
          first base)
        (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
          third base)
  rw [map_add]
  simp only [Pi.add_apply, inner_add_right]

private theorem programPT05SpinCMatterFiniteCoreIntrinsicPairing_smul_right
    (scalar : Real)
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        first (scalar • second) =
      scalar • programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        first second := by
  funext base
  change inner Real
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        first base)
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        (scalar • second) base) =
    scalar * inner Real
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        first base)
      (programPT05SpinCMatterFiniteCoreCoordinatesRealLinearMap period hPeriod
        second base)
  rw [map_smul]
  simp only [Pi.smul_apply, real_inner_smul_right]

/-- The intrinsic real scalar pairing is integrable without a measurable
choice of vector-valued gauge coordinates. -/
theorem programPT05SpinCMatterFiniteCoreIntrinsicPairing_integrable
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    Integrable
      (programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        first second)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have hComplex :=
    programPT05SpinCMatterFiniteCorePointwiseCoordinates_inner_integrable
      period hPeriod first second
  exact hComplex.re.congr <| ae_of_all _ fun base => by
    simp only [programPT05SpinCMatterFiniteCoreIntrinsicPairing,
      real_inner_eq_re_inner]

/-- Integration of the intrinsic core pairing is exactly the real coefficient
Hilbert pairing. -/
theorem programPT05SpinCMatterFiniteCoreIntrinsicPairing_integral
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (∫ base,
      programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        first second base
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      inner Real
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding first)
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding second) := by
  have hComplex :=
    programPT05SpinCMatterFiniteCorePointwiseCoordinates_inner_integrable
      period hPeriod first second
  calc
    (∫ base,
        programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
          first second base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        ∫ base,
          (inner Complex
            (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
              first base)
            (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
              second base)).re
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      apply integral_congr_ae
      exact ae_of_all _ fun base => by
        simp only [programPT05SpinCMatterFiniteCoreIntrinsicPairing,
          real_inner_eq_re_inner]
        rw [RCLike.re_eq_complex_re]
    _ = (∫ base,
          inner Complex
            (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
              first base)
            (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
              second base)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)).re :=
      integral_re hComplex
    _ = (inner Complex
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding first)
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding second)).re :=
      congrArg Complex.re
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates_integral_inner
          period hPeriod first second)
    _ = inner Real
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding first)
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding second) := by
      rw [real_inner_eq_re_inner]
      rw [RCLike.re_eq_complex_re]

/-- L1 class of the intrinsic real pairing on the finite core. -/
def programPT05SpinCMatterFiniteCoreIntrinsicPairingL1
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    SpinCMatterL1 period hPeriod :=
  (programPT05SpinCMatterFiniteCoreIntrinsicPairing_integrable period hPeriod
    first second).toL1
      (programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        first second)

/-- The finite-core L1 pairing has its intrinsic scalar representative almost
everywhere. -/
theorem programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    ⇑(programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
        first second) =ᵐ[intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
        first second :=
  (programPT05SpinCMatterFiniteCoreIntrinsicPairing_integrable period hPeriod
    first second).coeFn_toL1

/-- The intrinsic finite-core pairing packaged as a real bilinear map. -/
def programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
        SpinCMatterL1 period hPeriod :=
  LinearMap.mk₂ Real
    (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod)
    (by
      intro first second third
      apply Lp.ext
      filter_upwards
        [programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod (first + second) third,
         programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod first third,
         programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod second third,
         Lp.coeFn_add
          (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
            first third)
          (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
            second third)]
        with base hSum hFirst hSecond hAdd
      simp only [Pi.add_apply] at hAdd
      rw [hAdd, hSum, hFirst, hSecond]
      exact congrFun
        (programPT05SpinCMatterFiniteCoreIntrinsicPairing_add_left
          period hPeriod first second third) base)
    (by
      intro scalar first second
      apply Lp.ext
      filter_upwards
        [programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod (scalar • first) second,
         programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod first second,
         Lp.coeFn_smul scalar
          (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
            first second)]
        with base hScaled hPair hSmul
      simp only [Pi.smul_apply] at hSmul
      rw [hSmul, hScaled, hPair]
      exact congrFun
        (programPT05SpinCMatterFiniteCoreIntrinsicPairing_smul_left
          period hPeriod scalar first second) base)
    (by
      intro first second third
      apply Lp.ext
      filter_upwards
        [programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod first (second + third),
         programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod first second,
         programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod first third,
         Lp.coeFn_add
          (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
            first second)
          (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
            first third)]
        with base hSum hSecond hThird hAdd
      simp only [Pi.add_apply] at hAdd
      rw [hAdd, hSum, hSecond, hThird]
      exact congrFun
        (programPT05SpinCMatterFiniteCoreIntrinsicPairing_add_right
          period hPeriod first second third) base)
    (by
      intro scalar first second
      apply Lp.ext
      filter_upwards
        [programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod first (scalar • second),
         programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod first second,
         Lp.coeFn_smul scalar
          (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
            first second)]
        with base hScaled hPair hSmul
      simp only [Pi.smul_apply] at hSmul
      rw [hSmul, hScaled, hPair]
      exact congrFun
        (programPT05SpinCMatterFiniteCoreIntrinsicPairing_smul_right
          period hPeriod scalar first second) base)

@[simp]
theorem programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap_apply
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap
        period hPeriod first second =
      programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
        first second :=
  rfl

private def programPT05SpinCMatterFiniteCorePointwiseNorm
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (base : EffectiveThroat period hPeriod) : Real :=
  ‖programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
    coefficients base‖

private theorem programPT05SpinCMatterFiniteCorePointwiseNorm_aestronglyMeasurable
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    AEStronglyMeasurable
      (programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod coefficients)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have hPair :=
    programPT05SpinCMatterFiniteCoreIntrinsicPairing_integrable
      period hPeriod coefficients coefficients
  have hSqrt : AEStronglyMeasurable
      (fun base => Real.sqrt
        (programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
          coefficients coefficients base))
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (hPair.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  refine hSqrt.congr <| ae_of_all _ fun base => ?_
  unfold programPT05SpinCMatterFiniteCoreIntrinsicPairing
    programPT05SpinCMatterFiniteCorePointwiseNorm
  change Real.sqrt
      (inner Real
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          coefficients base)
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          coefficients base)) = _
  rw [real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

private theorem programPT05SpinCMatterFiniteCorePointwiseNorm_memLp
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    MemLp
      (programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod coefficients)
      2 (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  apply (memLp_two_iff_integrable_sq
    (programPT05SpinCMatterFiniteCorePointwiseNorm_aestronglyMeasurable
      period hPeriod coefficients)).2
  exact
    (programPT05SpinCMatterFiniteCoreIntrinsicPairing_integrable
      period hPeriod coefficients coefficients).congr <|
        ae_of_all _ fun base => by
          unfold programPT05SpinCMatterFiniteCoreIntrinsicPairing
            programPT05SpinCMatterFiniteCorePointwiseNorm
          rw [real_inner_self_eq_norm_sq]

private theorem programPT05SpinCMatterFiniteCorePointwiseNorm_integral_sq
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (∫ base,
      programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod
        coefficients base ^ 2
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients‖ ^ 2 := by
  calc
    (∫ base,
        programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod
          coefficients base ^ 2
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        ∫ base,
          programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
            coefficients coefficients base
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      apply integral_congr_ae
      exact ae_of_all _ fun base => by
        unfold programPT05SpinCMatterFiniteCoreIntrinsicPairing
          programPT05SpinCMatterFiniteCorePointwiseNorm
        rw [real_inner_self_eq_norm_sq]
    _ = inner Real
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients)
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients) :=
      programPT05SpinCMatterFiniteCoreIntrinsicPairing_integral
        period hPeriod coefficients coefficients
    _ = ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

/-- Cauchy-Schwarz and the exact geometric core norm give a unit bilinear
bound into L1. -/
theorem programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_norm_le
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    ‖programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
        first second‖ ≤
      ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding first‖ *
        ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding second‖ := by
  have hFirst :=
    programPT05SpinCMatterFiniteCorePointwiseNorm_memLp
      period hPeriod first
  have hSecond :=
    programPT05SpinCMatterFiniteCorePointwiseNorm_memLp
      period hPeriod second
  have hProduct : Integrable
      (programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod first *
        programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod second)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    hFirst.integrable_mul hSecond
  have hSqFirst :
      (∫ base,
        programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod
          first base ^ (2 : Real)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding first‖ ^ 2 := by
    simpa only [Real.rpow_two] using
      programPT05SpinCMatterFiniteCorePointwiseNorm_integral_sq
        period hPeriod first
  have hSqSecond :
      (∫ base,
        programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod
          second base ^ (2 : Real)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding second‖ ^ 2 := by
    simpa only [Real.rpow_two] using
      programPT05SpinCMatterFiniteCorePointwiseNorm_integral_sq
        period hPeriod second
  change ‖(programPT05SpinCMatterFiniteCoreIntrinsicPairing_integrable
      period hPeriod first second).toL1
        (programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
          first second)‖ ≤ _
  rw [L1.norm_of_fun_eq_integral_norm]
  calc
    (∫ base,
        ‖programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
          first second base‖
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) ≤
        ∫ base,
          programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod
              first base *
            programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod
              second base
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      apply integral_mono
      · exact (programPT05SpinCMatterFiniteCoreIntrinsicPairing_integrable
          period hPeriod first second).norm
      · exact hProduct
      · intro base
        unfold programPT05SpinCMatterFiniteCoreIntrinsicPairing
          programPT05SpinCMatterFiniteCorePointwiseNorm
        simpa only [Real.norm_eq_abs] using
          abs_real_inner_le_norm
            (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
              first base)
            (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
              second base)
    _ ≤ (∫ base,
          programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod
            first base ^ (2 : Real)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) ^
          (1 / (2 : Real)) *
        (∫ base,
          programPT05SpinCMatterFiniteCorePointwiseNorm period hPeriod
            second base ^ (2 : Real)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) ^
          (1 / (2 : Real)) := by
      apply integral_mul_le_Lp_mul_Lq_of_nonneg
        (p := (2 : Real)) (q := (2 : Real))
      · rw [Real.holderConjugate_iff]
        norm_num
      · exact Eventually.of_forall fun base => norm_nonneg _
      · exact Eventually.of_forall fun base => norm_nonneg _
      · simpa using hFirst
      · simpa using hSecond
    _ = ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding first‖ *
        ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding second‖ := by
      rw [hSqFirst, hSqSecond,
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
        Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

private theorem programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_fixed_norm_bound
    (first : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    ∃ constant : Real,
      ∀ second : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
        ‖programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap
            period hPeriod first second‖ ≤
          constant *
            ‖programPT05SpinCMatterFiniteHilbertEmbeddingReal second‖ := by
  refine ⟨‖programPT05SpinCMatterFiniteHilbertEmbeddingReal first‖, ?_⟩
  intro second
  exact programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_norm_le
    period hPeriod first second

/-- Extension in the second argument for a finite first coefficient. -/
def programPT05SpinCMatterIntrinsicPairingRightExtension
    (first : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    ProgramPPrimitiveSpinCMatterHilbert →L[Real]
      SpinCMatterL1 period hPeriod :=
  LinearMap.extendOfNorm
    (𝕜 := Real) (𝕜₂ := Real) (σ₁₂ := RingHom.id Real)
    (E := ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (Eₗ := ProgramPPrimitiveSpinCMatterHilbert)
    (F := SpinCMatterL1 period hPeriod)
    (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap
      period hPeriod first)
    programPT05SpinCMatterFiniteHilbertEmbeddingReal

@[simp]
theorem programPT05SpinCMatterIntrinsicPairingRightExtension_core
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterIntrinsicPairingRightExtension period hPeriod first
        (programPT05SpinCMatterFiniteHilbertEmbeddingReal second) =
      programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
        first second := by
  unfold programPT05SpinCMatterIntrinsicPairingRightExtension
  rw [LinearMap.extendOfNorm_eq
    programPT05SpinCMatterFiniteHilbertEmbeddingReal_denseRange
    (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_fixed_norm_bound
      period hPeriod first) second]
  rfl

theorem programPT05SpinCMatterIntrinsicPairingRightExtension_opNorm_le
    (first : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    ‖programPT05SpinCMatterIntrinsicPairingRightExtension
        period hPeriod first‖ ≤
      ‖programPT05SpinCMatterFiniteHilbertEmbeddingReal first‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro state
  change ‖LinearMap.extendOfNorm
      (𝕜 := Real) (𝕜₂ := Real) (σ₁₂ := RingHom.id Real)
      (E := ProgramPPrimitiveSpinCMatterFiniteCoefficients)
      (Eₗ := ProgramPPrimitiveSpinCMatterHilbert)
      (F := SpinCMatterL1 period hPeriod)
      (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap
        period hPeriod first)
      programPT05SpinCMatterFiniteHilbertEmbeddingReal state‖ ≤
    ‖programPT05SpinCMatterFiniteHilbertEmbeddingReal first‖ * ‖state‖
  have hNorm : ∀ second : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      ‖programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap
          period hPeriod first second‖ ≤
        ‖programPT05SpinCMatterFiniteHilbertEmbeddingReal first‖ *
          ‖programPT05SpinCMatterFiniteHilbertEmbeddingReal second‖ := by
    intro second
    exact programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_norm_le
      period hPeriod first second
  exact LinearMap.norm_extendOfNorm_apply_le
    programPT05SpinCMatterFiniteHilbertEmbeddingReal_denseRange
    ‖programPT05SpinCMatterFiniteHilbertEmbeddingReal first‖
    hNorm state

/-- The one-sided extensions depend real-linearly on the finite first
coefficient. -/
def programPT05SpinCMatterIntrinsicPairingLeftLinearMap :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      (ProgramPPrimitiveSpinCMatterHilbert →L[Real]
        SpinCMatterL1 period hPeriod) where
  toFun := programPT05SpinCMatterIntrinsicPairingRightExtension period hPeriod
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro state
    refine DenseRange.induction_on
      programPT05SpinCMatterFiniteHilbertEmbeddingReal_denseRange state
      (isClosed_eq
        (programPT05SpinCMatterIntrinsicPairingRightExtension
          period hPeriod (first + second)).continuous
        ((programPT05SpinCMatterIntrinsicPairingRightExtension
            period hPeriod first +
          programPT05SpinCMatterIntrinsicPairingRightExtension
            period hPeriod second).continuous)) ?_
    intro core
    simp only [add_apply,
      programPT05SpinCMatterIntrinsicPairingRightExtension_core]
    have hAdd := congrArg
      (fun linear => linear core)
      ((programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap
        period hPeriod).map_add first second)
    simpa only [LinearMap.add_apply,
      programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap_apply]
      using hAdd
  map_smul' scalar first := by
    apply ContinuousLinearMap.ext
    intro state
    refine DenseRange.induction_on
      programPT05SpinCMatterFiniteHilbertEmbeddingReal_denseRange state
      (isClosed_eq
        (programPT05SpinCMatterIntrinsicPairingRightExtension
          period hPeriod (scalar • first)).continuous
        ((scalar • programPT05SpinCMatterIntrinsicPairingRightExtension
          period hPeriod first).continuous)) ?_
    intro core
    simp only [smul_apply,
      programPT05SpinCMatterIntrinsicPairingRightExtension_core]
    have hSmul := congrArg
      (fun linear => linear core)
      ((programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap
        period hPeriod).map_smul scalar first)
    simpa only [LinearMap.smul_apply, RingHom.id_apply,
      programPT05SpinCMatterFiniteCoreIntrinsicPairingL1LinearMap_apply]
      using hSmul

private theorem programPT05SpinCMatterIntrinsicPairingLeftLinearMap_norm_bound :
    ∃ constant : Real,
      ∀ first : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
        ‖programPT05SpinCMatterIntrinsicPairingLeftLinearMap
            period hPeriod first‖ ≤
          constant *
            ‖programPT05SpinCMatterFiniteHilbertEmbeddingReal first‖ := by
  refine ⟨1, ?_⟩
  intro first
  change ‖programPT05SpinCMatterIntrinsicPairingRightExtension
      period hPeriod first‖ ≤
    1 * ‖programPT05SpinCMatterFiniteHilbertEmbeddingReal first‖
  rw [one_mul]
  exact programPT05SpinCMatterIntrinsicPairingRightExtension_opNorm_le
    period hPeriod first

/-- Canonical scalar L1 pairing on the completed SpinC Hilbert space. -/
def programPT05SpinCMatterMaximalIntrinsicPairingL1 :
    ProgramPPrimitiveSpinCMatterHilbert →L[Real]
      (ProgramPPrimitiveSpinCMatterHilbert →L[Real]
        SpinCMatterL1 period hPeriod) :=
  LinearMap.extendOfNorm
    (𝕜 := Real) (𝕜₂ := Real) (σ₁₂ := RingHom.id Real)
    (E := ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (Eₗ := ProgramPPrimitiveSpinCMatterHilbert)
    (F := ProgramPPrimitiveSpinCMatterHilbert →L[Real]
      SpinCMatterL1 period hPeriod)
    (programPT05SpinCMatterIntrinsicPairingLeftLinearMap period hPeriod)
    programPT05SpinCMatterFiniteHilbertEmbeddingReal

@[simp]
theorem programPT05SpinCMatterMaximalIntrinsicPairingL1_core_left
    (first : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterMaximalIntrinsicPairingL1 period hPeriod
        (programPT05SpinCMatterFiniteHilbertEmbeddingReal first) =
      programPT05SpinCMatterIntrinsicPairingRightExtension
        period hPeriod first := by
  unfold programPT05SpinCMatterMaximalIntrinsicPairingL1
  rw [LinearMap.extendOfNorm_eq
    programPT05SpinCMatterFiniteHilbertEmbeddingReal_denseRange
    (programPT05SpinCMatterIntrinsicPairingLeftLinearMap_norm_bound
      period hPeriod) first]
  rfl

@[simp]
theorem programPT05SpinCMatterMaximalIntrinsicPairingL1_core
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterMaximalIntrinsicPairingL1 period hPeriod
        (programPT05SpinCMatterFiniteHilbertEmbeddingReal first)
        (programPT05SpinCMatterFiniteHilbertEmbeddingReal second) =
      programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
        first second := by
  rw [programPT05SpinCMatterMaximalIntrinsicPairingL1_core_left,
    programPT05SpinCMatterIntrinsicPairingRightExtension_core]

private theorem programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_integral
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    L1.integralCLM
        (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
          first second) =
      inner Real
        (programPT05SpinCMatterFiniteHilbertEmbeddingReal first)
        (programPT05SpinCMatterFiniteHilbertEmbeddingReal second) := by
  calc
    L1.integralCLM
        (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
          first second) =
        L1.integral
          (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
            first second) :=
      (L1.integral_eq _).symm
    _ = ∫ base,
        programPT05SpinCMatterFiniteCoreIntrinsicPairingL1 period hPeriod
          first second base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
      L1.integral_eq_integral _
    _ = ∫ base,
        programPT05SpinCMatterFiniteCoreIntrinsicPairing period hPeriod
          first second base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      exact integral_congr_ae
        (programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_coeFn
          period hPeriod first second)
    _ = inner Real
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding first)
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding second) :=
      programPT05SpinCMatterFiniteCoreIntrinsicPairing_integral
        period hPeriod first second
    _ = inner Real
        (programPT05SpinCMatterFiniteHilbertEmbeddingReal first)
        (programPT05SpinCMatterFiniteHilbertEmbeddingReal second) :=
      rfl

/-- The integral of the completed intrinsic L1 pairing is the Hilbert inner
product for all completed states. -/
theorem programPT05SpinCMatterMaximalIntrinsicPairingL1_integral
    (first second : ProgramPPrimitiveSpinCMatterHilbert) :
    L1.integralCLM
        (programPT05SpinCMatterMaximalIntrinsicPairingL1 period hPeriod
          first second) =
      inner Real first second := by
  let pairing := programPT05SpinCMatterMaximalIntrinsicPairingL1
    period hPeriod
  let integralMap :=
    L1.integralCLM
      (α := EffectiveThroat period hPeriod) (E := Real)
      (μ := intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  let embedding := programPT05SpinCMatterFiniteHilbertEmbeddingReal
  have hDense : DenseRange
      (embedding : ProgramPPrimitiveSpinCMatterFiniteCoefficients →
        ProgramPPrimitiveSpinCMatterHilbert) :=
    programPT05SpinCMatterFiniteHilbertEmbeddingReal_denseRange
  refine DenseRange.induction_on hDense first
    (isClosed_eq
      ((integralMap.comp (pairing.flip second)).continuous)
      (((innerSL Real).flip second).continuous)) ?_
  intro coreFirst
  refine DenseRange.induction_on hDense second
    (isClosed_eq
      ((integralMap.comp (pairing (embedding coreFirst))).continuous)
      ((innerSL Real (embedding coreFirst)).continuous)) ?_
  intro coreSecond
  change L1.integralCLM
      (programPT05SpinCMatterMaximalIntrinsicPairingL1 period hPeriod
        (programPT05SpinCMatterFiniteHilbertEmbeddingReal coreFirst)
        (programPT05SpinCMatterFiniteHilbertEmbeddingReal coreSecond)) = _
  rw [programPT05SpinCMatterMaximalIntrinsicPairingL1_core]
  exact programPT05SpinCMatterFiniteCoreIntrinsicPairingL1_integral
    period hPeriod coreFirst coreSecond

/-- Maximal intrinsic spacetime density of a SpinC graph state. -/
def programPT05SpinCMatterMaximalIntrinsicLocalDensityL1
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) : SpinCMatterL1 period hPeriod :=
  (1 / 2 : Real) •
    programPT05SpinCMatterMaximalIntrinsicPairingL1 period hPeriod
      state.1.1 state.1.2

/-- The maximal intrinsic L1 density integrates to the exact graph action. -/
theorem programPT05SpinCMatterMaximalIntrinsicLocalDensityL1_integral_eq_graphAction
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    (∫ base,
      programPT05SpinCMatterMaximalIntrinsicLocalDensityL1
        period hPeriod massSquared state base
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        state := by
  let density := programPT05SpinCMatterMaximalIntrinsicLocalDensityL1
    period hPeriod massSquared state
  calc
    (∫ base, density base
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        L1.integral density :=
      (L1.integral_eq_integral density).symm
    _ = L1.integralCLM density :=
      L1.integral_eq density
    _ = (1 / 2 : Real) *
        L1.integralCLM
          (programPT05SpinCMatterMaximalIntrinsicPairingL1 period hPeriod
            state.1.1 state.1.2) := by
      simp only [density,
        programPT05SpinCMatterMaximalIntrinsicLocalDensityL1, map_smul,
        smul_eq_mul]
    _ = (1 / 2 : Real) * inner Real state.1.1 state.1.2 := by
      rw [programPT05SpinCMatterMaximalIntrinsicPairingL1_integral]
    _ = programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        state := by
      rw [programPPrimitiveSpinCMatterGraphAction,
        programPPrimitiveSpinCMatterGraphForm_apply]

/-- Every Gate-828 SpinC frontier now carries an intrinsic L1 density. -/
def ProgramPT05BulkSpinCLocalDensityFrontier.intrinsicDensityL1
    (couplings : GlobalCandidateAActionCouplings)
    (frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      couplings.matterMassSquared) : SpinCMatterL1 period hPeriod :=
  programPT05SpinCMatterMaximalIntrinsicLocalDensityL1 period hPeriod
    couplings.matterMassSquared frontier.graphState

/-- The intrinsic frontier density has exactly the action used at Gate 828. -/
theorem ProgramPT05BulkSpinCLocalDensityFrontier.integral_intrinsicDensityL1
    (couplings : GlobalCandidateAActionCouplings)
    (frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      couplings.matterMassSquared) :
    (∫ base,
      ProgramPT05BulkSpinCLocalDensityFrontier.intrinsicDensityL1
        period hPeriod couplings frontier base
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      programPT05BulkSpinCFrontierAction period hPeriod couplings frontier := by
  unfold ProgramPT05BulkSpinCLocalDensityFrontier.intrinsicDensityL1
    programPT05BulkSpinCFrontierAction
  exact
    programPT05SpinCMatterMaximalIntrinsicLocalDensityL1_integral_eq_graphAction
      period hPeriod couplings.matterMassSquared frontier.graphState

end
end P0EFTJanusProgramPT05SpinCMatterIntrinsicL1Completion4D
end JanusFormal
