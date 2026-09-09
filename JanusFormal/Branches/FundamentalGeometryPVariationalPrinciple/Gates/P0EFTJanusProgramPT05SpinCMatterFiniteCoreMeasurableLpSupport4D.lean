import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterFiniteCoreLpExtensionSupport4D

/-!
# T05 measurable finite-core SpinC realization

The finite smooth SpinC core already has the exact geometric `L²` norm of
its signed-mode coefficients.  The only datum missing from the current bundle
API is strong measurability of its values in one fixed global coordinate
fiber.  From that datum this module constructs the finite-core `Lp` map,
proves complex linearity and exact norm preservation, and supplies Gate 845's
finite-core support.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05SpinCMatterFiniteCoreMeasurableLpSupport4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal lp
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorPairingSmooth4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT05SpinCMatterMaximalLpDensityBridge4D
open P0EFTJanusProgramPT05SpinCMatterFiniteCoreLpExtensionSupport4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance spinCMatterFiniteCoreMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance spinCMatterFiniteCoreBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance spinCMatterFiniteCoreFiniteMeasure :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- The smallest missing analytic input: fixed-fiber coordinates of every
finite smooth synthesis are strongly measurable almost everywhere. -/
structure ProgramPT05SpinCMatterFiniteCoreCoordinateMeasurability where
  aestronglyMeasurable :
    ∀ coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      AEStronglyMeasurable
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          coefficients)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

private theorem programPT05SpinCMatterPointwiseCoordinates_add
    (first second : Sector → D9DoubledMatterFiber) :
    programPT05SpinCMatterPointwiseCoordinates
        (fun sector => first sector + second sector) =
      programPT05SpinCMatterPointwiseCoordinates first +
        programPT05SpinCMatterPointwiseCoordinates second := by
  classical
  apply PiLp.ext
  intro index
  have hAdd :
      d9DoubledMatterFiberHalfSpinorLinearEquiv
          (first index.1 + second index.1) =
        d9DoubledMatterFiberHalfSpinorLinearEquiv (first index.1) +
          d9DoubledMatterFiberHalfSpinorLinearEquiv (second index.1) :=
    map_add d9DoubledMatterFiberHalfSpinorLinearEquiv _ _
  by_cases hComponent : index.2.1 = (0 : Fin 2)
  · simpa [programPT05SpinCMatterPointwiseCoordinates, hComponent,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_apply] using
      congrFun (congrArg Prod.fst hAdd) index.2.2
  · simpa [programPT05SpinCMatterPointwiseCoordinates, hComponent,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_apply] using
      congrFun (congrArg Prod.snd hAdd) index.2.2

private theorem programPT05SpinCMatterPointwiseCoordinates_complexAction
    (scalar : Complex) (field : Sector → D9DoubledMatterFiber) :
    programPT05SpinCMatterPointwiseCoordinates
        (fun sector => d9PrimitiveSpinCComplexActionCLM scalar (field sector)) =
      scalar • programPT05SpinCMatterPointwiseCoordinates field := by
  classical
  apply PiLp.ext
  intro index
  have hAction :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction
      scalar (field index.1)
  by_cases hComponent : index.2.1 = (0 : Fin 2)
  · simpa [programPT05SpinCMatterPointwiseCoordinates, hComponent,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_apply] using
      congrFun (congrArg Prod.fst hAction) index.2.2
  · simpa [programPT05SpinCMatterPointwiseCoordinates, hComponent,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_apply] using
      congrFun (congrArg Prod.snd hAction) index.2.2

private theorem programPT05SpinCMatterFiniteCorePointwiseCoordinates_add_apply
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (base : EffectiveThroat period hPeriod) :
    programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        (first + second) base =
      programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          first base +
        programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          second base := by
  have hSynthesis := map_add
    (programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap
      period hPeriod) first second
  have hField :
      (fun sector =>
        show D9DoubledMatterFiber from
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            (first + second) sector base) =
        fun sector =>
          (show D9DoubledMatterFiber from
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              first sector base) +
          (show D9DoubledMatterFiber from
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              second sector base) := by
    funext sector
    exact congrArg
      (fun state => show D9DoubledMatterFiber from state base)
      (congrFun hSynthesis sector)
  change
    programPT05SpinCMatterPointwiseCoordinates
        (fun sector =>
          show D9DoubledMatterFiber from
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              (first + second) sector base) = _
  rw [hField]
  exact programPT05SpinCMatterPointwiseCoordinates_add _ _

private theorem programPT05SpinCMatterFiniteCorePointwiseCoordinates_smul_apply
    (scalar : Complex)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (base : EffectiveThroat period hPeriod) :
    programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        (scalar • coefficients) base =
      scalar •
        programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          coefficients base := by
  have hSynthesis := map_smul
    (programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap
      period hPeriod) scalar coefficients
  have hField :
      (fun sector =>
        show D9DoubledMatterFiber from
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            (scalar • coefficients) sector base) =
        fun sector =>
          d9PrimitiveSpinCComplexActionCLM scalar
            (show D9DoubledMatterFiber from
              programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
                coefficients sector base) := by
    funext sector
    have hEval :
        (show D9DoubledMatterFiber from
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            (scalar • coefficients) sector base) =
          (scalar •
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              coefficients sector) base := by
      exact congrArg
        (fun state => show D9DoubledMatterFiber from state base)
        (congrFun hSynthesis sector)
    rw [hEval]
    change d9PrimitiveSpinCComplexScalarSection
        period hPeriod .positiveQuarter scalar
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
          coefficients sector) base = _
    exact d9PrimitiveSpinCComplexScalarSection_apply_complexAction
      period hPeriod .positiveQuarter scalar
      (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        coefficients sector) base
  change
    programPT05SpinCMatterPointwiseCoordinates
        (fun sector =>
          show D9DoubledMatterFiber from
            programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              (scalar • coefficients) sector base) = _
  rw [hField]
  exact programPT05SpinCMatterPointwiseCoordinates_complexAction _ _

private def primitiveSpinCFiniteCoefficientEmbedding :
    PrimitiveSpinCGeometricSignedFiniteCoefficients →ₗ[Complex]
      ComplexDiagonalHilbert PrimitiveSpinCGeometricSignedMode :=
  Finsupp.linearCombination Complex
    (complexDiagonalBasis PrimitiveSpinCGeometricSignedMode)

@[simp]
private theorem primitiveSpinCFiniteCoefficientEmbedding_single
    (mode : PrimitiveSpinCGeometricSignedMode) (coefficient : Complex) :
    primitiveSpinCFiniteCoefficientEmbedding
        (Finsupp.single mode coefficient) =
      lp.single 2 mode coefficient := by
  rw [primitiveSpinCFiniteCoefficientEmbedding,
    Finsupp.linearCombination_single, complexDiagonalBasis_eq_single]
  ext other
  by_cases hOther : other = mode
  · subst other
    simp [lp.single_apply]
  · simp [lp.single_apply, hOther]

@[simp]
private theorem primitiveSpinCFiniteCoefficientEmbedding_apply
    (coefficients : PrimitiveSpinCGeometricSignedFiniteCoefficients)
    (mode : PrimitiveSpinCGeometricSignedMode) :
    primitiveSpinCFiniteCoefficientEmbedding coefficients mode =
      coefficients mode := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [primitiveSpinCFiniteCoefficientEmbedding]
  | single_add other coefficient rest _ _ inductionHypothesis =>
      rw [map_add]
      change
        primitiveSpinCFiniteCoefficientEmbedding
              (Finsupp.single other coefficient) mode +
            primitiveSpinCFiniteCoefficientEmbedding rest mode =
          Finsupp.single other coefficient mode + rest mode
      rw [primitiveSpinCFiniteCoefficientEmbedding_single,
        inductionHypothesis]
      by_cases hMode : other = mode
      · subst other
        simp [lp.single_apply]
      · simp [lp.single_apply, hMode]

private theorem primitiveSpinCFiniteSynthesis_embedding
    (coefficients : PrimitiveSpinCGeometricSignedFiniteCoefficients) :
    d9PrimitiveSpinCGeometricL2Embedding
        period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod coefficients) =
      primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod
        (primitiveSpinCFiniteCoefficientEmbedding coefficients) := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp
  | single_add mode coefficient rest _ _ inductionHypothesis =>
      rw [map_add, map_add, map_add, map_add, inductionHypothesis,
        primitiveSpinCFiniteCoefficientEmbedding_single,
        primitiveSpinCGeometricSignedDiracFiniteSynthesis_single]
      congr 1
      calc
        d9PrimitiveSpinCGeometricL2Embedding
            period hPeriod .positiveQuarter
            (coefficient •
              primitiveSpinCGeometricSignedDiracModeSmoothVector
                period hPeriod mode) =
            coefficient •
              d9PrimitiveSpinCGeometricL2Embedding
                period hPeriod .positiveQuarter
                (primitiveSpinCGeometricSignedDiracModeSmoothVector
                  period hPeriod mode) := by
          exact map_smul
            (d9PrimitiveSpinCGeometricL2Embedding
              period hPeriod .positiveQuarter) coefficient _
        _ = coefficient •
            primitiveSpinCGeometricSignedDiracModeVector
              period hPeriod mode := rfl
        _ = primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod
            (lp.single 2 mode coefficient) :=
          (primitiveSpinCGeometricSignedDiracModeUnitary_single
            period hPeriod mode coefficient).symm

private theorem primitiveSpinCFiniteSynthesis_pairing_eq_inner
    (first second : PrimitiveSpinCGeometricSignedFiniteCoefficients) :
    d9PrimitiveSpinCGeometricL2Pairing period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod first)
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod second) =
      inner Complex
        (primitiveSpinCFiniteCoefficientEmbedding first)
        (primitiveSpinCFiniteCoefficientEmbedding second) := by
  change inner Complex
      (primitiveSpinCGeometricSignedDiracFiniteSynthesis
        period hPeriod first)
      (primitiveSpinCGeometricSignedDiracFiniteSynthesis
        period hPeriod second) = _
  rw [← UniformSpace.Completion.inner_coe]
  change inner Complex
      (d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod first))
      (d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis
          period hPeriod second)) = _
  rw [primitiveSpinCFiniteSynthesis_embedding,
    primitiveSpinCFiniteSynthesis_embedding,
    LinearIsometryEquiv.inner_map_map]

private theorem tsum_prod_eq_sum
    {Outer Inner : Type*} [Fintype Outer]
    (f : Outer × Inner → Complex) (hf : Summable f) :
    (∑' mode, f mode) = ∑ outer, ∑' innerMode, f (outer, innerMode) := by
  rw [hf.tsum_prod, tsum_fintype]

private theorem product_inner_eq_sum
    {Outer Inner : Type*} [Fintype Outer]
    (first second : lp (fun _ : Outer × Inner => Complex) 2) :
    inner Complex first second =
      ∑ outer : Outer, ∑' innerMode : Inner,
        inner Complex (first (outer, innerMode))
          (second (outer, innerMode)) := by
  calc
    inner Complex first second =
        ∑' mode, inner Complex (first mode) (second mode) :=
      lp.inner_eq_tsum first second
    _ = ∑ outer : Outer, ∑' innerMode : Inner,
          inner Complex (first (outer, innerMode))
            (second (outer, innerMode)) :=
      tsum_prod_eq_sum _ (lp.summable_inner first second)

private theorem programPT05SpinCMatterFiniteCorePointwiseCoordinates_inner
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients)
    (base : EffectiveThroat period hPeriod) :
    inner Complex
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          first base)
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          second base) =
      ∑ sector : Sector,
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            first sector)
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            second sector) base := by
  change inner Complex
      (programPT05SpinCMatterPointwiseCoordinates fun sector =>
        show D9DoubledMatterFiber from
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            first sector base)
      (programPT05SpinCMatterPointwiseCoordinates fun sector =>
        show D9DoubledMatterFiber from
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            second sector base) =
    ∑ sector : Sector,
      d9DoubledMatterSpinorHermitianPairing
        (show D9DoubledMatterFiber from
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            first sector base)
        (show D9DoubledMatterFiber from
          programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            second sector base)
  exact programPT05SpinCMatterPointwiseCoordinates_inner _ _

/-- The fixed-coordinate pairing of two finite syntheses is integrable. -/
theorem programPT05SpinCMatterFiniteCorePointwiseCoordinates_inner_integrable
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    Integrable
      (fun base => inner Complex
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          first base)
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          second base))
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [show
    (fun base => inner Complex
      (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        first base)
      (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        second base)) =
      fun base => ∑ sector : Sector,
        d9PrimitiveSpinCPointwiseHermitianPairing
          period hPeriod .positiveQuarter
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            first sector)
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            second sector) base by
    funext base
    exact programPT05SpinCMatterFiniteCorePointwiseCoordinates_inner
      period hPeriod first second base]
  exact integrable_finsetSum _ fun sector _ =>
    d9PrimitiveSpinCPointwiseHermitianPairing_integrable
      period hPeriod .positiveQuarter
      (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        first sector)
      (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        second sector)

/-- The integrated fixed-coordinate pairing is exactly the signed-mode
Hilbert pairing. -/
theorem programPT05SpinCMatterFiniteCorePointwiseCoordinates_integral_inner
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (∫ base, inner Complex
      (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        first base)
      (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        second base)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      inner Complex
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding first)
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding second) := by
  calc
    (∫ base, inner Complex
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          first base)
        (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          second base)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        ∫ base, ∑ sector : Sector,
          d9PrimitiveSpinCPointwiseHermitianPairing
            period hPeriod .positiveQuarter
            (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              first sector)
            (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              second sector) base
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      apply integral_congr_ae
      exact ae_of_all _ fun base =>
        programPT05SpinCMatterFiniteCorePointwiseCoordinates_inner
          period hPeriod first second base
    _ = ∑ sector : Sector,
        d9PrimitiveSpinCGeometricL2Pairing
          period hPeriod .positiveQuarter
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            first sector)
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            second sector) := by
      rw [integral_finsetSum Finset.univ]
      · rfl
      · intro sector _
        exact d9PrimitiveSpinCPointwiseHermitianPairing_integrable
          period hPeriod .positiveQuarter
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            first sector)
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            second sector)
    _ = ∑ sector : Sector,
        inner Complex
          (primitiveSpinCFiniteCoefficientEmbedding (first.curry sector))
          (primitiveSpinCFiniteCoefficientEmbedding
            (second.curry sector)) := by
      apply Finset.sum_congr rfl
      intro sector _
      exact primitiveSpinCFiniteSynthesis_pairing_eq_inner
        period hPeriod (first.curry sector) (second.curry sector)
    _ = inner Complex
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding first)
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding second) := by
      rw [product_inner_eq_sum]
      apply Finset.sum_congr rfl
      intro sector _
      rw [lp.inner_eq_tsum]
      simp_rw [primitiveSpinCFiniteCoefficientEmbedding_apply,
        programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply]
      apply tsum_congr
      intro mode
      rfl

private theorem programPT05SpinCMatterFiniteCorePointwiseCoordinates_normSq_integrable
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    Integrable
      (fun base =>
        ‖programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          coefficients base‖ ^ 2)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have hPair :=
    programPT05SpinCMatterFiniteCorePointwiseCoordinates_inner_integrable
      period hPeriod coefficients coefficients
  exact hPair.re.congr <| ae_of_all _ fun base =>
    (norm_sq_eq_re_inner (𝕜 := Complex)
      (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        coefficients base)).symm

/-- Measurability plus the already proved geometric pairing puts every finite
synthesis in fixed-fiber `L²`. -/
theorem programPT05SpinCMatterFiniteCorePointwiseCoordinates_memLp
    (measurability :
      ProgramPT05SpinCMatterFiniteCoreCoordinateMeasurability period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    MemLp
      (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        coefficients)
      2 (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (memLp_two_iff_integrable_sq_norm
    (measurability.aestronglyMeasurable coefficients)).2
      (programPT05SpinCMatterFiniteCorePointwiseCoordinates_normSq_integrable
        period hPeriod coefficients)

/-- Canonical `Lp` class of a finite smooth synthesis. -/
def programPT05SpinCMatterFiniteCoreToLp
    (measurability :
      ProgramPT05SpinCMatterFiniteCoreCoordinateMeasurability period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    Lp ProgramPT05SpinCMatterPointwiseFiber 2
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (programPT05SpinCMatterFiniteCorePointwiseCoordinates_memLp
    period hPeriod measurability coefficients).toLp
      (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
        coefficients)

/-- The finite-core `Lp` realization is complex-linear. -/
def programPT05SpinCMatterFiniteCoreToLpLinearMap
    (measurability :
      ProgramPT05SpinCMatterFiniteCoreCoordinateMeasurability period hPeriod) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Complex]
      Lp ProgramPT05SpinCMatterPointwiseFiber 2
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) where
  toFun := programPT05SpinCMatterFiniteCoreToLp period hPeriod measurability
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [(programPT05SpinCMatterFiniteCorePointwiseCoordinates_memLp
          period hPeriod measurability (first + second)).coeFn_toLp,
       (programPT05SpinCMatterFiniteCorePointwiseCoordinates_memLp
          period hPeriod measurability first).coeFn_toLp,
       (programPT05SpinCMatterFiniteCorePointwiseCoordinates_memLp
          period hPeriod measurability second).coeFn_toLp,
       Lp.coeFn_add
        (programPT05SpinCMatterFiniteCoreToLp period hPeriod measurability first)
        (programPT05SpinCMatterFiniteCoreToLp period hPeriod measurability
          second)]
      with base hSum hFirst hSecond hAdd
    simp only [Pi.add_apply] at hAdd
    rw [hAdd]
    unfold programPT05SpinCMatterFiniteCoreToLp
    rw [hSum, hFirst, hSecond]
    exact programPT05SpinCMatterFiniteCorePointwiseCoordinates_add_apply
      period hPeriod first second base
  map_smul' scalar coefficients := by
    apply Lp.ext
    filter_upwards
      [(programPT05SpinCMatterFiniteCorePointwiseCoordinates_memLp
          period hPeriod measurability (scalar • coefficients)).coeFn_toLp,
       (programPT05SpinCMatterFiniteCorePointwiseCoordinates_memLp
          period hPeriod measurability coefficients).coeFn_toLp,
       Lp.coeFn_smul scalar
        (programPT05SpinCMatterFiniteCoreToLp period hPeriod measurability
          coefficients)]
      with base hScaled hCoefficients hSmul
    simp only [Pi.smul_apply] at hSmul
    simp only [RingHom.id_apply]
    rw [hSmul]
    unfold programPT05SpinCMatterFiniteCoreToLp
    rw [hScaled, hCoefficients]
    exact programPT05SpinCMatterFiniteCorePointwiseCoordinates_smul_apply
      period hPeriod scalar coefficients base

/-- The `Lp` class uses the requested fixed-coordinate representative. -/
theorem programPT05SpinCMatterFiniteCoreToLpLinearMap_ae
    (measurability :
      ProgramPT05SpinCMatterFiniteCoreCoordinateMeasurability period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    ⇑(programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
        measurability coefficients) =ᵐ[
      intrinsicCanonicalThroatVolumeMeasure period hPeriod]
        programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
          coefficients :=
  (programPT05SpinCMatterFiniteCorePointwiseCoordinates_memLp
    period hPeriod measurability coefficients).coeFn_toLp

/-- The `Lp` pairing agrees with the canonical coefficient pairing. -/
theorem programPT05SpinCMatterFiniteCoreToLpLinearMap_inner
    (measurability :
      ProgramPT05SpinCMatterFiniteCoreCoordinateMeasurability period hPeriod)
    (first second : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    inner Complex
        (programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
          measurability first)
        (programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
          measurability second) =
      inner Complex
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding first)
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding second) := by
  rw [L2.inner_def]
  calc
    (∫ base, inner Complex
        (programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
          measurability first base)
        (programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
          measurability second base)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        ∫ base, inner Complex
          (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
            first base)
          (programPT05SpinCMatterFiniteCorePointwiseCoordinates period hPeriod
            second base)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      apply integral_congr_ae
      filter_upwards
        [programPT05SpinCMatterFiniteCoreToLpLinearMap_ae
          period hPeriod measurability first,
         programPT05SpinCMatterFiniteCoreToLpLinearMap_ae
          period hPeriod measurability second]
        with base hFirst hSecond
      rw [hFirst, hSecond]
    _ = _ :=
      programPT05SpinCMatterFiniteCorePointwiseCoordinates_integral_inner
        period hPeriod first second

/-- The finite-core realization preserves the exact signed-mode norm. -/
theorem programPT05SpinCMatterFiniteCoreToLpLinearMap_norm
    (measurability :
      ProgramPT05SpinCMatterFiniteCoreCoordinateMeasurability period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    ‖programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
        measurability coefficients‖ =
      ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients‖ := by
  have hSquare :
      ‖programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
          measurability coefficients‖ ^ 2 =
        ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients‖ ^ 2 := by
    calc
      ‖programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
          measurability coefficients‖ ^ 2 =
          (inner Complex
            (programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
              measurability coefficients)
            (programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
              measurability coefficients)).re :=
        norm_sq_eq_re_inner (𝕜 := Complex) _
      _ = (inner Complex
          (programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients)
          (programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients)).re :=
        congrArg Complex.re
          (programPT05SpinCMatterFiniteCoreToLpLinearMap_inner
            period hPeriod measurability coefficients coefficients)
      _ = ‖programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients‖ ^ 2 :=
        (norm_sq_eq_re_inner (𝕜 := Complex) _).symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hSquare

/-- The sole coordinate-measurability input supplies all of Gate 845's
finite-core `Lp` support. -/
def ProgramPT05SpinCMatterFiniteCoreCoordinateMeasurability.toFiniteCoreLpSupport
    (measurability :
      ProgramPT05SpinCMatterFiniteCoreCoordinateMeasurability period hPeriod) :
    ProgramPT05SpinCMatterFiniteCoreLpSupport period hPeriod where
  coreToLp :=
    programPT05SpinCMatterFiniteCoreToLpLinearMap period hPeriod
      measurability
  norm_eq :=
    programPT05SpinCMatterFiniteCoreToLpLinearMap_norm period hPeriod
      measurability
  coeFn_ae :=
    programPT05SpinCMatterFiniteCoreToLpLinearMap_ae period hPeriod
      measurability

end
end P0EFTJanusProgramPT05SpinCMatterFiniteCoreMeasurableLpSupport4D
end JanusFormal
