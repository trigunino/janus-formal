import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinHalfPlaneIntegrability4D

/-!
# Mellin germs of the reduced-sphere integrable remainders

The counterterm-subtracted short integral and the exponentially decreasing
long integral are continuous at the Mellin origin.  Consequently their
product with reciprocal Gamma has derivative at zero equal to their value at
zero.  No analytic continuation of the spectral series is assumed here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereMellinRemainderGerm4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D
open P0EFTJanusProgramPProductThroatSphereMellinHalfPlaneIntegrability4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-- The short-time Mellin integral after subtraction of all three local heat
coefficients. -/
def reducedSphereMellinShortRemainderIntegral
    (data : ProductThroatSpectralData) (spectral : Complex) : Complex :=
  ∫ time in Set.Ioc (0 : Real) 1,
    (time : Complex) ^ spectral *
      (((positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time -
        reducedSphereCounterterm data time) / time : Real) : Complex)

/-- The Mellin integral of the reduced heat-trace tail, written as `t^s`
times the logarithmic heat integrand. -/
def reducedSphereMellinLongTailIntegral
    (data : ProductThroatSpectralData) (spectral : Complex) : Complex :=
  ∫ time in Set.Ioi (1 : Real),
    (time : Complex) ^ spectral *
      ((positiveTimeTraceExtension
        (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex)

/-- Integrable short-time envelope valid for `‖s‖ < 1/2`. -/
def reducedSphereMellinShortGermMajorant
    (data : ProductThroatSpectralData) (time : Real) : Real :=
  time ^ (-(1 : Real) / 2) * sphereShortTimeMajorant data time

/-- Integrable long-time envelope valid for `‖s‖ < 1/2`. -/
def reducedSphereMellinLongGermMajorant
    (data : ProductThroatSpectralData) (time : Real) : Real :=
  time ^ ((1 : Real) / 2) *
    longTimeExponentialBound (reducedSphereLongTimeScale data)
      ((1 : Real) / 2) time

private theorem shortGermPower_integrableOn :
    IntegrableOn (fun time : Real => time ^ (-(1 : Real) / 2))
      (Set.Ioc (0 : Real) 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : Real) < 1)]
  norm_num

theorem reducedSphereMellinShortGermMajorant_integrableOn
    (data : ProductThroatSpectralData) :
    IntegrableOn (reducedSphereMellinShortGermMajorant data)
      (Set.Ioc (0 : Real) 1) := by
  unfold reducedSphereMellinShortGermMajorant
  exact shortGermPower_integrableOn.mul_continuousOn_of_subset
    (show ContinuousOn (sphereShortTimeMajorant data)
        (Set.Icc (0 : Real) 1) by
      exact (show Continuous (sphereShortTimeMajorant data) by
        unfold sphereShortTimeMajorant
        fun_prop).continuousOn)
    measurableSet_Ioc isCompact_Icc Set.Ioc_subset_Icc_self

theorem reducedSphereMellinLongGermMajorant_integrableOn
    (data : ProductThroatSpectralData) :
    IntegrableOn (reducedSphereMellinLongGermMajorant data)
      (Set.Ioi (1 : Real)) := by
  have hBase : IntegrableOn
      (fun time : Real =>
        time ^ ((1 : Real) / 2) * Real.exp (-((1 : Real) / 2) * time))
      (Set.Ioi (0 : Real)) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (1 : Real) / 2) (p := (1 : Real)) (b := (1 : Real) / 2)
        (by norm_num) (by norm_num) (by norm_num))
  unfold reducedSphereMellinLongGermMajorant longTimeExponentialBound
  have hScaled := IntegrableOn.mono_set
    (hBase.const_mul (reducedSphereLongTimeScale data))
    (show Set.Ioi (1 : Real) ⊆ Set.Ioi 0 by
      intro time hTime
      exact (by norm_num : (0 : Real) < 1).trans hTime)
  refine hScaled.congr ?_
  filter_upwards with time
  ring

private theorem spectral_re_lower_of_mem_halfBall
    {spectral : Complex} (hSpectral : spectral ∈ Metric.ball 0 ((1 : Real) / 2)) :
    -(1 : Real) / 2 ≤ spectral.re := by
  have hNorm : ‖spectral‖ < (1 : Real) / 2 := by
    simpa [Metric.mem_ball, dist_zero_right] using hSpectral
  have hAbs := Complex.abs_re_le_norm spectral
  linarith [neg_le_abs spectral.re]

private theorem spectral_re_upper_of_mem_halfBall
    {spectral : Complex} (hSpectral : spectral ∈ Metric.ball 0 ((1 : Real) / 2)) :
    spectral.re ≤ (1 : Real) / 2 := by
  have hNorm : ‖spectral‖ < (1 : Real) / 2 := by
    simpa [Metric.mem_ball, dist_zero_right] using hSpectral
  exact (Complex.re_le_norm spectral).trans hNorm.le

private theorem reducedSphereShortRemainder_norm_le
    (data : ProductThroatSpectralData) {time : Real}
    (hTime : time ∈ Set.Ioc (0 : Real) 1) :
    ‖(((positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time -
        reducedSphereCounterterm data time) / time : Real) : Complex)‖ ≤
      sphereShortTimeMajorant data time := by
  have hBound := sphereShortTimeMajorant_bound data hTime
  rw [Complex.norm_real]
  simpa [dimensionlessReducedSphereHeatTrace, dimensionlessSphereHeatTrace,
    reducedSphereCounterterm, hTime.1] using hBound

private theorem reducedSphereMellinShort_integrand_norm_le
    (data : ProductThroatSpectralData) {spectral : Complex} {time : Real}
    (hSpectral : spectral ∈ Metric.ball 0 ((1 : Real) / 2))
    (hTime : time ∈ Set.Ioc (0 : Real) 1) :
    ‖(time : Complex) ^ spectral *
        (((positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time -
          reducedSphereCounterterm data time) / time : Real) : Complex)‖ ≤
      reducedSphereMellinShortGermMajorant data time := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hTime.1]
  have hPower : time ^ spectral.re ≤ time ^ (-(1 : Real) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hTime.1 hTime.2
      (spectral_re_lower_of_mem_halfBall hSpectral)
  have hRemainder := reducedSphereShortRemainder_norm_le data hTime
  have hMajorantNonnegative : 0 ≤ sphereShortTimeMajorant data time := by
    exact (norm_nonneg _).trans hRemainder
  calc
    time ^ spectral.re *
          ‖(((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time -
            reducedSphereCounterterm data time) / time : Real) : Complex)‖ ≤
        time ^ spectral.re * sphereShortTimeMajorant data time :=
      mul_le_mul_of_nonneg_left hRemainder
        (Real.rpow_nonneg hTime.1.le _)
    _ ≤ time ^ (-(1 : Real) / 2) * sphereShortTimeMajorant data time :=
      mul_le_mul_of_nonneg_right hPower hMajorantNonnegative
    _ = reducedSphereMellinShortGermMajorant data time := rfl

private theorem reducedSphereMellinLong_integrand_norm_le
    (data : ProductThroatSpectralData) {spectral : Complex} {time : Real}
    (hSpectral : spectral ∈ Metric.ball 0 ((1 : Real) / 2))
    (hTime : time ∈ Set.Ioi (1 : Real)) :
    ‖(time : Complex) ^ spectral *
        ((positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex)‖ ≤
      reducedSphereMellinLongGermMajorant data time := by
  have hTimePos : 0 < time := (by norm_num : (0 : Real) < 1).trans hTime
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hTimePos]
  have hPower : time ^ spectral.re ≤ time ^ ((1 : Real) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hTime.le
      (spectral_re_upper_of_mem_halfBall hSpectral)
  have hTrace :
      ‖((positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex)‖ ≤
        longTimeExponentialBound (reducedSphereLongTimeScale data)
          ((1 : Real) / 2) time := by
    rw [Complex.norm_real]
    simpa [dimensionlessReducedSphereHeatTrace, dimensionlessSphereHeatTrace,
      hTimePos] using reducedSphereLogTrace_le_longTimeExponential data hTime
  have hLongNonnegative :
      0 ≤ longTimeExponentialBound (reducedSphereLongTimeScale data)
        ((1 : Real) / 2) time := by
    exact (norm_nonneg _).trans hTrace
  calc
    time ^ spectral.re *
          ‖((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex)‖ ≤
        time ^ spectral.re *
          longTimeExponentialBound (reducedSphereLongTimeScale data)
            ((1 : Real) / 2) time :=
      mul_le_mul_of_nonneg_left hTrace (Real.rpow_nonneg hTimePos.le _)
    _ ≤ time ^ ((1 : Real) / 2) *
          longTimeExponentialBound (reducedSphereLongTimeScale data)
            ((1 : Real) / 2) time :=
      mul_le_mul_of_nonneg_right hPower hLongNonnegative
    _ = reducedSphereMellinLongGermMajorant data time := rfl

private theorem reducedSphereMellinShort_integrand_aestronglyMeasurable
    (data : ProductThroatSpectralData) (spectral : Complex) :
    AEStronglyMeasurable
      (fun time : Real =>
        (time : Complex) ^ spectral *
          (((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time -
            reducedSphereCounterterm data time) / time : Real) : Complex))
      (volume.restrict (Set.Ioc (0 : Real) 1)) := by
  have hPower : AEStronglyMeasurable
      (fun time : Real => (time : Complex) ^ spectral)
      (volume.restrict (Set.Ioc (0 : Real) 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    exact continuousOn_of_forall_continuousAt fun time hTime =>
      Complex.continuousAt_ofReal_cpow_const time spectral
        (Or.inr hTime.1.ne')
  have hRemainder : AEStronglyMeasurable
      (fun time : Real =>
        (((positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time -
          reducedSphereCounterterm data time) / time : Real) : Complex))
      (volume.restrict (Set.Ioc (0 : Real) 1)) :=
    (positiveTimeReducedSphere_shortTimeIntegrable data).ofReal.aestronglyMeasurable
  exact hPower.mul hRemainder

private theorem reducedSphereMellinLong_integrand_aestronglyMeasurable
    (data : ProductThroatSpectralData) (spectral : Complex) :
    AEStronglyMeasurable
      (fun time : Real =>
        (time : Complex) ^ spectral *
          ((positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex))
      (volume.restrict (Set.Ioi (1 : Real))) := by
  have hPower : AEStronglyMeasurable
      (fun time : Real => (time : Complex) ^ spectral)
      (volume.restrict (Set.Ioi (1 : Real))) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact continuousOn_of_forall_continuousAt fun time hTime =>
      Complex.continuousAt_ofReal_cpow_const time spectral
        (Or.inr ((by norm_num : (0 : Real) < 1).trans hTime).ne')
  have hTail : AEStronglyMeasurable
      (fun time : Real =>
        ((positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex))
      (volume.restrict (Set.Ioi (1 : Real))) :=
    (positiveTimeReducedSphere_longTimeIntegrable data).ofReal.aestronglyMeasurable
  exact hPower.mul hTail

theorem reducedSphereMellinShortRemainder_integrableOn_halfBall
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hSpectral : spectral ∈ Metric.ball 0 ((1 : Real) / 2)) :
    IntegrableOn
      (fun time : Real =>
        (time : Complex) ^ spectral *
          (((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time -
            reducedSphereCounterterm data time) / time : Real) : Complex))
      (Set.Ioc (0 : Real) 1) := by
  refine (reducedSphereMellinShortGermMajorant_integrableOn data).mono'
    (reducedSphereMellinShort_integrand_aestronglyMeasurable data spectral) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
  exact reducedSphereMellinShort_integrand_norm_le data hSpectral hTime

theorem reducedSphereMellinLongTail_integrableOn_halfBall
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hSpectral : spectral ∈ Metric.ball 0 ((1 : Real) / 2)) :
    IntegrableOn
      (fun time : Real =>
        (time : Complex) ^ spectral *
          ((positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex))
      (Set.Ioi (1 : Real)) := by
  refine (reducedSphereMellinLongGermMajorant_integrableOn data).mono'
    (reducedSphereMellinLong_integrand_aestronglyMeasurable data spectral) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact reducedSphereMellinLong_integrand_norm_le data hSpectral hTime

theorem reducedSphereMellinShortRemainderIntegral_continuousAt_zero
    (data : ProductThroatSpectralData) :
    ContinuousAt (reducedSphereMellinShortRemainderIntegral data) 0 := by
  unfold reducedSphereMellinShortRemainderIntegral ContinuousAt
  refine tendsto_integral_filter_of_dominated_convergence
    (reducedSphereMellinShortGermMajorant data)
    (Eventually.of_forall
      (reducedSphereMellinShort_integrand_aestronglyMeasurable data)) ?_
    (reducedSphereMellinShortGermMajorant_integrableOn data) ?_
  · filter_upwards
      [Metric.ball_mem_nhds (0 : Complex) (by norm_num : (0 : Real) < 1 / 2)]
      with spectral hSpectral
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
    exact reducedSphereMellinShort_integrand_norm_le data hSpectral hTime
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
    have hPower : ContinuousAt
        (fun spectral : Complex => (time : Complex) ^ spectral) 0 :=
      ((hasDerivAt_id' (0 : Complex)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hTime.1.ne'))).continuousAt
    exact hPower.mul continuousAt_const

theorem reducedSphereMellinLongTailIntegral_continuousAt_zero
    (data : ProductThroatSpectralData) :
    ContinuousAt (reducedSphereMellinLongTailIntegral data) 0 := by
  unfold reducedSphereMellinLongTailIntegral ContinuousAt
  refine tendsto_integral_filter_of_dominated_convergence
    (reducedSphereMellinLongGermMajorant data)
    (Eventually.of_forall
      (reducedSphereMellinLong_integrand_aestronglyMeasurable data)) ?_
    (reducedSphereMellinLongGermMajorant_integrableOn data) ?_
  · filter_upwards
      [Metric.ball_mem_nhds (0 : Complex) (by norm_num : (0 : Real) < 1 / 2)]
      with spectral hSpectral
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    exact reducedSphereMellinLong_integrand_norm_le data hSpectral hTime
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    have hTimePos : 0 < time :=
      (by norm_num : (0 : Real) < 1).trans hTime
    have hPower : ContinuousAt
        (fun spectral : Complex => (time : Complex) ^ spectral) 0 :=
      ((hasDerivAt_id' (0 : Complex)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hTimePos.ne'))).continuousAt
    exact hPower.mul continuousAt_const

@[simp]
theorem reducedSphereMellinShortRemainderIntegral_zero
    (data : ProductThroatSpectralData) :
    reducedSphereMellinShortRemainderIntegral data 0 =
      (relativeHeatShortTimeFinitePart
        (reducedSphereMellinFinitePartData data) : Complex) := by
  unfold reducedSphereMellinShortRemainderIntegral
    relativeHeatShortTimeFinitePart reducedSphereMellinFinitePartData
  simp only [Complex.cpow_zero, one_mul]
  exact integral_complex_ofReal

@[simp]
theorem reducedSphereMellinLongTailIntegral_zero
    (data : ProductThroatSpectralData) :
    reducedSphereMellinLongTailIntegral data 0 =
      (relativeHeatLongTimeIntegral
        (reducedSphereMellinFinitePartData data) : Complex) := by
  unfold reducedSphereMellinLongTailIntegral relativeHeatLongTimeIntegral
  simp only [Complex.cpow_zero, one_mul]
  exact integral_complex_ofReal

/-- Sum of the two genuinely integrable Mellin pieces. -/
def reducedSphereMellinRegularRemainderIntegral
    (data : ProductThroatSpectralData) (spectral : Complex) : Complex :=
  reducedSphereMellinShortRemainderIntegral data spectral +
    reducedSphereMellinLongTailIntegral data spectral

theorem reducedSphereMellinRegularRemainderIntegral_continuousAt_zero
    (data : ProductThroatSpectralData) :
    ContinuousAt (reducedSphereMellinRegularRemainderIntegral data) 0 :=
  (reducedSphereMellinShortRemainderIntegral_continuousAt_zero data).add
    (reducedSphereMellinLongTailIntegral_continuousAt_zero data)

@[simp]
theorem reducedSphereMellinRegularRemainderIntegral_zero
    (data : ProductThroatSpectralData) :
    reducedSphereMellinRegularRemainderIntegral data 0 =
      ((relativeHeatShortTimeFinitePart
          (reducedSphereMellinFinitePartData data) +
        relativeHeatLongTimeIntegral
          (reducedSphereMellinFinitePartData data) : Real) : Complex) := by
  simp [reducedSphereMellinRegularRemainderIntegral]

/-- Reciprocal Gamma has its standard simple-zero slope limit. -/
theorem one_div_Gamma_tendsto_slope_zero :
    Tendsto
      (slope (fun spectral : Complex => (Complex.Gamma spectral)⁻¹) 0)
      (𝓝[≠] (0 : Complex)) (𝓝 (1 : Complex)) := by
  have hShift : DifferentiableAt Complex
      (fun spectral : Complex => (Complex.Gamma (spectral + 1))⁻¹) 0 :=
    Complex.differentiable_one_div_Gamma.differentiableAt.comp 0
      ((differentiableAt_id.add_const (1 : Complex)))
  have hProductRaw :=
    (hasDerivAt_id (𝕜 := Complex) 0).mul hShift.hasDerivAt
  have hProduct := hProductRaw.congr_deriv (show
      1 * (Complex.Gamma ((0 : Complex) + 1))⁻¹ +
          0 * deriv (fun spectral : Complex =>
            (Complex.Gamma (spectral + 1))⁻¹) 0 = 1 by
    simp [Complex.Gamma_one])
  have hFunction :
      (id * fun spectral : Complex =>
        (Complex.Gamma (spectral + 1))⁻¹) =
        (fun spectral : Complex => (Complex.Gamma spectral)⁻¹) := by
    funext spectral
    exact (Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one spectral).symm
  rw [hFunction] at hProduct
  exact hProduct.tendsto_slope

/-- Reciprocal Gamma has its standard simple zero with derivative one. -/
theorem one_div_Gamma_hasDerivAt_zero :
    HasDerivAt (fun spectral : Complex => (Complex.Gamma spectral)⁻¹) 1 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  exact one_div_Gamma_tendsto_slope_zero

private theorem hasDerivAt_mul_of_left_zero_of_continuousAt
    {left right : Complex → Complex} {leftDerivative : Complex}
    (hLeft : HasDerivAt left leftDerivative 0)
    (hLeftZero : left 0 = 0) (hRight : ContinuousAt right 0) :
    HasDerivAt (fun spectral => left spectral * right spectral)
      (leftDerivative * right 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hRight' : Tendsto right (𝓝[≠] (0 : Complex)) (𝓝 (right 0)) :=
    hRight.tendsto.mono_left inf_le_left
  refine (hLeft.tendsto_slope.mul hRight').congr' ?_
  filter_upwards [self_mem_nhdsWithin] with spectral hSpectral
  simp [slope, hLeftZero, smul_eq_mul, mul_assoc]

/-- Gamma-normalized contribution of the two integrable Mellin pieces. -/
def reducedSphereMellinRegularRemainderZeta
    (data : ProductThroatSpectralData) (spectral : Complex) : Complex :=
  (Complex.Gamma spectral)⁻¹ *
    reducedSphereMellinRegularRemainderIntegral data spectral

@[simp]
theorem reducedSphereMellinRegularRemainderZeta_zero
    (data : ProductThroatSpectralData) :
    reducedSphereMellinRegularRemainderZeta data 0 = 0 := by
  simp [reducedSphereMellinRegularRemainderZeta]

/-- The simple zero of reciprocal Gamma extracts exactly the finite value of
the regular Mellin remainder. -/
theorem reducedSphereMellinRegularRemainderZeta_hasDerivAt_zero
    (data : ProductThroatSpectralData) :
    HasDerivAt (reducedSphereMellinRegularRemainderZeta data)
      ((relativeHeatShortTimeFinitePart
          (reducedSphereMellinFinitePartData data) +
        relativeHeatLongTimeIntegral
          (reducedSphereMellinFinitePartData data) : Real) : Complex) 0 := by
  unfold reducedSphereMellinRegularRemainderZeta
  simpa using hasDerivAt_mul_of_left_zero_of_continuousAt
    one_div_Gamma_hasDerivAt_zero
    (by simp)
    (reducedSphereMellinRegularRemainderIntegral_continuousAt_zero data)

/-- Public local checkpoint: honest integrability on a complex disk,
continuity at the origin, and the Gamma-normalized derivative formula. -/
theorem product_throat_sphere_mellin_remainder_germ_gate
    (data : ProductThroatSpectralData) :
    (∀ spectral : Complex, spectral ∈ Metric.ball 0 ((1 : Real) / 2) →
        IntegrableOn
          (fun time : Real =>
            (time : Complex) ^ spectral *
              (((positiveTimeTraceExtension
                  (dimensionlessReducedSphereHeatTrace data) time -
                reducedSphereCounterterm data time) / time : Real) : Complex))
          (Set.Ioc (0 : Real) 1)) ∧
      (∀ spectral : Complex, spectral ∈ Metric.ball 0 ((1 : Real) / 2) →
        IntegrableOn
          (fun time : Real =>
            (time : Complex) ^ spectral *
              ((positiveTimeTraceExtension
                (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex))
          (Set.Ioi (1 : Real))) ∧
      ContinuousAt (reducedSphereMellinRegularRemainderIntegral data) 0 ∧
      HasDerivAt (reducedSphereMellinRegularRemainderZeta data)
        ((relativeHeatShortTimeFinitePart
            (reducedSphereMellinFinitePartData data) +
          relativeHeatLongTimeIntegral
            (reducedSphereMellinFinitePartData data) : Real) : Complex) 0 := by
  exact ⟨fun (spectral : Complex) hSpectral =>
      reducedSphereMellinShortRemainder_integrableOn_halfBall data hSpectral,
    fun (spectral : Complex) hSpectral =>
      reducedSphereMellinLongTail_integrableOn_halfBall data hSpectral,
    reducedSphereMellinRegularRemainderIntegral_continuousAt_zero data,
    reducedSphereMellinRegularRemainderZeta_hasDerivAt_zero data⟩

end
end P0EFTJanusProgramPProductThroatSphereMellinRemainderGerm4D
end JanusFormal
