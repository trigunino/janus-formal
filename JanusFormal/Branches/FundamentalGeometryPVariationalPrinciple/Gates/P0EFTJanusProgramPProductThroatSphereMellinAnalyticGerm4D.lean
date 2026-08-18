import Mathlib.Analysis.Complex.CauchyIntegral
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinZetaContinuation4D

/-!
# Holomorphic Mellin germ of the reduced-sphere remainder

The logarithm produced by differentiating `t ^ s` is absorbed by the gap
between the parameter disks of radii `1 / 4` and `3 / 8`.  Differentiation
under the integral then makes both integrable Mellin pieces holomorphic near
the origin.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereMellinAnalyticGerm4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPProductThroatSphereMellinRemainderGerm4D
open P0EFTJanusProgramPProductThroatSphereMellinCountertermContinuation4D
open P0EFTJanusProgramPProductThroatSphereMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

private theorem spectral_re_lower_of_mem_three_eighths_ball
    {spectral : Complex}
    (hSpectral : spectral ∈ Metric.ball 0 ((3 : Real) / 8)) :
    -(3 : Real) / 8 ≤ spectral.re := by
  have hNorm : ‖spectral‖ < (3 : Real) / 8 := by
    simpa [Metric.mem_ball, dist_zero_right] using hSpectral
  have hAbs := Complex.abs_re_le_norm spectral
  linarith [neg_le_abs spectral.re]

private theorem spectral_re_upper_of_mem_three_eighths_ball
    {spectral : Complex}
    (hSpectral : spectral ∈ Metric.ball 0 ((3 : Real) / 8)) :
    spectral.re ≤ (3 : Real) / 8 := by
  have hNorm : ‖spectral‖ < (3 : Real) / 8 := by
    simpa [Metric.mem_ball, dist_zero_right] using hSpectral
  exact (Complex.re_le_norm spectral).trans hNorm.le

private theorem quarter_ball_subset_three_eighths_ball :
    Metric.ball (0 : Complex) ((1 : Real) / 4) ⊆
      Metric.ball 0 ((3 : Real) / 8) := by
  intro spectral hSpectral
  rw [Metric.mem_ball] at hSpectral ⊢
  exact hSpectral.trans (by norm_num)

private theorem three_eighths_ball_subset_half_ball :
    Metric.ball (0 : Complex) ((3 : Real) / 8) ⊆
      Metric.ball 0 ((1 : Real) / 2) := by
  intro spectral hSpectral
  rw [Metric.mem_ball] at hSpectral ⊢
  exact hSpectral.trans (by norm_num)

private theorem short_log_power_bound {time : Real}
    (hTime : time ∈ Set.Ioc (0 : Real) 1) :
    time ^ (-(3 : Real) / 8) * |Real.log time| ≤
      8 * time ^ (-(1 : Real) / 2) := by
  have hLog := Real.abs_log_mul_self_rpow_lt time ((1 : Real) / 8)
    hTime.1 hTime.2 (by norm_num)
  have hPowerPos : 0 < time ^ ((1 : Real) / 8) :=
    Real.rpow_pos_of_pos hTime.1 _
  rw [abs_mul, abs_of_pos hPowerPos] at hLog
  norm_num at hLog
  calc
    time ^ (-(3 : Real) / 8) * |Real.log time| =
        time ^ (-(1 : Real) / 2) *
          (|Real.log time| * time ^ ((1 : Real) / 8)) := by
      rw [show -(3 : Real) / 8 = -(1 : Real) / 2 + (1 : Real) / 8 by norm_num,
        Real.rpow_add hTime.1]
      ring
    _ ≤ time ^ (-(1 : Real) / 2) * 8 :=
      mul_le_mul_of_nonneg_left hLog.le
        (Real.rpow_nonneg hTime.1.le _)
    _ = 8 * time ^ (-(1 : Real) / 2) := by ring

private theorem long_log_power_bound {time : Real}
    (hTime : time ∈ Set.Ioi (1 : Real)) :
    time ^ ((3 : Real) / 8) * |Real.log time| ≤
      8 * time ^ ((1 : Real) / 2) := by
  have hTimePos : 0 < time := (by norm_num : (0 : Real) < 1).trans hTime
  have hLogNonnegative : 0 ≤ Real.log time := Real.log_nonneg hTime.le
  have hLog := Real.log_le_rpow_div hTimePos.le
    (by norm_num : (0 : Real) < (1 : Real) / 8)
  rw [abs_of_nonneg hLogNonnegative]
  calc
    time ^ ((3 : Real) / 8) * Real.log time ≤
        time ^ ((3 : Real) / 8) *
          (time ^ ((1 : Real) / 8) / ((1 : Real) / 8)) :=
      mul_le_mul_of_nonneg_left hLog
        (Real.rpow_nonneg hTimePos.le _)
    _ = 8 * time ^ ((1 : Real) / 2) := by
      rw [show (1 : Real) / 2 = 3 / 8 + 1 / 8 by norm_num,
        Real.rpow_add hTimePos]
      norm_num [div_eq_mul_inv]
      ring

/-- Parameter derivative of the short integrand. -/
def reducedSphereMellinShortDerivativeIntegrand
    (data : ProductThroatSpectralData) (spectral : Complex)
    (time : Real) : Complex :=
  ((time : Complex) ^ spectral * Complex.log (time : Complex)) *
    (((positiveTimeTraceExtension
        (dimensionlessReducedSphereHeatTrace data) time -
      reducedSphereCounterterm data time) / time : Real) : Complex)

/-- Parameter derivative of the long integrand. -/
def reducedSphereMellinLongDerivativeIntegrand
    (data : ProductThroatSpectralData) (spectral : Complex)
    (time : Real) : Complex :=
  ((time : Complex) ^ spectral * Complex.log (time : Complex)) *
    ((positiveTimeTraceExtension
      (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex)

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

private theorem reducedSphereMellinShortDerivative_norm_le
    (data : ProductThroatSpectralData) {spectral : Complex} {time : Real}
    (hSpectral : spectral ∈ Metric.ball 0 ((3 : Real) / 8))
    (hTime : time ∈ Set.Ioc (0 : Real) 1) :
    ‖reducedSphereMellinShortDerivativeIntegrand data spectral time‖ ≤
      8 * reducedSphereMellinShortGermMajorant data time := by
  have hPower : time ^ spectral.re ≤ time ^ (-(3 : Real) / 8) :=
    Real.rpow_le_rpow_of_exponent_ge hTime.1 hTime.2
      (spectral_re_lower_of_mem_three_eighths_ball hSpectral)
  have hRemainder := reducedSphereShortRemainder_norm_le data hTime
  have hRemainderNonnegative : 0 ≤ sphereShortTimeMajorant data time :=
    (norm_nonneg _).trans hRemainder
  have hLogNonnegative : 0 ≤ |Real.log time| := abs_nonneg _
  unfold reducedSphereMellinShortDerivativeIntegrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hTime.1,
    ← Complex.ofReal_log hTime.1.le, Complex.norm_real]
  calc
    time ^ spectral.re * |Real.log time| *
          ‖(((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time -
            reducedSphereCounterterm data time) / time : Real) : Complex)‖ ≤
        time ^ spectral.re * |Real.log time| *
          sphereShortTimeMajorant data time :=
      mul_le_mul_of_nonneg_left hRemainder
        (mul_nonneg (Real.rpow_nonneg hTime.1.le _) hLogNonnegative)
    _ ≤ time ^ (-(3 : Real) / 8) * |Real.log time| *
          sphereShortTimeMajorant data time :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hPower hLogNonnegative)
        hRemainderNonnegative
    _ ≤ (8 * time ^ (-(1 : Real) / 2)) *
          sphereShortTimeMajorant data time :=
      mul_le_mul_of_nonneg_right (short_log_power_bound hTime)
        hRemainderNonnegative
    _ = 8 * reducedSphereMellinShortGermMajorant data time := by
      unfold reducedSphereMellinShortGermMajorant
      ring

private theorem reducedSphereMellinLongDerivative_norm_le
    (data : ProductThroatSpectralData) {spectral : Complex} {time : Real}
    (hSpectral : spectral ∈ Metric.ball 0 ((3 : Real) / 8))
    (hTime : time ∈ Set.Ioi (1 : Real)) :
    ‖reducedSphereMellinLongDerivativeIntegrand data spectral time‖ ≤
      8 * reducedSphereMellinLongGermMajorant data time := by
  have hTimePos : 0 < time := (by norm_num : (0 : Real) < 1).trans hTime
  have hPower : time ^ spectral.re ≤ time ^ ((3 : Real) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hTime.le
      (spectral_re_upper_of_mem_three_eighths_ball hSpectral)
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
        ((1 : Real) / 2) time := (norm_nonneg _).trans hTrace
  have hLogNonnegative : 0 ≤ |Real.log time| := abs_nonneg _
  unfold reducedSphereMellinLongDerivativeIntegrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hTimePos,
    ← Complex.ofReal_log hTimePos.le, Complex.norm_real]
  calc
    time ^ spectral.re * |Real.log time| *
          ‖((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex)‖ ≤
        time ^ spectral.re * |Real.log time| *
          longTimeExponentialBound (reducedSphereLongTimeScale data)
            ((1 : Real) / 2) time :=
      mul_le_mul_of_nonneg_left hTrace
        (mul_nonneg (Real.rpow_nonneg hTimePos.le _) hLogNonnegative)
    _ ≤ time ^ ((3 : Real) / 8) * |Real.log time| *
          longTimeExponentialBound (reducedSphereLongTimeScale data)
            ((1 : Real) / 2) time :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hPower hLogNonnegative)
        hLongNonnegative
    _ ≤ (8 * time ^ ((1 : Real) / 2)) *
          longTimeExponentialBound (reducedSphereLongTimeScale data)
            ((1 : Real) / 2) time :=
      mul_le_mul_of_nonneg_right (long_log_power_bound hTime)
        hLongNonnegative
    _ = 8 * reducedSphereMellinLongGermMajorant data time := by
      unfold reducedSphereMellinLongGermMajorant
      ring

private theorem complexLogOfReal_aestronglyMeasurable_Ioc :
    AEStronglyMeasurable (fun time : Real => Complex.log (time : Complex))
      (volume.restrict (Set.Ioc (0 : Real) 1)) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
  exact continuousOn_of_forall_continuousAt fun time hTime =>
    (show ContinuousAt (fun x : Real => (x : Complex)) time by fun_prop).clog
      (Complex.ofReal_mem_slitPlane.mpr hTime.1)

private theorem complexLogOfReal_aestronglyMeasurable_Ioi :
    AEStronglyMeasurable (fun time : Real => Complex.log (time : Complex))
      (volume.restrict (Set.Ioi (1 : Real))) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  exact continuousOn_of_forall_continuousAt fun time hTime =>
    (show ContinuousAt (fun x : Real => (x : Complex)) time by fun_prop).clog
      (Complex.ofReal_mem_slitPlane.mpr
        ((by norm_num : (0 : Real) < 1).trans hTime))

private theorem reducedSphereMellinShortDerivative_aestronglyMeasurable
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hSpectral : spectral ∈ Metric.ball 0 ((1 : Real) / 2)) :
    AEStronglyMeasurable
      (reducedSphereMellinShortDerivativeIntegrand data spectral)
      (volume.restrict (Set.Ioc (0 : Real) 1)) := by
  have hOriginal :=
    (reducedSphereMellinShortRemainder_integrableOn_halfBall data hSpectral).1
  refine (hOriginal.mul complexLogOfReal_aestronglyMeasurable_Ioc).congr
    (Filter.Eventually.of_forall fun time => ?_)
  simp only [reducedSphereMellinShortDerivativeIntegrand, Pi.mul_apply]
  ring

private theorem reducedSphereMellinLongDerivative_aestronglyMeasurable
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hSpectral : spectral ∈ Metric.ball 0 ((1 : Real) / 2)) :
    AEStronglyMeasurable
      (reducedSphereMellinLongDerivativeIntegrand data spectral)
      (volume.restrict (Set.Ioi (1 : Real))) := by
  have hOriginal :=
    (reducedSphereMellinLongTail_integrableOn_halfBall data hSpectral).1
  refine (hOriginal.mul complexLogOfReal_aestronglyMeasurable_Ioi).congr
    (Filter.Eventually.of_forall fun time => ?_)
  simp only [reducedSphereMellinLongDerivativeIntegrand, Pi.mul_apply]
  ring

private theorem reducedSphereMellinShort_hasDerivAt
    (data : ProductThroatSpectralData) (spectral : Complex) {time : Real}
    (hTime : time ∈ Set.Ioc (0 : Real) 1) :
    HasDerivAt
      (fun z : Complex =>
        (time : Complex) ^ z *
          (((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time -
            reducedSphereCounterterm data time) / time : Real) : Complex))
      (reducedSphereMellinShortDerivativeIntegrand data spectral time)
      spectral := by
  simpa [reducedSphereMellinShortDerivativeIntegrand, mul_assoc] using
    (((hasDerivAt_id' spectral).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hTime.1.ne'))).mul_const
        (((positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time -
          reducedSphereCounterterm data time) / time : Real) : Complex))

private theorem reducedSphereMellinLong_hasDerivAt
    (data : ProductThroatSpectralData) (spectral : Complex) {time : Real}
    (hTime : time ∈ Set.Ioi (1 : Real)) :
    HasDerivAt
      (fun z : Complex =>
        (time : Complex) ^ z *
          ((positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex))
      (reducedSphereMellinLongDerivativeIntegrand data spectral time)
      spectral := by
  have hTimePos : 0 < time := (by norm_num : (0 : Real) < 1).trans hTime
  simpa [reducedSphereMellinLongDerivativeIntegrand, mul_assoc] using
    (((hasDerivAt_id' spectral).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hTimePos.ne'))).mul_const
        ((positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex))

/-- Differentiation under the short-time remainder integral on the inner
parameter disk. -/
theorem reducedSphereMellinShortRemainderIntegral_hasDerivAt
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hSpectral : spectral ∈ Metric.ball 0 ((1 : Real) / 4)) :
    HasDerivAt (reducedSphereMellinShortRemainderIntegral data)
      (∫ time in Set.Ioc (0 : Real) 1,
        reducedSphereMellinShortDerivativeIntegrand data spectral time)
      spectral := by
  have hThree := quarter_ball_subset_three_eighths_ball hSpectral
  have hHalf := three_eighths_ball_subset_half_ball hThree
  unfold reducedSphereMellinShortRemainderIntegral
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0 : Real) 1))
    (F' := reducedSphereMellinShortDerivativeIntegrand data)
    (bound := fun time =>
      8 * reducedSphereMellinShortGermMajorant data time)
    (s := Metric.ball 0 ((3 : Real) / 8))
    (isOpen_ball.mem_nhds hThree) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [isOpen_ball.mem_nhds hHalf] with z hz
    exact (reducedSphereMellinShortRemainder_integrableOn_halfBall
      data hz).aestronglyMeasurable
  · exact reducedSphereMellinShortRemainder_integrableOn_halfBall data hHalf
  · exact reducedSphereMellinShortDerivative_aestronglyMeasurable data hHalf
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
    intro z hz
    exact reducedSphereMellinShortDerivative_norm_le data hz hTime
  · exact (reducedSphereMellinShortGermMajorant_integrableOn data).const_mul 8
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
    intro z _
    exact reducedSphereMellinShort_hasDerivAt data z hTime

/-- Differentiation under the exponentially decaying tail integral on the
inner parameter disk. -/
theorem reducedSphereMellinLongTailIntegral_hasDerivAt
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hSpectral : spectral ∈ Metric.ball 0 ((1 : Real) / 4)) :
    HasDerivAt (reducedSphereMellinLongTailIntegral data)
      (∫ time in Set.Ioi (1 : Real),
        reducedSphereMellinLongDerivativeIntegrand data spectral time)
      spectral := by
  have hThree := quarter_ball_subset_three_eighths_ball hSpectral
  have hHalf := three_eighths_ball_subset_half_ball hThree
  unfold reducedSphereMellinLongTailIntegral
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (1 : Real)))
    (F' := reducedSphereMellinLongDerivativeIntegrand data)
    (bound := fun time =>
      8 * reducedSphereMellinLongGermMajorant data time)
    (s := Metric.ball 0 ((3 : Real) / 8))
    (isOpen_ball.mem_nhds hThree) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [isOpen_ball.mem_nhds hHalf] with z hz
    exact (reducedSphereMellinLongTail_integrableOn_halfBall
      data hz).aestronglyMeasurable
  · exact reducedSphereMellinLongTail_integrableOn_halfBall data hHalf
  · exact reducedSphereMellinLongDerivative_aestronglyMeasurable data hHalf
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    intro z hz
    exact reducedSphereMellinLongDerivative_norm_le data hz hTime
  · exact (reducedSphereMellinLongGermMajorant_integrableOn data).const_mul 8
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    intro z _
    exact reducedSphereMellinLong_hasDerivAt data z hTime

/-- Both integrable Mellin pieces are holomorphic on the quarter disk. -/
theorem reducedSphereMellinRegularRemainderIntegral_differentiableOn
    (data : ProductThroatSpectralData) :
    DifferentiableOn Complex (reducedSphereMellinRegularRemainderIntegral data)
      (Metric.ball 0 ((1 : Real) / 4)) := by
  intro spectral hSpectral
  exact ((reducedSphereMellinShortRemainderIntegral_hasDerivAt
      data hSpectral).add
    (reducedSphereMellinLongTailIntegral_hasDerivAt
      data hSpectral)).differentiableAt.differentiableWithinAt

/-- The regular Mellin remainder is analytic at the origin. -/
theorem reducedSphereMellinRegularRemainderIntegral_analyticAt_zero
    (data : ProductThroatSpectralData) :
    AnalyticAt Complex (reducedSphereMellinRegularRemainderIntegral data) 0 := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards
    [Metric.ball_mem_nhds (0 : Complex) (by norm_num : (0 : Real) < 1 / 4)]
    with spectral hSpectral
  exact ((reducedSphereMellinShortRemainderIntegral_hasDerivAt
      data hSpectral).add
    (reducedSphereMellinLongTailIntegral_hasDerivAt
      data hSpectral)).differentiableAt

/-- Gamma normalization preserves the analytic remainder germ. -/
theorem reducedSphereMellinRegularRemainderZeta_analyticAt_zero
    (data : ProductThroatSpectralData) :
    AnalyticAt Complex (reducedSphereMellinRegularRemainderZeta data) 0 := by
  unfold reducedSphereMellinRegularRemainderZeta
  exact (Complex.differentiable_one_div_Gamma.analyticAt 0).mul
    (reducedSphereMellinRegularRemainderIntegral_analyticAt_zero data)

/-- The explicit reduced-sphere zeta formula is an honest holomorphic germ
at zero.  This statement is local; the disk itself does not meet `1 < re s`.
-/
theorem reducedSphereMellinZeta_analyticAt_zero
    (data : ProductThroatSpectralData) :
    AnalyticAt Complex (reducedSphereMellinZeta data) 0 := by
  unfold reducedSphereMellinZeta
  exact (reducedSphereMellinRegularRemainderZeta_analyticAt_zero data).add
    (reducedSphereCountertermMellinZeta_analyticAt_zero data)

/-- Public local checkpoint.  It deliberately records a germ near zero,
not yet analytic connectedness with the convergent half-plane. -/
theorem product_throat_sphere_mellin_analytic_germ_gate
    (data : ProductThroatSpectralData) :
    DifferentiableOn Complex
        (reducedSphereMellinRegularRemainderIntegral data)
        (Metric.ball 0 ((1 : Real) / 4)) ∧
      AnalyticAt Complex
        (reducedSphereMellinRegularRemainderZeta data) 0 ∧
      AnalyticAt Complex (reducedSphereMellinZeta data) 0 :=
  ⟨reducedSphereMellinRegularRemainderIntegral_differentiableOn data,
    reducedSphereMellinRegularRemainderZeta_analyticAt_zero data,
    reducedSphereMellinZeta_analyticAt_zero data⟩

end
end P0EFTJanusProgramPProductThroatSphereMellinAnalyticGerm4D
end JanusFormal
