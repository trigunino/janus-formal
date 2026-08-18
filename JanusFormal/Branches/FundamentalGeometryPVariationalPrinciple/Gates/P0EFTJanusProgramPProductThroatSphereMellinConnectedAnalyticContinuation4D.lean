import Mathlib.Analysis.Normed.Module.Connected
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinAnalyticGerm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinConnectedAnalyticSchwarz4D

/-!
# Connected analytic Mellin continuation for the reduced sphere

Three overlapping disks form an open corridor from the origin to the
convergent Mellin half-plane while avoiding the genuine pole at `s = 1`.
Uniform short-time and exponential-tail envelopes prove holomorphy on the
whole corridor, so the zero germ and the spectral Mellin germ are restrictions
of one concrete analytic function.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereMellinConnectedAnalyticContinuation4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D
open P0EFTJanusProgramPProductThroatSphereMellinRemainderGerm4D
open P0EFTJanusProgramPProductThroatSphereMellinCountertermContinuation4D
open P0EFTJanusProgramPProductThroatSphereMellinZetaContinuation4D
open P0EFTJanusProgramPProductThroatSphereMellinAnalyticGerm4D
open P0EFTJanusProgramPRelativeHeatMellinConnectedAnalyticContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinConnectedAnalyticSchwarz4D
open P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D

/-- Left disk containing the Mellin origin. -/
def reducedSphereMellinLeftDisk : Set Complex :=
  Metric.ball 0 ((1 : Real) / 3)

/-- Upper disk routing the continuation around the pole at `1`. -/
def reducedSphereMellinBridgeDisk : Set Complex :=
  Metric.ball ((3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I)
    ((3 : Real) / 5)

/-- Conjugate lower disk, making the corridor Schwarz invariant. -/
def reducedSphereMellinLowerBridgeDisk : Set Complex :=
  Metric.ball ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I)
    ((3 : Real) / 5)

/-- Right disk containing the convergent seed `5 / 4`. -/
def reducedSphereMellinSeedDisk : Set Complex :=
  Metric.ball ((5 : Complex) / 4) ((1 : Real) / 4)

/-- Explicit open corridor connecting zero to a point with real part above
the convergence abscissa, without containing the pole at `1`. -/
def reducedSphereMellinConnectedDomain : Set Complex :=
  ((reducedSphereMellinLeftDisk ∪ reducedSphereMellinBridgeDisk) ∪
    reducedSphereMellinLowerBridgeDisk) ∪ reducedSphereMellinSeedDisk

theorem reducedSphereMellinConnectedDomain_isOpen :
    IsOpen reducedSphereMellinConnectedDomain := by
  exact ((isOpen_ball.union isOpen_ball).union isOpen_ball).union isOpen_ball

private theorem left_bridge_inter_nonempty :
    (reducedSphereMellinLeftDisk ∩
      reducedSphereMellinBridgeDisk).Nonempty := by
  refine ⟨(1 : Complex) / 5 + (1 : Complex) / 10 * Complex.I, ?_, ?_⟩
  · simp only [reducedSphereMellinLeftDisk, Metric.mem_ball]
    rw [Complex.dist_eq, Complex.norm_def]
    rw [← Real.sqrt_sq (by norm_num : (0 : Real) ≤ 1 / 3),
      Real.sqrt_lt_sqrt_iff (Complex.normSq_nonneg _)]
    norm_num [Complex.normSq_apply]
  · simp only [reducedSphereMellinBridgeDisk, Metric.mem_ball]
    rw [Complex.dist_eq, Complex.norm_def]
    rw [← Real.sqrt_sq (by norm_num : (0 : Real) ≤ 3 / 5),
      Real.sqrt_lt_sqrt_iff (Complex.normSq_nonneg _)]
    norm_num [Complex.normSq_apply]

private theorem bridge_seed_inter_nonempty :
    (reducedSphereMellinBridgeDisk ∩
      reducedSphereMellinSeedDisk).Nonempty := by
  refine ⟨(26 : Complex) / 25 + (3 : Complex) / 25 * Complex.I, ?_, ?_⟩
  · simp only [reducedSphereMellinBridgeDisk, Metric.mem_ball]
    rw [Complex.dist_eq, Complex.norm_def]
    rw [← Real.sqrt_sq (by norm_num : (0 : Real) ≤ 3 / 5),
      Real.sqrt_lt_sqrt_iff (Complex.normSq_nonneg _)]
    norm_num [Complex.normSq_apply]
  · simp only [reducedSphereMellinSeedDisk, Metric.mem_ball]
    rw [Complex.dist_eq, Complex.norm_def]
    rw [← Real.sqrt_sq (by norm_num : (0 : Real) ≤ 1 / 4),
      Real.sqrt_lt_sqrt_iff (Complex.normSq_nonneg _)]
    norm_num [Complex.normSq_apply]

private theorem left_lowerBridge_inter_nonempty :
    (reducedSphereMellinLeftDisk ∩
      reducedSphereMellinLowerBridgeDisk).Nonempty := by
  refine ⟨(1 : Complex) / 5 - (1 : Complex) / 10 * Complex.I, ?_, ?_⟩
  · simp only [reducedSphereMellinLeftDisk, Metric.mem_ball]
    rw [Complex.dist_eq, Complex.norm_def,
      ← Real.sqrt_sq (by norm_num : (0 : Real) ≤ 1 / 3),
      Real.sqrt_lt_sqrt_iff (Complex.normSq_nonneg _)]
    norm_num [Complex.normSq_apply]
  · simp only [reducedSphereMellinLowerBridgeDisk, Metric.mem_ball]
    rw [Complex.dist_eq, Complex.norm_def,
      ← Real.sqrt_sq (by norm_num : (0 : Real) ≤ 3 / 5),
      Real.sqrt_lt_sqrt_iff (Complex.normSq_nonneg _)]
    norm_num [Complex.normSq_apply]

theorem reducedSphereMellinConnectedDomain_isPreconnected :
    IsPreconnected reducedSphereMellinConnectedDomain := by
  have hLeftBridge : IsPreconnected
      (reducedSphereMellinLeftDisk ∪ reducedSphereMellinBridgeDisk) :=
    IsPreconnected.union' left_bridge_inter_nonempty
      (convex_ball (0 : Complex) ((1 : Real) / 3)).isPreconnected
      (convex_ball
        ((3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I)
        ((3 : Real) / 5)).isPreconnected
  have hLowerIntersection :
      ((reducedSphereMellinLeftDisk ∪ reducedSphereMellinBridgeDisk) ∩
        reducedSphereMellinLowerBridgeDisk).Nonempty := by
    exact left_lowerBridge_inter_nonempty.mono fun spectral hSpectral =>
      ⟨Or.inl hSpectral.1, hSpectral.2⟩
  have hThree : IsPreconnected
      ((reducedSphereMellinLeftDisk ∪ reducedSphereMellinBridgeDisk) ∪
        reducedSphereMellinLowerBridgeDisk) :=
    IsPreconnected.union' hLowerIntersection hLeftBridge
      (convex_ball
        ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I)
        ((3 : Real) / 5)).isPreconnected
  have hUnionIntersection :
      (((reducedSphereMellinLeftDisk ∪ reducedSphereMellinBridgeDisk) ∪
          reducedSphereMellinLowerBridgeDisk) ∩
        reducedSphereMellinSeedDisk).Nonempty := by
    exact bridge_seed_inter_nonempty.mono fun spectral hSpectral =>
      ⟨Or.inl (Or.inr hSpectral.1), hSpectral.2⟩
  exact IsPreconnected.union' hUnionIntersection hThree
    (convex_ball ((5 : Complex) / 4) ((1 : Real) / 4)).isPreconnected

@[simp]
theorem zero_mem_reducedSphereMellinConnectedDomain :
    (0 : Complex) ∈ reducedSphereMellinConnectedDomain := by
  left
  left
  simp [reducedSphereMellinLeftDisk]

@[simp]
theorem five_fourths_mem_reducedSphereMellinConnectedDomain :
    ((5 : Complex) / 4) ∈ reducedSphereMellinConnectedDomain := by
  right
  simp [reducedSphereMellinSeedDisk]

private theorem conj_upperBridgeCenter :
    conj ((3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I) =
      (3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I := by
  have hThree : (3 : Complex) / 5 = ((3 / 5 : Real) : Complex) := by
    norm_num
  have hHalf : (1 : Complex) / 2 = ((1 / 2 : Real) : Complex) := by
    norm_num
  rw [hThree, hHalf, map_add, map_mul, Complex.conj_I]
  simp only [Complex.conj_ofReal]
  ring

private theorem conj_lowerBridgeCenter :
    conj ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I) =
      (3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I := by
  have hThree : (3 : Complex) / 5 = ((3 / 5 : Real) : Complex) := by
    norm_num
  have hHalf : (1 : Complex) / 2 = ((1 / 2 : Real) : Complex) := by
    norm_num
  rw [hThree, hHalf, map_sub, map_mul, Complex.conj_I]
  simp only [Complex.conj_ofReal]
  ring

private theorem conj_seedCenter :
    conj ((5 : Complex) / 4) = (5 : Complex) / 4 := by
  have hSeed : (5 : Complex) / 4 = ((5 / 4 : Real) : Complex) := by
    norm_num
  rw [hSeed, Complex.conj_ofReal]

/-- The corridor is invariant under complex conjugation. -/
theorem conj_mem_reducedSphereMellinConnectedDomain
    (spectral : Complex)
    (hSpectral : spectral ∈ reducedSphereMellinConnectedDomain) :
    conj spectral ∈ reducedSphereMellinConnectedDomain := by
  rcases hSpectral with ((hLeft | hUpper) | hLower) | hSeed
  · exact Or.inl (Or.inl (Or.inl (by
      simp only [reducedSphereMellinLeftDisk, Metric.mem_ball] at hLeft ⊢
      calc
        dist (conj spectral) 0 = dist (conj spectral) (conj 0) := by simp
        _ = dist spectral 0 := Complex.dist_conj_conj _ _
        _ < (1 : Real) / 3 := hLeft)))
  · exact Or.inl (Or.inr (by
      simp only [reducedSphereMellinBridgeDisk, Metric.mem_ball] at hUpper
      simp only [reducedSphereMellinLowerBridgeDisk, Metric.mem_ball]
      calc
        dist (conj spectral)
            ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I) =
          dist (conj spectral)
            (conj ((3 : Complex) / 5 +
              (1 : Complex) / 2 * Complex.I)) := by
                rw [conj_upperBridgeCenter]
        _ = dist spectral
            ((3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I) :=
          Complex.dist_conj_conj _ _
        _ < (3 : Real) / 5 := hUpper))
  · exact Or.inl (Or.inl (Or.inr (by
      simp only [reducedSphereMellinLowerBridgeDisk, Metric.mem_ball] at hLower
      simp only [reducedSphereMellinBridgeDisk, Metric.mem_ball]
      calc
        dist (conj spectral)
            ((3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I) =
          dist (conj spectral)
            (conj ((3 : Complex) / 5 -
              (1 : Complex) / 2 * Complex.I)) := by
                rw [conj_lowerBridgeCenter]
        _ = dist spectral
            ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I) :=
          Complex.dist_conj_conj _ _
        _ < (3 : Real) / 5 := hLower)))
  · exact Or.inr (by
      simp only [reducedSphereMellinSeedDisk, Metric.mem_ball] at hSeed ⊢
      calc
        dist (conj spectral) ((5 : Complex) / 4) =
          dist (conj spectral) (conj ((5 : Complex) / 4)) := by
            rw [conj_seedCenter]
        _ = dist spectral ((5 : Complex) / 4) := Complex.dist_conj_conj _ _
        _ < (1 : Real) / 4 := hSeed)

private theorem connectedDomain_re_lower {spectral : Complex}
    (hSpectral : spectral ∈ reducedSphereMellinConnectedDomain) :
    -(3 : Real) / 8 < spectral.re := by
  rcases hSpectral with ((hLeft | hBridge) | hLowerBridge) | hSeed
  · have hNorm : ‖spectral‖ < (1 : Real) / 3 := by
      simpa [reducedSphereMellinLeftDisk, Metric.mem_ball,
        dist_zero_right] using hLeft
    have hAbs := Complex.abs_re_le_norm spectral
    linarith [neg_le_abs spectral.re]
  · have hNorm :
        ‖spectral - ((3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I)‖ <
          (3 : Real) / 5 := by
      simpa [reducedSphereMellinBridgeDisk, Metric.mem_ball,
        Complex.dist_eq] using hBridge
    have hRe := Complex.abs_re_le_norm
      (spectral - ((3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I))
    have hLower : -(3 : Real) / 5 <
        (spectral - ((3 : Complex) / 5 +
          (1 : Complex) / 2 * Complex.I)).re := by
      linarith [neg_le_abs
        (spectral - ((3 : Complex) / 5 +
          (1 : Complex) / 2 * Complex.I)).re]
    norm_num at hLower ⊢
    linarith
  · have hNorm :
        ‖spectral - ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I)‖ <
          (3 : Real) / 5 := by
      have hDist : dist spectral
          ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I) <
          (3 : Real) / 5 := by
        simpa [reducedSphereMellinLowerBridgeDisk, Metric.mem_ball] using
          hLowerBridge
      rwa [Complex.dist_eq] at hDist
    have hLower : -(3 : Real) / 5 <
        (spectral - ((3 : Complex) / 5 -
          (1 : Complex) / 2 * Complex.I)).re := by
      have hRe := Complex.abs_re_le_norm
        (spectral - ((3 : Complex) / 5 -
          (1 : Complex) / 2 * Complex.I))
      linarith [neg_le_abs
        (spectral - ((3 : Complex) / 5 -
          (1 : Complex) / 2 * Complex.I)).re]
    norm_num at hLower ⊢
    linarith
  · have hNorm : ‖spectral - (5 : Complex) / 4‖ < (1 : Real) / 4 := by
      simpa [reducedSphereMellinSeedDisk, Metric.mem_ball,
        Complex.dist_eq] using hSeed
    have hLower : -(1 : Real) / 4 <
        (spectral - (5 : Complex) / 4).re := by
      have hRe := Complex.abs_re_le_norm
        (spectral - (5 : Complex) / 4)
      linarith [neg_le_abs (spectral - (5 : Complex) / 4).re]
    norm_num at hLower ⊢
    linarith

private theorem connectedDomain_re_upper {spectral : Complex}
    (hSpectral : spectral ∈ reducedSphereMellinConnectedDomain) :
    spectral.re < (13 : Real) / 8 := by
  rcases hSpectral with ((hLeft | hBridge) | hLowerBridge) | hSeed
  · have hNorm : ‖spectral‖ < (1 : Real) / 3 := by
      simpa [reducedSphereMellinLeftDisk, Metric.mem_ball,
        dist_zero_right] using hLeft
    exact (Complex.re_le_norm spectral).trans_lt (hNorm.trans (by norm_num))
  · have hNorm :
        ‖spectral - ((3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I)‖ <
          (3 : Real) / 5 := by
      simpa [reducedSphereMellinBridgeDisk, Metric.mem_ball,
        Complex.dist_eq] using hBridge
    have hUpper :
        (spectral - ((3 : Complex) / 5 +
          (1 : Complex) / 2 * Complex.I)).re < (3 : Real) / 5 :=
      (Complex.re_le_norm _).trans_lt hNorm
    norm_num at hUpper ⊢
    linarith
  · have hNorm :
        ‖spectral - ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I)‖ <
          (3 : Real) / 5 := by
      have hDist : dist spectral
          ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I) <
          (3 : Real) / 5 := by
        simpa [reducedSphereMellinLowerBridgeDisk, Metric.mem_ball] using
          hLowerBridge
      rwa [Complex.dist_eq] at hDist
    have hUpper :
        (spectral - ((3 : Complex) / 5 -
          (1 : Complex) / 2 * Complex.I)).re < (3 : Real) / 5 :=
      (Complex.re_le_norm _).trans_lt hNorm
    norm_num at hUpper ⊢
    linarith
  · have hNorm : ‖spectral - (5 : Complex) / 4‖ < (1 : Real) / 4 := by
      simpa [reducedSphereMellinSeedDisk, Metric.mem_ball,
        Complex.dist_eq] using hSeed
    have hUpper : (spectral - (5 : Complex) / 4).re < (1 : Real) / 4 :=
      (Complex.re_le_norm _).trans_lt hNorm
    norm_num at hUpper ⊢
    linarith

/-- A fixed exponential envelope for the long-time part throughout the
connected corridor and a surrounding open strip. -/
def reducedSphereMellinLongConnectedMajorant
    (data : ProductThroatSpectralData) (time : Real) : Real :=
  time ^ (2 : Real) *
    longTimeExponentialBound (reducedSphereLongTimeScale data)
      ((1 : Real) / 2) time

private theorem reducedSphereMellinLongConnectedMajorant_integrableOn
    (data : ProductThroatSpectralData) :
    IntegrableOn (reducedSphereMellinLongConnectedMajorant data)
      (Set.Ioi (1 : Real)) := by
  have hBase : IntegrableOn
      (fun time : Real =>
        time ^ (2 : Real) * Real.exp (-((1 : Real) / 2) * time))
      (Set.Ioi (0 : Real)) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (2 : Real)) (p := (1 : Real)) (b := (1 : Real) / 2)
        (by norm_num) (by norm_num) (by norm_num))
  unfold reducedSphereMellinLongConnectedMajorant longTimeExponentialBound
  have hScaled := IntegrableOn.mono_set
    (hBase.const_mul (reducedSphereLongTimeScale data))
    (show Set.Ioi (1 : Real) ⊆ Set.Ioi 0 by
      intro time hTime
      exact (by norm_num : (0 : Real) < 1).trans hTime)
  refine hScaled.congr ?_
  filter_upwards with time
  ring

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
      rw [show -(3 : Real) / 8 = -(1 : Real) / 2 + (1 : Real) / 8 by
        norm_num, Real.rpow_add hTime.1]
      ring
    _ ≤ time ^ (-(1 : Real) / 2) * 8 :=
      mul_le_mul_of_nonneg_left hLog.le
        (Real.rpow_nonneg hTime.1.le _)
    _ = 8 * time ^ (-(1 : Real) / 2) := by ring

private theorem long_log_power_bound {time : Real}
    (hTime : time ∈ Set.Ioi (1 : Real)) :
    time ^ ((13 : Real) / 8) * |Real.log time| ≤
      3 * time ^ (2 : Real) := by
  have hTimePos : 0 < time := (by norm_num : (0 : Real) < 1).trans hTime
  have hLogNonnegative : 0 ≤ Real.log time := Real.log_nonneg hTime.le
  have hLog := Real.log_le_rpow_div hTimePos.le
    (by norm_num : (0 : Real) < (3 : Real) / 8)
  rw [abs_of_nonneg hLogNonnegative]
  calc
    time ^ ((13 : Real) / 8) * Real.log time ≤
        time ^ ((13 : Real) / 8) *
          (time ^ ((3 : Real) / 8) / ((3 : Real) / 8)) :=
      mul_le_mul_of_nonneg_left hLog (Real.rpow_nonneg hTimePos.le _)
    _ = (8 / 3 : Real) * time ^ (2 : Real) := by
      rw [show (2 : Real) = 13 / 8 + 3 / 8 by norm_num,
        Real.rpow_add hTimePos]
      ring
    _ ≤ 3 * time ^ (2 : Real) := by
      gcongr
      norm_num

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

private theorem reducedSphereLongTrace_norm_le
    (data : ProductThroatSpectralData) {time : Real}
    (hTime : time ∈ Set.Ioi (1 : Real)) :
    ‖((positiveTimeTraceExtension
        (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex)‖ ≤
      longTimeExponentialBound (reducedSphereLongTimeScale data)
        ((1 : Real) / 2) time := by
  have hTimePos : 0 < time := (by norm_num : (0 : Real) < 1).trans hTime
  rw [Complex.norm_real]
  simpa [dimensionlessReducedSphereHeatTrace, dimensionlessSphereHeatTrace,
    hTimePos] using reducedSphereLogTrace_le_longTimeExponential data hTime

private theorem short_integrand_norm_le
    (data : ProductThroatSpectralData) {spectral : Complex} {time : Real}
    (hSpectral : -(3 : Real) / 8 < spectral.re)
    (hTime : time ∈ Set.Ioc (0 : Real) 1) :
    ‖(time : Complex) ^ spectral *
        (((positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time -
          reducedSphereCounterterm data time) / time : Real) : Complex)‖ ≤
      reducedSphereMellinShortGermMajorant data time := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hTime.1]
  have hPower : time ^ spectral.re ≤ time ^ (-(1 : Real) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hTime.1 hTime.2 (by linarith)
  have hRemainder := reducedSphereShortRemainder_norm_le data hTime
  have hNonnegative : 0 ≤ sphereShortTimeMajorant data time :=
    (norm_nonneg _).trans hRemainder
  calc
    time ^ spectral.re *
          ‖(((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time -
            reducedSphereCounterterm data time) / time : Real) : Complex)‖ ≤
        time ^ spectral.re * sphereShortTimeMajorant data time :=
      mul_le_mul_of_nonneg_left hRemainder
        (Real.rpow_nonneg hTime.1.le _)
    _ ≤ time ^ (-(1 : Real) / 2) * sphereShortTimeMajorant data time :=
      mul_le_mul_of_nonneg_right hPower hNonnegative
    _ = reducedSphereMellinShortGermMajorant data time := rfl

private theorem long_integrand_norm_le
    (data : ProductThroatSpectralData) {spectral : Complex} {time : Real}
    (hSpectral : spectral.re < (13 : Real) / 8)
    (hTime : time ∈ Set.Ioi (1 : Real)) :
    ‖(time : Complex) ^ spectral *
        ((positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex)‖ ≤
      reducedSphereMellinLongConnectedMajorant data time := by
  have hTimePos : 0 < time := (by norm_num : (0 : Real) < 1).trans hTime
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hTimePos]
  have hPower : time ^ spectral.re ≤ time ^ (2 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hTime.le (by linarith)
  have hTrace := reducedSphereLongTrace_norm_le data hTime
  have hNonnegative :
      0 ≤ longTimeExponentialBound (reducedSphereLongTimeScale data)
        ((1 : Real) / 2) time := (norm_nonneg _).trans hTrace
  calc
    time ^ spectral.re *
          ‖((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex)‖ ≤
        time ^ spectral.re *
          longTimeExponentialBound (reducedSphereLongTimeScale data)
            ((1 : Real) / 2) time :=
      mul_le_mul_of_nonneg_left hTrace
        (Real.rpow_nonneg hTimePos.le _)
    _ ≤ time ^ (2 : Real) *
          longTimeExponentialBound (reducedSphereLongTimeScale data)
            ((1 : Real) / 2) time :=
      mul_le_mul_of_nonneg_right hPower hNonnegative
    _ = reducedSphereMellinLongConnectedMajorant data time := rfl

private theorem short_derivative_norm_le
    (data : ProductThroatSpectralData) {spectral : Complex} {time : Real}
    (hSpectral : -(3 : Real) / 8 < spectral.re)
    (hTime : time ∈ Set.Ioc (0 : Real) 1) :
    ‖reducedSphereMellinShortDerivativeIntegrand data spectral time‖ ≤
      8 * reducedSphereMellinShortGermMajorant data time := by
  have hPower : time ^ spectral.re ≤ time ^ (-(3 : Real) / 8) :=
    Real.rpow_le_rpow_of_exponent_ge hTime.1 hTime.2 hSpectral.le
  have hRemainder := reducedSphereShortRemainder_norm_le data hTime
  have hRemainderNonnegative : 0 ≤ sphereShortTimeMajorant data time :=
    (norm_nonneg _).trans hRemainder
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
        (mul_nonneg (Real.rpow_nonneg hTime.1.le _) (abs_nonneg _))
    _ ≤ time ^ (-(3 : Real) / 8) * |Real.log time| *
          sphereShortTimeMajorant data time :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hPower (abs_nonneg _))
        hRemainderNonnegative
    _ ≤ (8 * time ^ (-(1 : Real) / 2)) *
          sphereShortTimeMajorant data time :=
      mul_le_mul_of_nonneg_right (short_log_power_bound hTime)
        hRemainderNonnegative
    _ = 8 * reducedSphereMellinShortGermMajorant data time := by
      unfold reducedSphereMellinShortGermMajorant
      ring

private theorem long_derivative_norm_le
    (data : ProductThroatSpectralData) {spectral : Complex} {time : Real}
    (hSpectral : spectral.re < (13 : Real) / 8)
    (hTime : time ∈ Set.Ioi (1 : Real)) :
    ‖reducedSphereMellinLongDerivativeIntegrand data spectral time‖ ≤
      3 * reducedSphereMellinLongConnectedMajorant data time := by
  have hTimePos : 0 < time := (by norm_num : (0 : Real) < 1).trans hTime
  have hPower : time ^ spectral.re ≤ time ^ ((13 : Real) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hTime.le hSpectral.le
  have hTrace := reducedSphereLongTrace_norm_le data hTime
  have hNonnegative :
      0 ≤ longTimeExponentialBound (reducedSphereLongTimeScale data)
        ((1 : Real) / 2) time := (norm_nonneg _).trans hTrace
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
        (mul_nonneg (Real.rpow_nonneg hTimePos.le _) (abs_nonneg _))
    _ ≤ time ^ ((13 : Real) / 8) * |Real.log time| *
          longTimeExponentialBound (reducedSphereLongTimeScale data)
            ((1 : Real) / 2) time :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hPower (abs_nonneg _)) hNonnegative
    _ ≤ (3 * time ^ (2 : Real)) *
          longTimeExponentialBound (reducedSphereLongTimeScale data)
            ((1 : Real) / 2) time :=
      mul_le_mul_of_nonneg_right (long_log_power_bound hTime) hNonnegative
    _ = 3 * reducedSphereMellinLongConnectedMajorant data time := by
      unfold reducedSphereMellinLongConnectedMajorant
      ring

private theorem short_integrand_aestronglyMeasurable
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

private theorem long_integrand_aestronglyMeasurable
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
        (Or.inr (((by norm_num : (0 : Real) < 1).trans hTime).ne'))
  have hTail : AEStronglyMeasurable
      (fun time : Real =>
        ((positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex))
      (volume.restrict (Set.Ioi (1 : Real))) :=
    (positiveTimeReducedSphere_longTimeIntegrable data).ofReal.aestronglyMeasurable
  exact hPower.mul hTail

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

private theorem short_derivative_aestronglyMeasurable
    (data : ProductThroatSpectralData) (spectral : Complex) :
    AEStronglyMeasurable
      (reducedSphereMellinShortDerivativeIntegrand data spectral)
      (volume.restrict (Set.Ioc (0 : Real) 1)) := by
  refine ((short_integrand_aestronglyMeasurable data spectral).mul
    complexLogOfReal_aestronglyMeasurable_Ioc).congr
      (Filter.Eventually.of_forall fun time => ?_)
  simp only [reducedSphereMellinShortDerivativeIntegrand, Pi.mul_apply]
  ring

private theorem long_derivative_aestronglyMeasurable
    (data : ProductThroatSpectralData) (spectral : Complex) :
    AEStronglyMeasurable
      (reducedSphereMellinLongDerivativeIntegrand data spectral)
      (volume.restrict (Set.Ioi (1 : Real))) := by
  refine ((long_integrand_aestronglyMeasurable data spectral).mul
    complexLogOfReal_aestronglyMeasurable_Ioi).congr
      (Filter.Eventually.of_forall fun time => ?_)
  simp only [reducedSphereMellinLongDerivativeIntegrand, Pi.mul_apply]
  ring

private theorem short_hasDerivAt
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

private theorem long_hasDerivAt
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

private theorem short_integrableOn_connectedStrip
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hSpectral : -(3 : Real) / 8 < spectral.re) :
    IntegrableOn
      (fun time : Real =>
        (time : Complex) ^ spectral *
          (((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time -
            reducedSphereCounterterm data time) / time : Real) : Complex))
      (Set.Ioc (0 : Real) 1) := by
  refine (reducedSphereMellinShortGermMajorant_integrableOn data).mono'
    (short_integrand_aestronglyMeasurable data spectral) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
  exact short_integrand_norm_le data hSpectral hTime

private theorem long_integrableOn_connectedStrip
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hSpectral : spectral.re < (13 : Real) / 8) :
    IntegrableOn
      (fun time : Real =>
        (time : Complex) ^ spectral *
          ((positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time / time : Real) : Complex))
      (Set.Ioi (1 : Real)) := by
  refine (reducedSphereMellinLongConnectedMajorant_integrableOn data).mono'
    (long_integrand_aestronglyMeasurable data spectral) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  exact long_integrand_norm_le data hSpectral hTime

private theorem reducedSphereMellinShortRemainderIntegral_hasDerivAt_connected
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hLower : -(3 : Real) / 8 < spectral.re)
    (hUpper : spectral.re < (13 : Real) / 8) :
    HasDerivAt (reducedSphereMellinShortRemainderIntegral data)
      (∫ time in Set.Ioc (0 : Real) 1,
        reducedSphereMellinShortDerivativeIntegrand data spectral time)
      spectral := by
  let strip : Set Complex :=
    {z : Complex | -(3 : Real) / 8 < z.re ∧ z.re < (13 : Real) / 8}
  have hOpen : IsOpen strip :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hMem : spectral ∈ strip := ⟨hLower, hUpper⟩
  unfold reducedSphereMellinShortRemainderIntegral
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioc (0 : Real) 1))
    (F' := reducedSphereMellinShortDerivativeIntegrand data)
    (bound := fun time => 8 * reducedSphereMellinShortGermMajorant data time)
    (s := strip) (hOpen.mem_nhds hMem) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun z => short_integrand_aestronglyMeasurable data z
  · exact short_integrableOn_connectedStrip data hLower
  · exact short_derivative_aestronglyMeasurable data spectral
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
    intro z hz
    exact short_derivative_norm_le data hz.1 hTime
  · exact (reducedSphereMellinShortGermMajorant_integrableOn data).const_mul 8
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
    intro z _
    exact short_hasDerivAt data z hTime

private theorem reducedSphereMellinLongTailIntegral_hasDerivAt_connected
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hLower : -(3 : Real) / 8 < spectral.re)
    (hUpper : spectral.re < (13 : Real) / 8) :
    HasDerivAt (reducedSphereMellinLongTailIntegral data)
      (∫ time in Set.Ioi (1 : Real),
        reducedSphereMellinLongDerivativeIntegrand data spectral time)
      spectral := by
  let strip : Set Complex :=
    {z : Complex | -(3 : Real) / 8 < z.re ∧ z.re < (13 : Real) / 8}
  have hOpen : IsOpen strip :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hMem : spectral ∈ strip := ⟨hLower, hUpper⟩
  unfold reducedSphereMellinLongTailIntegral
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (1 : Real)))
    (F' := reducedSphereMellinLongDerivativeIntegrand data)
    (bound := fun time => 3 * reducedSphereMellinLongConnectedMajorant data time)
    (s := strip) (hOpen.mem_nhds hMem) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun z => long_integrand_aestronglyMeasurable data z
  · exact long_integrableOn_connectedStrip data hUpper
  · exact long_derivative_aestronglyMeasurable data spectral
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    intro z hz
    exact long_derivative_norm_le data hz.2 hTime
  · exact (reducedSphereMellinLongConnectedMajorant_integrableOn data).const_mul 3
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    intro z _
    exact long_hasDerivAt data z hTime

private theorem reducedSphereMellinRegularRemainderIntegral_differentiableAt_connected
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hSpectral : spectral ∈ reducedSphereMellinConnectedDomain) :
    DifferentiableAt Complex
      (reducedSphereMellinRegularRemainderIntegral data) spectral := by
  have hLower := connectedDomain_re_lower hSpectral
  have hUpper := connectedDomain_re_upper hSpectral
  exact ((reducedSphereMellinShortRemainderIntegral_hasDerivAt_connected
      data hLower hUpper).add
    (reducedSphereMellinLongTailIntegral_hasDerivAt_connected
      data hLower hUpper)).differentiableAt

private theorem reducedSphereCountertermMellinZeta_differentiableAt_connected
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hSpectral : spectral ∈ reducedSphereMellinConnectedDomain) :
    DifferentiableAt Complex (reducedSphereCountertermMellinZeta data) spectral := by
  have hLower := connectedDomain_re_lower hSpectral
  have hOne : spectral ≠ 1 := by
    intro h
    subst spectral
    rcases hSpectral with ((hLeft | hBridge) | hLowerBridge) | hSeed
    · have hNorm : ‖(1 : Complex)‖ < (1 : Real) / 3 := by
        simpa [reducedSphereMellinLeftDisk, Metric.mem_ball,
          dist_zero_right] using hLeft
      norm_num at hNorm
    · have hNorm :
          ‖(1 : Complex) -
            ((3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I)‖ <
            (3 : Real) / 5 := by
        simpa [reducedSphereMellinBridgeDisk, Metric.mem_ball,
          Complex.dist_eq] using hBridge
      rw [Complex.norm_def] at hNorm
      have hSq :
          Complex.normSq ((1 : Complex) -
            ((3 : Complex) / 5 + (1 : Complex) / 2 * Complex.I)) =
            (41 : Real) / 100 := by
        norm_num [Complex.normSq_apply]
      rw [hSq] at hNorm
      have hReverse : (3 : Real) / 5 < Real.sqrt ((41 : Real) / 100) := by
        rw [← Real.sqrt_sq (by norm_num : (0 : Real) ≤ 3 / 5),
          Real.sqrt_lt_sqrt_iff (sq_nonneg ((3 : Real) / 5))]
        norm_num
      exact (not_lt_of_ge hReverse.le) hNorm
    · have hNorm :
          ‖(1 : Complex) -
            ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I)‖ <
            (3 : Real) / 5 := by
        have hDist : dist (1 : Complex)
            ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I) <
            (3 : Real) / 5 := by
          simpa [reducedSphereMellinLowerBridgeDisk, Metric.mem_ball] using
            hLowerBridge
        rwa [Complex.dist_eq] at hDist
      rw [Complex.norm_def] at hNorm
      have hSq :
          Complex.normSq ((1 : Complex) -
            ((3 : Complex) / 5 - (1 : Complex) / 2 * Complex.I)) =
            (41 : Real) / 100 := by
        norm_num [Complex.normSq_apply]
      rw [hSq] at hNorm
      have hReverse : (3 : Real) / 5 < Real.sqrt ((41 : Real) / 100) := by
        rw [← Real.sqrt_sq (by norm_num : (0 : Real) ≤ 3 / 5),
          Real.sqrt_lt_sqrt_iff (sq_nonneg ((3 : Real) / 5))]
        norm_num
      exact (not_lt_of_ge hReverse.le) hNorm
    · have hNorm : ‖(1 : Complex) - (5 : Complex) / 4‖ <
          (1 : Real) / 4 := by
        simpa [reducedSphereMellinSeedDisk, Metric.mem_ball,
          Complex.dist_eq] using hSeed
      norm_num at hNorm
  have hNegOne : spectral ≠ -1 := by
    intro h
    subst spectral
    norm_num at hLower
  unfold reducedSphereCountertermMellinZeta
  have hGamma : DifferentiableAt Complex
      (fun z : Complex => (Complex.Gamma (z + 1))⁻¹) spectral :=
    Complex.differentiable_one_div_Gamma.differentiableAt.comp spectral
      (differentiableAt_id.add_const (1 : Complex))
  have hSub : spectral - 1 ≠ 0 := sub_ne_zero.mpr hOne
  have hAdd : spectral + 1 ≠ 0 := by
    intro h
    exact hNegOne (add_eq_zero_iff_eq_neg.mp h)
  have hFirst : DifferentiableAt Complex
      (fun z : Complex => 2 / (z - 1)) spectral :=
    (differentiableAt_const (x := spectral) (2 : Complex)).div
      (differentiableAt_id.sub_const 1) hSub
  have hLinear : DifferentiableAt Complex
      (fun z : Complex =>
        (reducedSphereMellinLinearCoefficient data : Complex) / (z + 1))
      spectral :=
    (differentiableAt_const (x := spectral)
      (reducedSphereMellinLinearCoefficient data : Complex)).div
        (differentiableAt_id.add_const 1) hAdd
  exact hGamma.mul
    ((differentiableAt_const (x := spectral)
      (reducedSphereMellinConstantCoefficient data : Complex)).add
        (differentiableAt_id.mul (hFirst.add hLinear)))

theorem reducedSphereMellinZeta_differentiableOn_connectedDomain
    (data : ProductThroatSpectralData) :
    DifferentiableOn Complex (reducedSphereMellinZeta data)
      reducedSphereMellinConnectedDomain := by
  intro spectral hSpectral
  unfold reducedSphereMellinZeta reducedSphereMellinRegularRemainderZeta
  exact ((Complex.differentiable_one_div_Gamma.differentiableAt.mul
      (reducedSphereMellinRegularRemainderIntegral_differentiableAt_connected
        data hSpectral)).add
    (reducedSphereCountertermMellinZeta_differentiableAt_connected
      data hSpectral)).differentiableWithinAt

theorem reducedSphereMellinZeta_analyticOn_connectedDomain
    (data : ProductThroatSpectralData) :
    AnalyticOnNhd Complex (reducedSphereMellinZeta data)
      reducedSphereMellinConnectedDomain :=
  (reducedSphereMellinZeta_differentiableOn_connectedDomain data).analyticOnNhd
    reducedSphereMellinConnectedDomain_isOpen

/-- The concrete reduced-sphere continuation with one analytic component
containing both zero and a genuine spectral Mellin seed. -/
def reducedSphereMellinConnectedAnalyticContinuationData
    (data : ProductThroatSpectralData) :
    RelativeHeatMellinConnectedAnalyticContinuationData
      (reducedSphereMellinFinitePartData data) where
  continuation := reducedSphereMellinZetaContinuationData data
  domain := reducedSphereMellinConnectedDomain
  isOpen_domain := reducedSphereMellinConnectedDomain_isOpen
  isPreconnected_domain := reducedSphereMellinConnectedDomain_isPreconnected
  zero_mem_domain := zero_mem_reducedSphereMellinConnectedDomain
  seed := (5 : Complex) / 4
  seed_mem_domain := five_fourths_mem_reducedSphereMellinConnectedDomain
  seed_mem_mellinHalfPlane := by
    norm_num [reducedSphereMellinZetaContinuationData]
  zeta_analytic := reducedSphereMellinZeta_analyticOn_connectedDomain data

/-- Canonical Schwarz packet derived from connected analyticity and the
conjugation-invariant corridor. -/
def reducedSphereMellinCanonicalSchwarzReflectionData
    (data : ProductThroatSpectralData) :=
  toCanonicalSchwarzReflection
    (reducedSphereMellinConnectedAnalyticContinuationData data)
    conj_mem_reducedSphereMellinConnectedDomain

theorem reducedSphereMellinZeta_schwarz_gate
    (data : ProductThroatSpectralData) :
    Set.EqOn (reducedSphereMellinZeta data)
        (schwarzReflect (reducedSphereMellinZeta data))
        reducedSphereMellinConnectedDomain ∧
      (reducedSphereMellinZetaContinuationData data).derivativeAtZero.im = 0 := by
  exact relative_heat_mellin_connected_analytic_schwarz_gate
    (reducedSphereMellinConnectedAnalyticContinuationData data)
    conj_mem_reducedSphereMellinConnectedDomain

/-- On the part of the connected corridor lying in `1 < re s`, the analytic
function is exactly the convergent spectral Mellin transform. -/
theorem reducedSphereMellinZeta_eq_candidate_on_connectedDomain
    (data : ProductThroatSpectralData) (spectral : Complex)
    (_hDomain : spectral ∈ reducedSphereMellinConnectedDomain)
    (hSpectral : 1 < spectral.re) :
    reducedSphereMellinZeta data spectral =
      relativeHeatMellinZetaCandidate
        (dimensionlessReducedSphereHeatTrace data) spectral :=
  reducedSphereMellinZeta_eq_candidate data spectral hSpectral

/-- Public no-splice gate: the zero germ and the convergent spectral germ are
restrictions of the same analytic function on one preconnected open set. -/
theorem product_throat_sphere_mellin_connected_analytic_continuation_gate
    (data : ProductThroatSpectralData) :
    IsOpen reducedSphereMellinConnectedDomain ∧
      IsPreconnected reducedSphereMellinConnectedDomain ∧
      (0 : Complex) ∈ reducedSphereMellinConnectedDomain ∧
      ((5 : Complex) / 4) ∈ reducedSphereMellinConnectedDomain ∧
      AnalyticOnNhd Complex (reducedSphereMellinZeta data)
        reducedSphereMellinConnectedDomain ∧
      reducedSphereMellinZeta data =ᶠ[𝓝 ((5 : Complex) / 4)]
        relativeHeatMellinZetaCandidate
          (dimensionlessReducedSphereHeatTrace data) := by
  have hGate :=
    RelativeHeatMellinConnectedAnalyticContinuationData.relative_heat_mellin_connected_analytic_continuation_gate
    (reducedSphereMellinConnectedAnalyticContinuationData data)
  exact ⟨hGate.1, hGate.2.1, hGate.2.2.1, hGate.2.2.2.1,
    hGate.2.2.2.2.2.1, hGate.2.2.2.2.2.2.1⟩

end
end P0EFTJanusProgramPProductThroatSphereMellinConnectedAnalyticContinuation4D
end JanusFormal
