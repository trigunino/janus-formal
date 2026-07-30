import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalMetricJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSpatialConformalCurvatureAlgebra4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D

/-!
# Spatial conformal curvature jet

This gate differentiates the exact contracted conformal Christoffel correction
and propagates it through raw coordinate Riemann, Ricci and scalar curvature.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSpatialConformalCurvatureJet4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusMappingTorusSpatialConformalMetricJet4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusMappingTorusSpatialConformalCurvatureAlgebra4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev Index4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4

private def coordinateBasisVector (index : Index4) : Vector4 :=
  Pi.single index 1

def localConformalChristoffelCorrectionDerivative
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative upper first second : Index4) : Real :=
  fderiv Real
      (fun current =>
        localConformalChristoffelCorrection period hPeriod scale patch current
          upper first second)
      coordinate (coordinateBasisVector derivative)

theorem localConformalChristoffelCorrection_contDiff
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (upper first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localConformalChristoffelCorrection period hPeriod scale patch coordinate
        upper first second) := by
  rw [show
    (fun coordinate =>
      localConformalChristoffelCorrection period hPeriod scale patch coordinate
        upper first second) =
      fun coordinate =>
        localLeviCivitaChristoffel period hPeriod
            (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
            patch coordinate upper first second -
          localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate upper first second by
    funext coordinate
    rw [localLeviCivitaChristoffel_conformal_eq_add_correction]
    ring]
  exact
    (localLeviCivitaChristoffel_contDiff period hPeriod
      (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
      patch upper first second).sub
      (localLeviCivitaChristoffel_contDiff period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch upper first second)

theorem localChristoffelDerivative_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative upper first second : Index4) :
    localChristoffelDerivative period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate derivative upper first second =
      localChristoffelDerivative period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate derivative upper first second +
        localConformalChristoffelCorrectionDerivative
          period hPeriod scale patch coordinate derivative upper first second := by
  unfold localChristoffelDerivative
    localConformalChristoffelCorrectionDerivative
  rw [show
    (fun current =>
      localLeviCivitaChristoffel period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch current upper first second) =
      fun current =>
        localLeviCivitaChristoffel period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch current upper first second +
          localConformalChristoffelCorrection period hPeriod scale patch current
            upper first second by
    funext current
    exact localLeviCivitaChristoffel_conformal_eq_add_correction
      period hPeriod scale hScale patch current upper first second]
  rw [show
    (fun current =>
      localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch current upper first second +
        localConformalChristoffelCorrection period hPeriod scale patch current
          upper first second) =
      (fun current =>
        localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch current upper first second) +
      (fun current =>
        localConformalChristoffelCorrection period hPeriod scale patch current
          upper first second) by rfl]
  rw [fderiv_add]
  · rfl
  · exact
      (localLeviCivitaChristoffel_contDiff period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch upper first second).differentiable (by simp) |>.differentiableAt
  · exact
      (localConformalChristoffelCorrection_contDiff
        period hPeriod scale hScale patch upper first second)
        |>.differentiable (by simp) |>.differentiableAt

def localConformalRiemannCorrection
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper lower first second : Index4) : Real :=
  localConformalChristoffelCorrectionDerivative
      period hPeriod scale patch coordinate first upper second lower -
    localConformalChristoffelCorrectionDerivative
      period hPeriod scale patch coordinate second upper first lower +
    ∑ contracted : Index4,
      (localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate upper first contracted *
        localConformalChristoffelCorrection period hPeriod scale patch coordinate
          contracted second lower +
       localConformalChristoffelCorrection period hPeriod scale patch coordinate
          upper first contracted *
        localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate contracted second lower +
       localConformalChristoffelCorrection period hPeriod scale patch coordinate
          upper first contracted *
        localConformalChristoffelCorrection period hPeriod scale patch coordinate
          contracted second lower) -
    ∑ contracted : Index4,
      (localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate upper second contracted *
        localConformalChristoffelCorrection period hPeriod scale patch coordinate
          contracted first lower +
       localConformalChristoffelCorrection period hPeriod scale patch coordinate
          upper second contracted *
        localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate contracted first lower +
       localConformalChristoffelCorrection period hPeriod scale patch coordinate
          upper second contracted *
        localConformalChristoffelCorrection period hPeriod scale patch coordinate
          contracted first lower)

theorem localRiemannCurvature_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper lower first second : Index4) :
    localRiemannCurvature period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate upper lower first second =
      localRiemannCurvature period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate upper lower first second +
        localConformalRiemannCorrection period hPeriod scale patch coordinate
          upper lower first second := by
  unfold localRiemannCurvature localConformalRiemannCorrection
  simp only [localChristoffelDerivative_conformal,
    localLeviCivitaChristoffel_conformal_eq_add_correction]
  simp_rw [mul_add, add_mul]
  simp only [Finset.sum_add_distrib]
  ring

theorem localConformalRiemannCorrection_contDiff
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (upper lower first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localConformalRiemannCorrection period hPeriod scale patch coordinate
        upper lower first second) := by
  rw [show
    (fun coordinate =>
      localConformalRiemannCorrection period hPeriod scale patch coordinate
        upper lower first second) =
      fun coordinate =>
        localRiemannCurvature period hPeriod
            (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
            patch coordinate upper lower first second -
          localRiemannCurvature period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate upper lower first second by
    funext coordinate
    rw [localRiemannCurvature_conformal]
    ring]
  exact
    (localRiemannCurvature_contDiff period hPeriod
      (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
      patch upper lower first second).sub
      (localRiemannCurvature_contDiff period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch upper lower first second)

def localConformalRicciCorrection
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) : Real :=
  ∑ contracted : Index4,
    localConformalRiemannCorrection period hPeriod scale patch coordinate
      contracted first contracted second

def localConformalQuadraticRicciCorrection
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) : Real :=
  ∑ contracted : Index4,
    ((∑ auxiliary : Index4,
      localConformalChristoffelCorrection period hPeriod scale patch coordinate
          contracted contracted auxiliary *
        localConformalChristoffelCorrection period hPeriod scale patch coordinate
          auxiliary second first) -
      ∑ auxiliary : Index4,
        localConformalChristoffelCorrection period hPeriod scale patch coordinate
            contracted second auxiliary *
          localConformalChristoffelCorrection period hPeriod scale patch coordinate
            auxiliary contracted first)

theorem localConformalQuadraticRicciCorrection_normal_form
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) :
    localConformalQuadraticRicciCorrection
        period hPeriod scale patch coordinate first second =
      2 *
        (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) ^ 2 *
        (localScalarGradient period hPeriod scale patch coordinate first *
            localScalarGradient period hPeriod scale patch coordinate second -
          localMetricCoefficient period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch first second coordinate *
            ∑ index : Index4,
              localScalarGradient period hPeriod scale patch coordinate index *
                localSmoothScalarRaisedGradient period hPeriod
                  (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                  patch scale coordinate index) := by
  unfold localConformalQuadraticRicciCorrection
  have hCorrection
      (upper lowerFirst lowerSecond : Index4) :
      localConformalChristoffelCorrection period hPeriod scale patch coordinate
          upper lowerFirst lowerSecond =
        conformalConnectionCorrection
          (1 / (2 * localScalarRepresentative
            period hPeriod scale patch coordinate))
          (localMetricMatrix period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)
          (localScalarGradient period hPeriod scale patch coordinate)
          (localSmoothScalarRaisedGradient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate)
          upper lowerFirst lowerSecond := by
    rw [localConformalChristoffelCorrection_normal_form]
    rfl
  simp_rw [hCorrection]
  apply conformalConnectionCorrection_quadraticRicci
  · exact
      (localFixedSignMetric period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate).metric_symmetric
  · intro lower
    let data :=
      localFixedSignMetric period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate
    have hContract :=
      inverseMetric_contract_metric data
        (localScalarGradient period hPeriod scale patch coordinate)
        lower
    calc
      _ = ∑ upper : Index4,
          localSmoothScalarRaisedGradient period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch scale coordinate upper *
            localMetricCoefficient period hPeriod
                (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                patch upper lower coordinate := by
          apply Finset.sum_congr rfl
          intro upper _
          change data.metric lower upper * _ = _ * data.metric upper lower
          rw [metric_entry_symmetric data lower upper]
          ring
      _ = _ := by
        simpa [data, localSmoothScalarRaisedGradient,
          covariantScalarJetRaisedGradient, localCovariantScalarJet,
          coordinateScalarJetNormalForm, localCoordinateScalarJet,
          localFixedSignMetric, localMetricMatrix,
          Matrix.mulVec, dotProduct] using hContract

def localConformalQuadraticScalarCorrection
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ first : Index4, ∑ second : Index4,
    (localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate)⁻¹ first second *
      localConformalQuadraticRicciCorrection
        period hPeriod scale patch coordinate first second

private theorem doubleSum_contract_rankOne_sub_trace
    (inverseMetric metric : Index4 → Index4 → Real)
    (gradient : Index4 → Real)
    (gradientSquare : Real)
    (hGradient :
      (∑ first : Index4, ∑ second : Index4,
        inverseMetric first second *
          (gradient first * gradient second)) = gradientSquare)
    (hTrace :
      (∑ first : Index4, ∑ second : Index4,
        inverseMetric first second * metric first second) = 4) :
    (∑ first : Index4, ∑ second : Index4,
      inverseMetric first second *
        (gradient first * gradient second -
          metric first second * gradientSquare)) =
      -3 * gradientSquare := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hGradient]
  have hMetricTerm :
      (∑ first : Index4, ∑ second : Index4,
        inverseMetric first second *
          (metric first second * gradientSquare)) =
        4 * gradientSquare := by
    rw [← hTrace]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro second _
    ring
  rw [hMetricTerm]
  ring

theorem localConformalQuadraticScalarCorrection_normal_form
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localConformalQuadraticScalarCorrection
        period hPeriod scale patch coordinate =
      -6 *
        (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) ^ 2 *
        covariantScalarGradientPairing
          (localFixedSignMetric period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate)
          (localCovariantScalarJet period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch scale coordinate) := by
  unfold localConformalQuadraticScalarCorrection
  simp_rw [localConformalQuadraticRicciCorrection_normal_form]
  rw [localScalarGradient_dot_raised_eq_pairing]
  have hContract :=
    doubleSum_contract_rankOne_sub_trace
      (fun first second =>
        (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ first second)
      (fun first second =>
        localMetricCoefficient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch first second coordinate)
      (localScalarGradient period hPeriod scale patch coordinate)
      (covariantScalarGradientPairing
        (localFixedSignMetric period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch scale coordinate)
        (localCovariantScalarJet period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch scale coordinate))
      (by
        unfold covariantScalarGradientPairing localFixedSignMetric
          localCovariantScalarJet coordinateScalarJetNormalForm
          localCoordinateScalarJet
        simp
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        ring)
      (intrinsicInverseMetric_trace_metric period hPeriod patch coordinate)
  have hFactor
      (factor : Real)
      (value : Index4 → Index4 → Real) :
      (∑ first : Index4, ∑ second : Index4,
        factor * value first second) =
        factor * ∑ first : Index4, ∑ second : Index4,
          value first second := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.mul_sum]
  calc
    _ = ∑ first : Index4, ∑ second : Index4,
        (2 * (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) ^ 2) *
          ((localMetricMatrix period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate)⁻¹ first second *
            (localScalarGradient period hPeriod scale patch coordinate first *
                localScalarGradient period hPeriod scale patch coordinate second -
              localMetricCoefficient period hPeriod
                  (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                  patch first second coordinate *
                covariantScalarGradientPairing
                  (localFixedSignMetric period hPeriod
                    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                    patch coordinate)
                  (localCovariantScalarJet period hPeriod
                    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                    patch scale coordinate)
                  (localCovariantScalarJet period hPeriod
                    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                    patch scale coordinate))) := by
          apply Finset.sum_congr rfl
          intro first _
          apply Finset.sum_congr rfl
          intro second _
          ring
    _ = _ := by
      rw [hFactor, hContract]
      ring

def localStandardConformalLinearScalarCorrection
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  let metric :=
    localFixedSignMetric period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate
  let jet :=
    localCovariantScalarJet period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch scale coordinate
  (-3 * (localScalarRepresentative period hPeriod scale patch coordinate)⁻¹ *
        covariantScalarJetWave metric jet +
      3 * (localScalarRepresentative period hPeriod scale patch coordinate)⁻¹ ^ 2 *
        covariantScalarGradientPairing metric jet jet)

theorem localRicciCurvature_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (first second : Index4) :
    localRicciCurvature period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate first second =
      localRicciCurvature period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate first second +
        localConformalRicciCorrection period hPeriod scale patch coordinate
          first second := by
  unfold localRicciCurvature localConformalRicciCorrection
  simp only [localRiemannCurvature_conformal, Finset.sum_add_distrib]

theorem localConformalRicciCorrection_contDiff
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞ (fun coordinate =>
      localConformalRicciCorrection period hPeriod scale patch coordinate
        first second) := by
  rw [show
    (fun coordinate =>
      localConformalRicciCorrection period hPeriod scale patch coordinate
        first second) =
      fun coordinate =>
        localRicciCurvature period hPeriod
            (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
            patch coordinate first second -
          localRicciCurvature period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate first second by
    funext coordinate
    rw [localRicciCurvature_conformal]
    ring]
  exact
    (localRicciCurvature_contDiff period hPeriod
      (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
      patch first second).sub
      (localRicciCurvature_contDiff period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch first second)

private theorem doubleSum_scale_mul_add
    (scalar : Real)
    (coefficient firstTerm secondTerm : Index4 → Index4 → Real) :
    (∑ first, ∑ second,
      scalar * coefficient first second *
        (firstTerm first second + secondTerm first second)) =
      scalar *
        ((∑ first, ∑ second,
            coefficient first second * firstTerm first second) +
          ∑ first, ∑ second,
            coefficient first second * secondTerm first second) := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring

def localConformalScalarCurvatureCorrection
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  ∑ first : Index4, ∑ second : Index4,
    (localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate)⁻¹ first second *
      localConformalRicciCorrection period hPeriod scale patch coordinate
        first second

theorem localScalarCurvature_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarCurvature period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate =
      (localScalarRepresentative period hPeriod scale patch coordinate)⁻¹ *
        (localScalarCurvature period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate +
          localConformalScalarCurvatureCorrection
            period hPeriod scale patch coordinate) := by
  unfold localScalarCurvature localConformalScalarCurvatureCorrection
  rw [localConformalMetricInverse]
  simp only [localRicciCurvature_conformal, Matrix.smul_apply, smul_eq_mul]
  apply doubleSum_scale_mul_add

theorem localConformalScalarCurvatureCorrection_contDiff
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (localConformalScalarCurvatureCorrection
        period hPeriod scale patch) := by
  rw [show
    localConformalScalarCurvatureCorrection period hPeriod scale patch =
      fun coordinate =>
        localScalarRepresentative period hPeriod scale patch coordinate *
            localScalarCurvature period hPeriod
              (conformalSmoothGeneralLorentzMetric
                period hPeriod scale hScale)
              patch coordinate -
          localScalarCurvature period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate by
    funext coordinate
    rw [localScalarCurvature_conformal]
    have hScaleNe :
        localScalarRepresentative period hPeriod scale patch coordinate ≠ 0 :=
      ne_of_gt (hScale (patch.coordinateMap coordinate))
    field_simp
    ring]
  exact
    ((localScalarRepresentative_contDiff period hPeriod scale patch).mul
      (localScalarCurvature_contDiff period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch)).sub
      (localScalarCurvature_contDiff period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)

def localStandardConformalScalarCurvatureCorrection
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Real :=
  let metric :=
    localFixedSignMetric period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate
  let jet :=
    localCovariantScalarJet period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch scale coordinate
  (-3 * (localScalarRepresentative period hPeriod scale patch coordinate)⁻¹ *
        covariantScalarJetWave metric jet +
      (3 / 2) *
        (localScalarRepresentative period hPeriod scale patch coordinate)⁻¹ ^ 2 *
        covariantScalarGradientPairing metric jet jet)

theorem localStandardConformalScalarCorrection_eq_linear_add_quadratic
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localStandardConformalScalarCurvatureCorrection
        period hPeriod scale patch coordinate =
      localStandardConformalLinearScalarCorrection
          period hPeriod scale patch coordinate +
        localConformalQuadraticScalarCorrection
          period hPeriod scale patch coordinate := by
  rw [localConformalQuadraticScalarCorrection_normal_form]
  unfold localStandardConformalScalarCurvatureCorrection
    localStandardConformalLinearScalarCorrection
  dsimp only
  have hScaleNe :
      localScalarRepresentative period hPeriod scale patch coordinate ≠ 0 :=
    ne_of_gt (hScale (patch.coordinateMap coordinate))
  field_simp
  ring

theorem localScalarCurvature_conformal_standard_iff
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarCurvature period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate =
      (localScalarRepresentative period hPeriod scale patch coordinate)⁻¹ *
        (localScalarCurvature period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate +
          localStandardConformalScalarCurvatureCorrection
            period hPeriod scale patch coordinate) ↔
      localConformalScalarCurvatureCorrection
          period hPeriod scale patch coordinate =
        localStandardConformalScalarCurvatureCorrection
          period hPeriod scale patch coordinate := by
  rw [localScalarCurvature_conformal]
  have hScaleNe :
      localScalarRepresentative period hPeriod scale patch coordinate ≠ 0 :=
    ne_of_gt (hScale (patch.coordinateMap coordinate))
  constructor <;> intro h
  · apply (add_left_cancel
      (a := localScalarCurvature period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate))
    apply (mul_left_cancel₀ hScaleNe)
    simpa [mul_assoc] using h
  · rw [h]

end

end P0EFTJanusMappingTorusSpatialConformalCurvatureJet4D
end JanusFormal
