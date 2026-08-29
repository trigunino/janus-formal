import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D

/-!
# Local jet of a spatially varying conformal metric

The existing intrinsic conformal construction already supplies a genuine
Lorentz metric for every positive smooth scalar factor.  This gate identifies
its local coefficient matrix, inverse, first coordinate derivative and exact
contracted Christoffel transformation. Curvature transformation laws remain
separate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSpatialConformalMetricJet4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusScalarStressLeviCivitaConnectionJet4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev ScalarIndex4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4

theorem localConformalMetricCoefficient
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : ScalarIndex4)
    (coordinate : Vector4) :
    localMetricCoefficient period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch first second coordinate =
      localScalarRepresentative period hPeriod scale patch coordinate *
        localMetricCoefficient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch first second coordinate :=
  rfl

theorem localConformalMetricMatrix
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localMetricMatrix period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate =
      localScalarRepresentative period hPeriod scale patch coordinate •
        localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate := by
  ext first second
  rfl

theorem localConformalMetricInverse
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (localMetricMatrix period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate)⁻¹ =
      (localScalarRepresentative period hPeriod scale patch coordinate)⁻¹ •
        (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ := by
  rw [localConformalMetricMatrix]
  let currentScale :=
    localScalarRepresentative period hPeriod scale patch coordinate
  have hCurrentScale : currentScale ≠ 0 :=
    ne_of_gt (hScale (patch.coordinateMap coordinate))
  letI : Invertible currentScale := invertibleOfNonzero hCurrentScale
  change (currentScale •
      localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate)⁻¹ =
    currentScale⁻¹ •
      (localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate)⁻¹
  have hUnit : IsUnit
      (localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate).det :=
    isUnit_iff_ne_zero.mpr
      (localMetricMatrix_det_ne_zero period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)
  calc
    _ = ⅟currentScale •
        (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ :=
      Matrix.inv_smul
        (A := localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)
        currentScale hUnit
    _ = _ := by rw [invOf_eq_inv]

theorem localConformalMetricDerivative
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (derivative first second : ScalarIndex4) :
    localMetricDerivative period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate derivative first second =
      localScalarGradient period hPeriod scale patch coordinate derivative *
          localMetricCoefficient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch first second coordinate +
        localScalarRepresentative period hPeriod scale patch coordinate *
          localMetricDerivative period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate derivative first second := by
  unfold localMetricDerivative localScalarGradient
  rw [show
      localMetricCoefficient period hPeriod
          (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
          patch first second =
        localScalarRepresentative period hPeriod scale patch *
          localMetricCoefficient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch first second by
      funext current
      exact localConformalMetricCoefficient period hPeriod
        scale hScale patch first second current]
  rw [fderiv_mul
    (((localScalarRepresentative_contDiff period hPeriod scale patch)
      |>.differentiable (by simp)).differentiableAt)
    (((localMetricCoefficient_contDiff period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch first second).differentiable (by simp)).differentiableAt)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change _ =
    (fderiv Real
        (localScalarRepresentative period hPeriod scale patch) coordinate)
          (Pi.single derivative 1) *
        localMetricCoefficient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch first second coordinate +
      localScalarRepresentative period hPeriod scale patch coordinate *
        (fderiv Real
          (localMetricCoefficient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch first second) coordinate) (Pi.single derivative 1)
  ring

/-- Contracted coordinate correction to the local Christoffel coefficients. -/
def localConformalChristoffelCorrection
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper first second : ScalarIndex4) : Real :=
  ∑ contracted : ScalarIndex4,
    (localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate)⁻¹ upper contracted *
      ((1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) *
        (localScalarGradient period hPeriod scale patch coordinate first *
            localMetricCoefficient period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch second contracted coordinate +
          localScalarGradient period hPeriod scale patch coordinate second *
            localMetricCoefficient period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch first contracted coordinate -
          localScalarGradient period hPeriod scale patch coordinate contracted *
            localMetricCoefficient period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch first second coordinate))

theorem intrinsicInverse_contract_metric
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper second : ScalarIndex4) :
    (∑ contracted : ScalarIndex4,
      (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ upper contracted *
        localMetricCoefficient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch second contracted coordinate) =
      if upper = second then 1 else 0 := by
  let metricMatrix :=
    localMetricMatrix period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate
  have hInverse :
      metricMatrix⁻¹ * metricMatrix = 1 :=
    Matrix.nonsing_inv_mul metricMatrix
      (isUnit_iff_ne_zero.mpr
        (localMetricMatrix_det_ne_zero period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate))
  have hEntry := congrArg (fun matrix => matrix upper second) hInverse
  simp only [Matrix.mul_apply, Matrix.one_apply] at hEntry
  rw [← hEntry]
  apply Finset.sum_congr rfl
  intro contracted _
  congr 1
  exact
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.symmetric
      (patch.coordinateMap coordinate)
      (patch.frame coordinate second)
      (patch.frame coordinate contracted)

theorem intrinsicInverseMetric_trace_metric
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (∑ first : ScalarIndex4, ∑ second : ScalarIndex4,
      (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ first second *
        localMetricCoefficient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch first second coordinate) = 4 := by
  apply Eq.trans
    (Finset.sum_congr rfl (fun first _ =>
      intrinsicInverse_contract_metric period hPeriod patch coordinate
        first first))
  simp

private theorem sum_conformalChristoffel_terms
    (factor firstGradient secondGradient metricCoefficient : Real)
    (inverseEntry secondMetric firstMetric gradient : ScalarIndex4 → Real) :
    (∑ contracted : ScalarIndex4,
      inverseEntry contracted *
        (factor *
          (firstGradient * secondMetric contracted +
            secondGradient * firstMetric contracted -
            gradient contracted * metricCoefficient))) =
      factor *
        (firstGradient *
            (∑ contracted : ScalarIndex4,
              inverseEntry contracted * secondMetric contracted) +
          secondGradient *
            (∑ contracted : ScalarIndex4,
              inverseEntry contracted * firstMetric contracted) -
          metricCoefficient *
            ∑ contracted : ScalarIndex4,
              inverseEntry contracted * gradient contracted) := by
  simp only [mul_add, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have hFirst :
      (∑ contracted : ScalarIndex4,
        inverseEntry contracted *
          (factor * (firstGradient * secondMetric contracted))) =
        factor *
          (firstGradient *
          ∑ contracted : ScalarIndex4,
            inverseEntry contracted * secondMetric contracted) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro contracted _
    ring
  have hSecond :
      (∑ contracted : ScalarIndex4,
        inverseEntry contracted *
          (factor * (secondGradient * firstMetric contracted))) =
        factor *
          (secondGradient *
          ∑ contracted : ScalarIndex4,
            inverseEntry contracted * firstMetric contracted) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro contracted _
    ring
  have hThird :
      (∑ contracted : ScalarIndex4,
        inverseEntry contracted *
          (factor * (gradient contracted * metricCoefficient))) =
        factor *
          (metricCoefficient *
          ∑ contracted : ScalarIndex4,
            inverseEntry contracted * gradient contracted) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro contracted _
    ring
  rw [hFirst, hSecond, hThird]

theorem localConformalChristoffelCorrection_normal_form
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper first second : ScalarIndex4) :
    localConformalChristoffelCorrection period hPeriod scale patch coordinate
        upper first second =
      (1 / (2 * localScalarRepresentative
          period hPeriod scale patch coordinate)) *
        ((if upper = second then
            localScalarGradient period hPeriod scale patch coordinate first
          else 0) +
          (if upper = first then
            localScalarGradient period hPeriod scale patch coordinate second
          else 0) -
          localMetricCoefficient period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch first second coordinate *
            localSmoothScalarRaisedGradient period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch scale coordinate upper) := by
  unfold localConformalChristoffelCorrection localSmoothScalarRaisedGradient
    covariantScalarJetRaisedGradient localFixedSignMetric
    localCovariantScalarJet coordinateScalarJetNormalForm
    localCoordinateScalarJet Matrix.mulVec dotProduct
  rw [sum_conformalChristoffel_terms]
  rw [intrinsicInverse_contract_metric,
    intrinsicInverse_contract_metric]
  split_ifs <;> simp_all

def localConformalLogGradient
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (index : ScalarIndex4) : Real :=
  (1 / (2 * localScalarRepresentative
    period hPeriod scale patch coordinate)) *
      localScalarGradient period hPeriod scale patch coordinate index

def localConformalRaisedLogGradient
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper : ScalarIndex4) : Real :=
  ∑ contracted : ScalarIndex4,
    (localMetricMatrix period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate)⁻¹ upper contracted *
      localConformalLogGradient period hPeriod scale patch coordinate contracted

theorem localConformalRaisedLogGradient_eq
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper : ScalarIndex4) :
    localConformalRaisedLogGradient period hPeriod scale patch coordinate upper =
      (1 / (2 * localScalarRepresentative
        period hPeriod scale patch coordinate)) *
        localSmoothScalarRaisedGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch scale coordinate upper := by
  unfold localConformalRaisedLogGradient localConformalLogGradient
    localSmoothScalarRaisedGradient covariantScalarJetRaisedGradient
    localFixedSignMetric localCovariantScalarJet coordinateScalarJetNormalForm
    localCoordinateScalarJet Matrix.mulVec dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro contracted _
  ring

theorem localConformalChristoffelCorrection_log_normal_form
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper first second : ScalarIndex4) :
    localConformalChristoffelCorrection period hPeriod scale patch coordinate
        upper first second =
      (if upper = second then
          localConformalLogGradient period hPeriod scale patch coordinate first
        else 0) +
        (if upper = first then
          localConformalLogGradient period hPeriod scale patch coordinate second
        else 0) -
        localMetricCoefficient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch first second coordinate *
          localConformalRaisedLogGradient
            period hPeriod scale patch coordinate upper := by
  rw [localConformalChristoffelCorrection_normal_form,
    localConformalRaisedLogGradient_eq]
  unfold localConformalLogGradient
  split_ifs <;> simp_all <;> ring

theorem localConformalChristoffelCorrection_trace
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (second : ScalarIndex4) :
    (∑ contracted : ScalarIndex4,
      localConformalChristoffelCorrection period hPeriod scale patch coordinate
        contracted contracted second) =
      4 * localConformalLogGradient
        period hPeriod scale patch coordinate second := by
  simp_rw [localConformalChristoffelCorrection_log_normal_form]
  have hMetricContraction :=
    inverseMetric_contract_metric
      (localFixedSignMetric period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch coordinate)
      (fun index =>
        localConformalLogGradient period hPeriod scale patch coordinate index)
      second
  change
    (∑ upper : ScalarIndex4,
      (∑ lower : ScalarIndex4,
        (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ upper lower *
            localConformalLogGradient
              period hPeriod scale patch coordinate lower) *
        localMetricCoefficient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch upper second coordinate) =
      localConformalLogGradient
        period hPeriod scale patch coordinate second at hMetricContraction
  simp only [if_true, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show
    (∑ contracted : ScalarIndex4,
      localMetricCoefficient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch contracted second coordinate *
        localConformalRaisedLogGradient
          period hPeriod scale patch coordinate contracted) =
      localConformalLogGradient period hPeriod scale patch coordinate second by
    rw [← hMetricContraction]
    unfold localConformalRaisedLogGradient
    apply Finset.sum_congr rfl
    intro contracted _
    ring]
  simp

theorem localConformalChristoffelCorrection_inverse_trace
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper : ScalarIndex4) :
    (∑ first : ScalarIndex4, ∑ second : ScalarIndex4,
      (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ first second *
        localConformalChristoffelCorrection
          period hPeriod scale patch coordinate upper second first) =
      -2 * localConformalRaisedLogGradient
        period hPeriod scale patch coordinate upper := by
  simp_rw [localConformalChristoffelCorrection_log_normal_form]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have hFirst :
      (∑ first : ScalarIndex4, ∑ second : ScalarIndex4,
        (localMetricMatrix period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)⁻¹ first second *
          (if upper = first then
            localConformalLogGradient
              period hPeriod scale patch coordinate second
          else 0)) =
        localConformalRaisedLogGradient
          period hPeriod scale patch coordinate upper := by
    simp [localConformalRaisedLogGradient]
  have hSecond :
      (∑ first : ScalarIndex4, ∑ second : ScalarIndex4,
        (localMetricMatrix period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)⁻¹ first second *
          (if upper = second then
            localConformalLogGradient
              period hPeriod scale patch coordinate first
          else 0)) =
        localConformalRaisedLogGradient
          period hPeriod scale patch coordinate upper := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ first : ScalarIndex4, ∑ second : ScalarIndex4,
          (localMetricMatrix period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate)⁻¹ first second *
            (if upper = first then
              localConformalLogGradient
                period hPeriod scale patch coordinate second
            else 0) := by
              apply Finset.sum_congr rfl
              intro first _
              apply Finset.sum_congr rfl
              intro second _
              have hInverseSymmetric :
                  (localMetricMatrix period hPeriod
                      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                      patch coordinate)⁻¹ second first =
                    (localMetricMatrix period hPeriod
                      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                      patch coordinate)⁻¹ first second := by
                have hEntry := congrArg
                  (fun matrix =>
                    matrix second first)
                  (localFixedSignMetric period hPeriod
                    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                    patch coordinate).inverse_symmetric
                simpa [Matrix.transpose_apply, localFixedSignMetric] using hEntry.symm
              rw [hInverseSymmetric]
      _ = _ := hFirst
  have hMetric :
      (∑ first : ScalarIndex4, ∑ second : ScalarIndex4,
        (localMetricMatrix period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate)⁻¹ first second *
          (localMetricCoefficient period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch second first coordinate *
            localConformalRaisedLogGradient
              period hPeriod scale patch coordinate upper)) =
        4 * localConformalRaisedLogGradient
          period hPeriod scale patch coordinate upper := by
    rw [← intrinsicInverseMetric_trace_metric period hPeriod patch coordinate]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro second _
    have hSymmetric :
        localMetricCoefficient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch second first coordinate =
          localMetricCoefficient period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch first second coordinate :=
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.symmetric
        (patch.coordinateMap coordinate)
        (patch.frame coordinate second)
        (patch.frame coordinate first)
    rw [hSymmetric]
    ring
  rw [hFirst, hSecond, hMetric]
  ring

theorem localConformalLogGradient_pairing
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (∑ first : ScalarIndex4, ∑ second : ScalarIndex4,
      (localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate)⁻¹ first second *
        localConformalLogGradient period hPeriod scale patch coordinate first *
        localConformalLogGradient period hPeriod scale patch coordinate second) =
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
  unfold localConformalLogGradient covariantScalarGradientPairing
    localFixedSignMetric localCovariantScalarJet coordinateScalarJetNormalForm
    localCoordinateScalarJet
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem localScalarGradient_dot_raised_eq_pairing
    (scale : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (∑ index : ScalarIndex4,
      localScalarGradient period hPeriod scale patch coordinate index *
        localSmoothScalarRaisedGradient period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch scale coordinate index) =
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
  unfold localSmoothScalarRaisedGradient covariantScalarJetRaisedGradient
    covariantScalarGradientPairing localFixedSignMetric
    localCovariantScalarJet coordinateScalarJetNormalForm
    localCoordinateScalarJet Matrix.mulVec dotProduct
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

/-- Exact local Christoffel transformation for the spatially varying
conformal factor.  The correction is kept in contracted coordinate form so it
can be differentiated directly by the curvature gate. -/
theorem localLeviCivitaChristoffel_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper first second : ScalarIndex4) :
    localLeviCivitaChristoffel period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate upper first second =
      localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate upper first second +
        ∑ contracted : ScalarIndex4,
          (localMetricMatrix period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod)
              patch coordinate)⁻¹ upper contracted *
            ((1 / (2 * localScalarRepresentative
                period hPeriod scale patch coordinate)) *
              (localScalarGradient period hPeriod scale patch coordinate first *
                  localMetricCoefficient period hPeriod
                    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                    patch second contracted coordinate +
                localScalarGradient period hPeriod scale patch coordinate second *
                  localMetricCoefficient period hPeriod
                    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                    patch first contracted coordinate -
                localScalarGradient period hPeriod scale patch coordinate contracted *
                  localMetricCoefficient period hPeriod
                    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
                    patch first second coordinate)) := by
  unfold localLeviCivitaChristoffel leviCivitaChristoffel
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro contracted _
  simp only [localFixedSignMetric]
  rw [localConformalMetricInverse,
    localConformalMetricDerivative,
    localConformalMetricDerivative,
    localConformalMetricDerivative]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hScaleNonzero :
      localScalarRepresentative period hPeriod scale patch coordinate ≠ 0 :=
    ne_of_gt (hScale (patch.coordinateMap coordinate))
  have hCancel :
      localScalarRepresentative period hPeriod scale patch coordinate *
          (localScalarRepresentative period hPeriod scale patch coordinate)⁻¹ = 1 :=
    mul_inv_cancel₀ hScaleNonzero
  ring_nf
  rw [hCancel]
  ring

theorem localLeviCivitaChristoffel_conformal_eq_add_correction
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (upper first second : ScalarIndex4) :
    localLeviCivitaChristoffel period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate upper first second =
      localLeviCivitaChristoffel period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate upper first second +
        localConformalChristoffelCorrection period hPeriod scale patch coordinate
          upper first second := by
  exact localLeviCivitaChristoffel_conformal
    period hPeriod scale hScale patch coordinate upper first second

end

end P0EFTJanusMappingTorusSpatialConformalMetricJet4D
end JanusFormal
