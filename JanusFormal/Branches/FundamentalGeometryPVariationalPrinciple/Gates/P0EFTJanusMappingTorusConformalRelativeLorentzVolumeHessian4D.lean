import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolumeHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompactParametricIntegralC2

/-!
# Conformal line realization of the relative Lorentz-volume Hessian

Positive exponential conformal curves give genuine smooth Lorentz metrics for
every real parameter.  Their frame-free relative volume ratio is computed
exactly, differentiated twice, and related to the already globalized
volume-Hessian density.  The second derivative along the nonlinear
exponential curve is the Hessian on its velocity plus the first variation on
its acceleration.

For a fixed smooth scalar integrand, compactness of the quotient and the
existing parametric-integration lemma promote the same line to a genuine
`C²` real action curve.

This is a concrete conformal line.  It is not a topology or a Frechet chart on
the full space of smooth Lorentz metrics.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.Frobenius Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolumeHessian4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusCompactParametricIntegralC2

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Coord4 :=
  P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-! ## Exact conformal relative volume -/

theorem localMetricMatrix_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) :
    localMetricMatrix period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate =
      scale (patch.coordinateMap coordinate) •
        localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
          coordinate := by
  ext first second
  rfl

theorem localMetricVolumeFactor_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) :
    localMetricVolumeFactor period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate =
      scale (patch.coordinateMap coordinate) ^ 2 *
        localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
          coordinate := by
  unfold localMetricVolumeFactor
  rw [localMetricMatrix_conformal, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [abs_mul, abs_of_pos
    (pow_pos (hScale (patch.coordinateMap coordinate)) 4)]
  rw [show scale (patch.coordinateMap coordinate) ^ 4 =
      (scale (patch.coordinateMap coordinate) ^ 2) ^ 2 by ring,
    Real.sqrt_mul (sq_nonneg (scale (patch.coordinateMap coordinate) ^ 2)),
    Real.sqrt_sq (sq_nonneg (scale (patch.coordinateMap coordinate)))]

theorem localMetricVolumeRatio_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) :
    localMetricVolumeRatio period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        patch coordinate =
      scale (patch.coordinateMap coordinate) ^ 2 := by
  unfold localMetricVolumeRatio
  rw [localMetricVolumeFactor_conformal]
  exact mul_div_cancel_right₀ _
    (localMetricVolumeFactor_ne_zero period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch coordinate)

theorem globalMetricVolumeRatio_conformal
    (scale : SmoothScalarField period hPeriod)
    (hScale : ∀ point, 0 < scale point)
    (point : EffectiveQuotient period hPeriod) :
    globalMetricVolumeRatio period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        point =
      scale point ^ 2 := by
  let witness := selectedMetricVolumeRatioChart period hPeriod point
  change
    localMetricVolumeRatio period hPeriod
        (conformalSmoothGeneralLorentzMetric period hPeriod scale hScale)
        witness.patch witness.coordinate =
      scale point ^ 2
  rw [localMetricVolumeRatio_conformal, witness.coordinateMap_eq]

/-! ## Genuine positive exponential metric line -/

/-- Positive scalar exponential curve through `baseScale`. -/
def positiveConformalScaleCurve
    (baseScale direction : SmoothScalarField period hPeriod)
    (parameter : Real) : SmoothScalarField period hPeriod where
  toFun := fun point =>
    baseScale point * Real.exp (parameter * direction point)
  contMDiff_toFun :=
    baseScale.contMDiff_toFun.mul
      (Real.contDiff_exp.contMDiff.comp
        (contMDiff_const.mul direction.contMDiff_toFun))

theorem positiveConformalScaleCurve_pos
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    0 < positiveConformalScaleCurve
      period hPeriod baseScale direction parameter point :=
  mul_pos (hBaseScale point) (Real.exp_pos _)

theorem positiveConformalScaleCurve_hasDerivAt
    (baseScale direction : SmoothScalarField period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        positiveConformalScaleCurve
          period hPeriod baseScale direction varied point)
      (positiveConformalScaleCurve
          period hPeriod baseScale direction parameter point *
        direction point)
      parameter := by
  have hExponential :=
    ((hasDerivAt_id (x := parameter)).mul_const (direction point)).exp
  simpa [positiveConformalScaleCurve, mul_assoc] using
    hExponential.const_mul (baseScale point)

/-- Genuine smooth Lorentz metric at every point of the exponential line. -/
def conformalLorentzMetricCurve
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) :
    SmoothGeneralLorentzMetric period hPeriod :=
  conformalSmoothGeneralLorentzMetric period hPeriod
    (positiveConformalScaleCurve
      period hPeriod baseScale direction parameter)
    (positiveConformalScaleCurve_pos
      period hPeriod baseScale direction hBaseScale parameter)

@[simp]
theorem conformalLorentzMetricCurve_localMetricMatrix_apply
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point) (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) (first second : Fin 4) :
    localMetricMatrix period hPeriod
        (conformalLorentzMetricCurve period hPeriod baseScale direction
          hBaseScale parameter) patch coordinate first second =
      positiveConformalScaleCurve period hPeriod baseScale direction parameter
          (patch.coordinateMap coordinate) *
        localMetricMatrix period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod)
          patch coordinate first second := by
  unfold conformalLorentzMetricCurve
  rw [localMetricMatrix_conformal]
  rfl

/-- Every local metric coefficient has the expected conformal velocity. -/
theorem conformalLorentzMetricCurve_localMetricMatrix_hasDerivAt
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point) (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) (first second : Fin 4) :
    HasDerivAt
      (fun varied => localMetricMatrix period hPeriod
        (conformalLorentzMetricCurve period hPeriod baseScale direction
          hBaseScale varied) patch coordinate first second)
      (direction (patch.coordinateMap coordinate) *
        localMetricMatrix period hPeriod
          (conformalLorentzMetricCurve period hPeriod baseScale direction
            hBaseScale parameter) patch coordinate first second)
      parameter := by
  have hScale := positiveConformalScaleCurve_hasDerivAt
    period hPeriod baseScale direction parameter
      (patch.coordinateMap coordinate)
  have hEntry := hScale.mul_const
    (localMetricMatrix period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch coordinate first second)
  have hEntry' : HasDerivAt
      (fun varied =>
        positiveConformalScaleCurve period hPeriod baseScale direction varied
            (patch.coordinateMap coordinate) *
          localMetricMatrix period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate first second)
      (direction (patch.coordinateMap coordinate) *
        (positiveConformalScaleCurve period hPeriod baseScale direction parameter
            (patch.coordinateMap coordinate) *
          localMetricMatrix period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            patch coordinate first second))
      parameter := hEntry.congr_deriv (by ring)
  simpa only [conformalLorentzMetricCurve_localMetricMatrix_apply] using hEntry'

/-- The local coefficient velocity differentiates to the expected conformal
acceleration. -/
theorem conformalLorentzMetricCurve_localMetricMatrix_velocity_hasDerivAt
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point) (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Coord4) (first second : Fin 4) :
    HasDerivAt
      (fun varied => direction (patch.coordinateMap coordinate) *
        localMetricMatrix period hPeriod
          (conformalLorentzMetricCurve period hPeriod baseScale direction
            hBaseScale varied) patch coordinate first second)
      (direction (patch.coordinateMap coordinate) *
        (direction (patch.coordinateMap coordinate) *
          localMetricMatrix period hPeriod
            (conformalLorentzMetricCurve period hPeriod baseScale direction
              hBaseScale parameter) patch coordinate first second))
      parameter := by
  exact (conformalLorentzMetricCurve_localMetricMatrix_hasDerivAt
    period hPeriod baseScale direction hBaseScale parameter patch coordinate
      first second).const_mul (direction (patch.coordinateMap coordinate))

/-- Frame-free relative volume along the genuine conformal metric line. -/
def conformalRelativeVolumeRatioCurve
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  globalMetricVolumeRatio period hPeriod
    (conformalLorentzMetricCurve
      period hPeriod baseScale direction hBaseScale parameter)
    point

theorem conformalRelativeVolumeRatioCurve_eq
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    conformalRelativeVolumeRatioCurve
        period hPeriod baseScale direction hBaseScale parameter point =
      positiveConformalScaleCurve
        period hPeriod baseScale direction parameter point ^ 2 := by
  exact globalMetricVolumeRatio_conformal period hPeriod
    (positiveConformalScaleCurve
      period hPeriod baseScale direction parameter)
    (positiveConformalScaleCurve_pos
      period hPeriod baseScale direction hBaseScale parameter)
    point

/-- First parameter derivative of the conformal relative-volume ratio. -/
def conformalRelativeVolumeFirstDerivative
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  2 * direction point *
    conformalRelativeVolumeRatioCurve
      period hPeriod baseScale direction hBaseScale parameter point

/-- Second parameter derivative of the conformal relative-volume ratio. -/
def conformalRelativeVolumeSecondDerivative
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  4 * direction point ^ 2 *
    conformalRelativeVolumeRatioCurve
      period hPeriod baseScale direction hBaseScale parameter point

theorem conformalRelativeVolumeRatioCurve_hasDerivAt
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        conformalRelativeVolumeRatioCurve
          period hPeriod baseScale direction hBaseScale varied point)
      (conformalRelativeVolumeFirstDerivative
        period hPeriod baseScale direction hBaseScale parameter point)
      parameter := by
  rw [show
    (fun varied =>
      conformalRelativeVolumeRatioCurve
        period hPeriod baseScale direction hBaseScale varied point) =
      fun varied =>
        positiveConformalScaleCurve
          period hPeriod baseScale direction varied point ^ 2 by
    funext varied
    exact conformalRelativeVolumeRatioCurve_eq
      period hPeriod baseScale direction hBaseScale varied point]
  have hScale := positiveConformalScaleCurve_hasDerivAt
    period hPeriod baseScale direction parameter point
  refine (hScale.pow 2).congr_deriv ?_
  rw [conformalRelativeVolumeFirstDerivative,
    conformalRelativeVolumeRatioCurve_eq]
  ring

theorem conformalRelativeVolumeFirstDerivative_hasDerivAt
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        conformalRelativeVolumeFirstDerivative
          period hPeriod baseScale direction hBaseScale varied point)
      (conformalRelativeVolumeSecondDerivative
        period hPeriod baseScale direction hBaseScale parameter point)
      parameter := by
  have hRatio := conformalRelativeVolumeRatioCurve_hasDerivAt
    period hPeriod baseScale direction hBaseScale parameter point
  unfold conformalRelativeVolumeFirstDerivative
    conformalRelativeVolumeSecondDerivative at *
  have hDerivative :
      (2 * direction point) *
          (2 * direction point *
            conformalRelativeVolumeRatioCurve
              period hPeriod baseScale direction hBaseScale parameter point) =
        4 * direction point ^ 2 *
          conformalRelativeVolumeRatioCurve
            period hPeriod baseScale direction hBaseScale parameter point := by
    ring
  exact (hRatio.const_mul (2 * direction point)).congr_deriv hDerivative

/-! ## Identification with the frame-free Hessian density -/

/-- Fieldwise scalar multiplication is pointwise linear in the invariant
general-metric pairing. -/
theorem generalMetricTensorPairingAt_smoothBulkScalarSMul_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : SmoothScalarField period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric first
        (smoothBulkScalarSMulTensor
          period hPeriod scalar second) point =
      scalar point *
        generalMetricTensorPairingAt
          period hPeriod metric first second point := by
  have hValue :
      (smoothBulkScalarSMulTensor
          period hPeriod scalar second).tensor point =
        (smoothSymmetricTensorSMul
          period hPeriod (scalar point) second).tensor point := by
    apply ContinuousLinearMap.ext
    intro left
    apply ContinuousLinearMap.ext
    intro right
    rfl
  rw [generalMetricTensorPairingAt_congr_right_at
    period hPeriod metric first
      (smoothBulkScalarSMulTensor period hPeriod scalar second)
      (smoothSymmetricTensorSMul
        period hPeriod (scalar point) second) point hValue]
  exact generalMetricTensorPairingAt_smul_right
    period hPeriod metric (scalar point) first second point

theorem globalRelativeMetricVolumeTraceAt_smoothBulkScalarSMul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalRelativeMetricVolumeTraceAt period hPeriod metric
        (smoothBulkScalarSMulTensor
          period hPeriod scalar tensor) point =
      scalar point *
        globalRelativeMetricVolumeTraceAt
          period hPeriod metric tensor point := by
  unfold globalRelativeMetricVolumeTraceAt
  rw [generalMetricTensorPairingAt_symmetric
    period hPeriod metric
      (smoothBulkScalarSMulTensor period hPeriod scalar tensor)
      metric.tensor point]
  rw [generalMetricTensorPairingAt_smoothBulkScalarSMul_right]
  rw [generalMetricTensorPairingAt_symmetric
    period hPeriod metric metric.tensor tensor point]

/-- Genuine velocity tensor of the exponential conformal metric line. -/
def conformalMetricVelocityTensor
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  smoothBulkScalarSMulTensor period hPeriod direction
    (conformalLorentzMetricCurve
      period hPeriod baseScale direction hBaseScale parameter).tensor

/-- Genuine acceleration tensor of the exponential conformal metric line. -/
def conformalMetricAccelerationTensor
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  smoothBulkScalarSMulTensor period hPeriod direction
    (conformalMetricVelocityTensor
      period hPeriod baseScale direction hBaseScale parameter)

theorem conformalMetricVelocity_trace
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    globalRelativeMetricVolumeTraceAt period hPeriod
        (conformalLorentzMetricCurve
          period hPeriod baseScale direction hBaseScale parameter)
        (conformalMetricVelocityTensor
          period hPeriod baseScale direction hBaseScale parameter)
        point =
      4 * direction point := by
  rw [conformalMetricVelocityTensor,
    globalRelativeMetricVolumeTraceAt_smoothBulkScalarSMul]
  unfold globalRelativeMetricVolumeTraceAt
  rw [generalMetricTensorPairingAt_metric_self]
  ring

theorem conformalRelativeVolumeFirstDerivative_eq_firstVariationDensity_velocity
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    conformalRelativeVolumeFirstDerivative
        period hPeriod baseScale direction hBaseScale parameter point =
      globalRelativeMetricVolumeFirstVariationDensity period hPeriod
        (conformalLorentzMetricCurve
          period hPeriod baseScale direction hBaseScale parameter)
        (conformalMetricVelocityTensor
          period hPeriod baseScale direction hBaseScale parameter)
        point := by
  unfold globalRelativeMetricVolumeFirstVariationDensity
  rw [conformalMetricVelocity_trace]
  change
    2 * direction point *
        conformalRelativeVolumeRatioCurve
          period hPeriod baseScale direction hBaseScale parameter point =
      conformalRelativeVolumeRatioCurve
          period hPeriod baseScale direction hBaseScale parameter point *
        ((1 / 2 : Real) * (4 * direction point))
  ring

theorem conformalMetricVelocity_pairing_self
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod
        (conformalLorentzMetricCurve
          period hPeriod baseScale direction hBaseScale parameter)
        (conformalMetricVelocityTensor
          period hPeriod baseScale direction hBaseScale parameter)
        (conformalMetricVelocityTensor
          period hPeriod baseScale direction hBaseScale parameter)
        point =
      4 * direction point ^ 2 := by
  rw [conformalMetricVelocityTensor,
    generalMetricTensorPairingAt_smoothBulkScalarSMul_right]
  change direction point *
      globalRelativeMetricVolumeTraceAt period hPeriod
        (conformalLorentzMetricCurve
          period hPeriod baseScale direction hBaseScale parameter)
        (conformalMetricVelocityTensor
          period hPeriod baseScale direction hBaseScale parameter)
        point =
      4 * direction point ^ 2
  rw [conformalMetricVelocity_trace]
  ring

theorem conformalMetricAcceleration_trace
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    globalRelativeMetricVolumeTraceAt period hPeriod
        (conformalLorentzMetricCurve
          period hPeriod baseScale direction hBaseScale parameter)
        (conformalMetricAccelerationTensor
          period hPeriod baseScale direction hBaseScale parameter)
        point =
      4 * direction point ^ 2 := by
  rw [conformalMetricAccelerationTensor,
    globalRelativeMetricVolumeTraceAt_smoothBulkScalarSMul,
    conformalMetricVelocity_trace]
  ring

theorem globalRelativeMetricVolumeHessianDensity_conformal_velocity
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    globalRelativeMetricVolumeHessianDensity period hPeriod
        (conformalLorentzMetricCurve
          period hPeriod baseScale direction hBaseScale parameter)
        (conformalMetricVelocityTensor
          period hPeriod baseScale direction hBaseScale parameter)
        (conformalMetricVelocityTensor
          period hPeriod baseScale direction hBaseScale parameter)
        point =
      2 * direction point ^ 2 *
        conformalRelativeVolumeRatioCurve
          period hPeriod baseScale direction hBaseScale parameter point := by
  unfold globalRelativeMetricVolumeHessianDensity
  rw [conformalMetricVelocity_trace, conformalMetricVelocity_pairing_self]
  change
    conformalRelativeVolumeRatioCurve
        period hPeriod baseScale direction hBaseScale parameter point *
      ((1 / 4 : Real) *
          ((4 * direction point) * (4 * direction point)) -
        (1 / 2 : Real) * (4 * direction point ^ 2)) =
      2 * direction point ^ 2 *
        conformalRelativeVolumeRatioCurve
          period hPeriod baseScale direction hBaseScale parameter point
  ring

theorem globalRelativeMetricVolumeFirstVariationDensity_conformal_acceleration
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    globalRelativeMetricVolumeFirstVariationDensity period hPeriod
        (conformalLorentzMetricCurve
          period hPeriod baseScale direction hBaseScale parameter)
        (conformalMetricAccelerationTensor
          period hPeriod baseScale direction hBaseScale parameter)
        point =
      2 * direction point ^ 2 *
        conformalRelativeVolumeRatioCurve
          period hPeriod baseScale direction hBaseScale parameter point := by
  unfold globalRelativeMetricVolumeFirstVariationDensity
  rw [conformalMetricAcceleration_trace]
  change
    conformalRelativeVolumeRatioCurve
        period hPeriod baseScale direction hBaseScale parameter point *
      ((1 / 2 : Real) * (4 * direction point ^ 2)) =
      2 * direction point ^ 2 *
        conformalRelativeVolumeRatioCurve
          period hPeriod baseScale direction hBaseScale parameter point
  ring

/-- Chain-rule decomposition for the nonlinear exponential metric line:
the second derivative is the Hessian on the velocity plus the first
variation on the acceleration. -/
theorem conformalRelativeVolumeSecondDerivative_eq_hessian_add_acceleration
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    conformalRelativeVolumeSecondDerivative
        period hPeriod baseScale direction hBaseScale parameter point =
      globalRelativeMetricVolumeHessianDensity period hPeriod
          (conformalLorentzMetricCurve
            period hPeriod baseScale direction hBaseScale parameter)
          (conformalMetricVelocityTensor
            period hPeriod baseScale direction hBaseScale parameter)
          (conformalMetricVelocityTensor
            period hPeriod baseScale direction hBaseScale parameter)
          point +
        globalRelativeMetricVolumeFirstVariationDensity period hPeriod
          (conformalLorentzMetricCurve
            period hPeriod baseScale direction hBaseScale parameter)
          (conformalMetricAccelerationTensor
            period hPeriod baseScale direction hBaseScale parameter)
          point := by
  rw [globalRelativeMetricVolumeHessianDensity_conformal_velocity,
    globalRelativeMetricVolumeFirstVariationDensity_conformal_acceleration]
  unfold conformalRelativeVolumeSecondDerivative
  ring

/-! ## Integrated fixed-integrand action -/

/-- Reference-measure density of a fixed scalar integrand along the conformal
metric line. -/
def conformalRelativeVolumeActionDensity
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  conformalRelativeVolumeRatioCurve
      period hPeriod baseScale direction hBaseScale parameter point *
    integrand point

def conformalRelativeVolumeActionFirstDerivativeDensity
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  conformalRelativeVolumeFirstDerivative
      period hPeriod baseScale direction hBaseScale parameter point *
    integrand point

def conformalRelativeVolumeActionSecondDerivativeDensity
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) : Real :=
  conformalRelativeVolumeSecondDerivative
      period hPeriod baseScale direction hBaseScale parameter point *
    integrand point

/-- The actual fixed-integrand action against the varying Lorentz-volume
measure. -/
def conformalRelativeVolumeActionCurve
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) : Real :=
  ∫ point, integrand point
    ∂generalLorentzVolumeMeasure period hPeriod
      (conformalLorentzMetricCurve
        period hPeriod baseScale direction hBaseScale parameter)

def conformalRelativeVolumeActionFirstDerivativeCurve
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) : Real :=
  ∫ point,
    conformalRelativeVolumeActionFirstDerivativeDensity
      period hPeriod integrand baseScale direction hBaseScale parameter point
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

def conformalRelativeVolumeActionSecondDerivativeCurve
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) : Real :=
  ∫ point,
    conformalRelativeVolumeActionSecondDerivativeDensity
      period hPeriod integrand baseScale direction hBaseScale parameter point
    ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

theorem conformalRelativeVolumeActionCurve_eq_reference
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) :
    conformalRelativeVolumeActionCurve
        period hPeriod integrand baseScale direction hBaseScale parameter =
      ∫ point,
        conformalRelativeVolumeActionDensity
          period hPeriod integrand baseScale direction hBaseScale
            parameter point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  exact integral_generalLorentzVolumeMeasure_eq_reference period hPeriod
    (conformalLorentzMetricCurve
      period hPeriod baseScale direction hBaseScale parameter)
    integrand

theorem positiveConformalScaleCurve_uncurry_continuous
    (baseScale direction : SmoothScalarField period hPeriod) :
    Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        positiveConformalScaleCurve
          period hPeriod baseScale direction input.1 input.2) := by
  exact
    (baseScale.contMDiff_toFun.continuous.comp continuous_snd).mul
      (Real.continuous_exp.comp
        (continuous_fst.mul
          (direction.contMDiff_toFun.continuous.comp continuous_snd)))

theorem conformalRelativeVolumeRatioCurve_uncurry_continuous
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point) :
    Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        conformalRelativeVolumeRatioCurve
          period hPeriod baseScale direction hBaseScale input.1 input.2) := by
  rw [show
    (fun input : Real × EffectiveQuotient period hPeriod =>
      conformalRelativeVolumeRatioCurve
        period hPeriod baseScale direction hBaseScale input.1 input.2) =
      fun input =>
        positiveConformalScaleCurve
          period hPeriod baseScale direction input.1 input.2 ^ 2 by
    funext input
    exact conformalRelativeVolumeRatioCurve_eq
      period hPeriod baseScale direction hBaseScale input.1 input.2]
  exact
    (positiveConformalScaleCurve_uncurry_continuous
      period hPeriod baseScale direction).pow 2

theorem conformalRelativeVolumeFirstDerivative_uncurry_continuous
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point) :
    Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        conformalRelativeVolumeFirstDerivative
          period hPeriod baseScale direction hBaseScale input.1 input.2) := by
  unfold conformalRelativeVolumeFirstDerivative
  exact
    (continuous_const.mul
      (direction.contMDiff_toFun.continuous.comp continuous_snd)).mul
      (conformalRelativeVolumeRatioCurve_uncurry_continuous
        period hPeriod baseScale direction hBaseScale)

theorem conformalRelativeVolumeSecondDerivative_uncurry_continuous
    (baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point) :
    Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        conformalRelativeVolumeSecondDerivative
          period hPeriod baseScale direction hBaseScale input.1 input.2) := by
  unfold conformalRelativeVolumeSecondDerivative
  exact
    (continuous_const.mul
      ((direction.contMDiff_toFun.continuous.comp continuous_snd).pow 2)).mul
      (conformalRelativeVolumeRatioCurve_uncurry_continuous
        period hPeriod baseScale direction hBaseScale)

theorem conformalRelativeVolumeActionDensity_uncurry_continuous
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point) :
    Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        conformalRelativeVolumeActionDensity
          period hPeriod integrand baseScale direction hBaseScale
            input.1 input.2) := by
  exact
    (conformalRelativeVolumeRatioCurve_uncurry_continuous
      period hPeriod baseScale direction hBaseScale).mul
      (integrand.contMDiff_toFun.continuous.comp continuous_snd)

theorem conformalRelativeVolumeActionFirstDerivativeDensity_uncurry_continuous
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point) :
    Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        conformalRelativeVolumeActionFirstDerivativeDensity
          period hPeriod integrand baseScale direction hBaseScale
            input.1 input.2) := by
  exact
    (conformalRelativeVolumeFirstDerivative_uncurry_continuous
      period hPeriod baseScale direction hBaseScale).mul
      (integrand.contMDiff_toFun.continuous.comp continuous_snd)

theorem conformalRelativeVolumeActionSecondDerivativeDensity_uncurry_continuous
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point) :
    Continuous
      (fun input : Real × EffectiveQuotient period hPeriod =>
        conformalRelativeVolumeActionSecondDerivativeDensity
          period hPeriod integrand baseScale direction hBaseScale
            input.1 input.2) := by
  exact
    (conformalRelativeVolumeSecondDerivative_uncurry_continuous
      period hPeriod baseScale direction hBaseScale).mul
      (integrand.contMDiff_toFun.continuous.comp continuous_snd)

theorem conformalRelativeVolumeActionDensity_hasDerivAt
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        conformalRelativeVolumeActionDensity
          period hPeriod integrand baseScale direction hBaseScale
            varied point)
      (conformalRelativeVolumeActionFirstDerivativeDensity
        period hPeriod integrand baseScale direction hBaseScale
          parameter point)
      parameter := by
  exact
    (conformalRelativeVolumeRatioCurve_hasDerivAt
      period hPeriod baseScale direction hBaseScale parameter point).mul_const
      (integrand point)

theorem conformalRelativeVolumeActionFirstDerivativeDensity_hasDerivAt
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        conformalRelativeVolumeActionFirstDerivativeDensity
          period hPeriod integrand baseScale direction hBaseScale
            varied point)
      (conformalRelativeVolumeActionSecondDerivativeDensity
        period hPeriod integrand baseScale direction hBaseScale
          parameter point)
      parameter := by
  exact
    (conformalRelativeVolumeFirstDerivative_hasDerivAt
      period hPeriod baseScale direction hBaseScale parameter point).mul_const
      (integrand point)

theorem conformalRelativeVolumeActionCurve_hasDerivAt
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) :
    HasDerivAt
      (conformalRelativeVolumeActionCurve
        period hPeriod integrand baseScale direction hBaseScale)
      (conformalRelativeVolumeActionFirstDerivativeCurve
        period hPeriod integrand baseScale direction hBaseScale parameter)
      parameter := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  rw [show
    conformalRelativeVolumeActionCurve
        period hPeriod integrand baseScale direction hBaseScale =
      fun varied =>
        ∫ point,
          conformalRelativeVolumeActionDensity
            period hPeriod integrand baseScale direction hBaseScale
              varied point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod by
    funext varied
    exact conformalRelativeVolumeActionCurve_eq_reference
      period hPeriod integrand baseScale direction hBaseScale varied]
  exact hasDerivAt_integral_of_jointContinuous_compact
    (measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (density := conformalRelativeVolumeActionDensity
      period hPeriod integrand baseScale direction hBaseScale)
    (derivative := conformalRelativeVolumeActionFirstDerivativeDensity
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionDensity_uncurry_continuous
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionFirstDerivativeDensity_uncurry_continuous
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionDensity_hasDerivAt
      period hPeriod integrand baseScale direction hBaseScale)
    parameter

theorem conformalRelativeVolumeActionFirstDerivativeCurve_hasDerivAt
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) :
    HasDerivAt
      (conformalRelativeVolumeActionFirstDerivativeCurve
        period hPeriod integrand baseScale direction hBaseScale)
      (conformalRelativeVolumeActionSecondDerivativeCurve
        period hPeriod integrand baseScale direction hBaseScale parameter)
      parameter := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact hasDerivAt_integral_of_jointContinuous_compact
    (measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (density := conformalRelativeVolumeActionFirstDerivativeDensity
      period hPeriod integrand baseScale direction hBaseScale)
    (derivative := conformalRelativeVolumeActionSecondDerivativeDensity
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionFirstDerivativeDensity_uncurry_continuous
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionSecondDerivativeDensity_uncurry_continuous
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionFirstDerivativeDensity_hasDerivAt
      period hPeriod integrand baseScale direction hBaseScale)
    parameter

/-- The exact integrated second derivative is the integral of the frame-free
volume Hessian plus the acceleration correction. -/
theorem conformalRelativeVolumeActionSecondDerivativeCurve_eq_hessian_add_acceleration
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point)
    (parameter : Real) :
    conformalRelativeVolumeActionSecondDerivativeCurve
        period hPeriod integrand baseScale direction hBaseScale parameter =
      ∫ point,
        (globalRelativeMetricVolumeHessianDensity period hPeriod
            (conformalLorentzMetricCurve
              period hPeriod baseScale direction hBaseScale parameter)
            (conformalMetricVelocityTensor
              period hPeriod baseScale direction hBaseScale parameter)
            (conformalMetricVelocityTensor
              period hPeriod baseScale direction hBaseScale parameter)
            point +
          globalRelativeMetricVolumeFirstVariationDensity period hPeriod
            (conformalLorentzMetricCurve
              period hPeriod baseScale direction hBaseScale parameter)
            (conformalMetricAccelerationTensor
              period hPeriod baseScale direction hBaseScale parameter)
            point) *
          integrand point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold conformalRelativeVolumeActionSecondDerivativeCurve
    conformalRelativeVolumeActionSecondDerivativeDensity
  apply integral_congr_ae
  filter_upwards [] with point
  rw [conformalRelativeVolumeSecondDerivative_eq_hessian_add_acceleration]

theorem conformalRelativeVolumeActionCurve_contDiff_two
    (integrand baseScale direction : SmoothScalarField period hPeriod)
    (hBaseScale : ∀ point, 0 < baseScale point) :
    ContDiff Real 2
      (conformalRelativeVolumeActionCurve
        period hPeriod integrand baseScale direction hBaseScale) := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  have hIntegrated := integral_contDiff_two_of_jointContinuous_compact
    (measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (density := conformalRelativeVolumeActionDensity
      period hPeriod integrand baseScale direction hBaseScale)
    (firstDerivative := conformalRelativeVolumeActionFirstDerivativeDensity
      period hPeriod integrand baseScale direction hBaseScale)
    (secondDerivative := conformalRelativeVolumeActionSecondDerivativeDensity
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionDensity_uncurry_continuous
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionFirstDerivativeDensity_uncurry_continuous
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionSecondDerivativeDensity_uncurry_continuous
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionDensity_hasDerivAt
      period hPeriod integrand baseScale direction hBaseScale)
    (conformalRelativeVolumeActionFirstDerivativeDensity_hasDerivAt
      period hPeriod integrand baseScale direction hBaseScale)
  rw [show
    conformalRelativeVolumeActionCurve
        period hPeriod integrand baseScale direction hBaseScale =
      fun parameter =>
        ∫ point,
          conformalRelativeVolumeActionDensity
            period hPeriod integrand baseScale direction hBaseScale
              parameter point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod by
    funext parameter
    exact conformalRelativeVolumeActionCurve_eq_reference
      period hPeriod integrand baseScale direction hBaseScale parameter]
  exact hIntegrated

end

end P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
end JanusFormal
