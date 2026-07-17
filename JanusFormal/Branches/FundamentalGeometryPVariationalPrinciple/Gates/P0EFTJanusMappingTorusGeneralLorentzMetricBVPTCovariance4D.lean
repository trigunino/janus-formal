import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D

/-!
# PT covariance of the first general-metric BV level

This gate acts by analytic PT pullback and sector exchange on metric
variations and antifields.  It proves the finite, pointwise BV covariance
statements only; no functional master equation is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricBVPTCovariance4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Analytic PT pullback followed by exchange of the two metric-variation
sectors. -/
def smoothGeneralMetricTensorPairPTExchange
    (variation : SmoothGeneralMetricTensorPair period hPeriod) :
    SmoothGeneralMetricTensorPair period hPeriod :=
  (smoothPTTensorPullback period hPeriod variation.2,
    smoothPTTensorPullback period hPeriod variation.1)

@[simp]
theorem smoothGeneralMetricTensorPairPTExchange_involutive
    (variation : SmoothGeneralMetricTensorPair period hPeriod) :
    smoothGeneralMetricTensorPairPTExchange period hPeriod
        (smoothGeneralMetricTensorPairPTExchange period hPeriod variation) =
      variation := by
  simp [smoothGeneralMetricTensorPairPTExchange]

@[simp]
theorem smoothPTTensorPullback_zero :
    smoothPTTensorPullback period hPeriod
        (zeroSymmetricTensor period hPeriod) =
      zeroSymmetricTensor period hPeriod := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change (0 : Real) = 0
  rfl

@[simp]
theorem smoothGeneralMetricTensorPairPTExchange_zero :
    smoothGeneralMetricTensorPairPTExchange period hPeriod
        (smoothGeneralMetricTensorPairZero period hPeriod) =
      smoothGeneralMetricTensorPairZero period hPeriod := by
  simp [smoothGeneralMetricTensorPairPTExchange,
    smoothGeneralMetricTensorPairZero]

/-- The same PT/exchange acts on the even variation and its shifted
antifield. -/
def smoothGeneralMetricBVPTExchange
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    SmoothGeneralMetricBVField period hPeriod :=
  (smoothGeneralMetricTensorPairPTExchange period hPeriod phase.1,
    smoothGeneralMetricTensorPairPTExchange period hPeriod phase.2)

@[simp]
theorem smoothGeneralMetricBVPTExchange_involutive
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    smoothGeneralMetricBVPTExchange period hPeriod
        (smoothGeneralMetricBVPTExchange period hPeriod phase) = phase := by
  apply Prod.ext <;>
    exact smoothGeneralMetricTensorPairPTExchange_involutive period hPeriod _

@[simp]
theorem smoothGeneralMetricBVPTExchange_zero :
    smoothGeneralMetricBVPTExchange period hPeriod
        (smoothGeneralMetricBVZero period hPeriod) =
      smoothGeneralMetricBVZero period hPeriod := by
  apply Prod.ext <;>
    exact smoothGeneralMetricTensorPairPTExchange_zero period hPeriod

/-- PT/exchange is an even symmetry of the contractible metric BV doublet. -/
theorem smoothGeneralMetricBVPTExchange_commutes_BRST
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    smoothGeneralMetricBVPTExchange period hPeriod
        (smoothGeneralMetricBVBRST period hPeriod phase) =
      smoothGeneralMetricBVBRST period hPeriod
        (smoothGeneralMetricBVPTExchange period hPeriod phase) := by
  apply Prod.ext
  · rfl
  · exact smoothGeneralMetricTensorPairPTExchange_zero period hPeriod

/-- A pulled tensor covector is the ordinary covector pullback of the
original tensor covector. -/
theorem smoothPTTensorPullback_covector
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    (smoothPTTensorPullback period hPeriod tensor).tensor point vector =
      pullbackCovector period hPeriod
        (analyticPTDerivative period hPeriod point)
        (tensor.tensor (reflectedSpherePT period hPeriod point)
          (analyticPTDerivative period hPeriod point vector)) := by
  apply ContinuousLinearMap.ext
  intro second
  simp only [smoothPTTensorPullback_apply, pullbackCovector_apply,
    analyticPTDerivative_apply]

/-- Raising a pulled tensor is conjugation of the original raised tensor by
the inverse PT derivative. -/
theorem raisedGeneralMetricTensorAt_pt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (raisedGeneralMetricTensorAt period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
        (smoothPTTensorPullback period hPeriod tensor) point).toLinearMap =
      (analyticPTDerivative period hPeriod point).symm.toLinearEquiv.conj
        (raisedGeneralMetricTensorAt period hPeriod metric tensor
          (reflectedSpherePT period hPeriod point)).toLinearMap := by
  apply LinearMap.ext
  intro vector
  apply (analyticPTDerivative period hPeriod point).injective
  change analyticPTDerivative period hPeriod point
      ((smoothGeneralLorentzMetricPTPullback period hPeriod metric).musical
        point |>.symm
        ((smoothPTTensorPullback period hPeriod tensor).tensor point vector)) = _
  rw [show
      (smoothPTTensorPullback period hPeriod tensor).tensor point vector =
        pullbackCovector period hPeriod
          (analyticPTDerivative period hPeriod point)
          (tensor.tensor (reflectedSpherePT period hPeriod point)
            (analyticPTDerivative period hPeriod point vector)) by
    exact smoothPTTensorPullback_covector period hPeriod tensor point vector]
  simp [raisedGeneralMetricTensorAt, smoothGeneralLorentzMetricPTPullback,
    pullbackMusical, pullbackCovector, LinearEquiv.conj_apply]
  apply ContinuousLinearMap.ext
  intro second
  simp

/-- The background-raised trace pairing is a PT scalar when the background
metric and both variations are pulled back coherently. -/
theorem generalMetricTensorPairingAt_pt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
        (smoothPTTensorPullback period hPeriod first)
        (smoothPTTensorPullback period hPeriod second) point =
      generalMetricTensorPairingAt period hPeriod metric first second
        (reflectedSpherePT period hPeriod point) := by
  unfold generalMetricTensorPairingAt
  rw [raisedGeneralMetricTensorAt_pt period hPeriod metric first point,
    raisedGeneralMetricTensorAt_pt period hPeriod metric second point]
  let equivalence :=
    (analyticPTDerivative period hPeriod point).symm.toLinearEquiv
  let firstEnd :=
    (raisedGeneralMetricTensorAt period hPeriod metric first
      (reflectedSpherePT period hPeriod point)).toLinearMap
  let secondEnd :=
    (raisedGeneralMetricTensorAt period hPeriod metric second
      (reflectedSpherePT period hPeriod point)).toLinearMap
  have hTrace := LinearMap.trace_conj' (firstEnd * secondEnd) equivalence
  rw [← hTrace]
  congr 1
  apply LinearMap.ext
  intro vector
  simp [equivalence, firstEnd, secondEnd]

/-- The two-sector pairing is covariant under simultaneous PT and sector
exchange. -/
theorem generalMetricTensorPairPairingAt_ptExchange
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairPairingAt period hPeriod
        (smoothGeneralLorentzMetricPTExchange period hPeriod metrics)
        (smoothGeneralMetricTensorPairPTExchange period hPeriod first)
        (smoothGeneralMetricTensorPairPTExchange period hPeriod second) point =
      generalMetricTensorPairPairingAt period hPeriod metrics first second
        (reflectedSpherePT period hPeriod point) := by
  simp only [generalMetricTensorPairPairingAt,
    smoothGeneralLorentzMetricPTExchange,
    smoothGeneralMetricTensorPairPTExchange]
  rw [generalMetricTensorPairingAt_pt period hPeriod metrics.2 first.2 second.2,
    generalMetricTensorPairingAt_pt period hPeriod metrics.1 first.1 second.1]
  exact add_comm _ _

/-- Pull back a point observable together with both Darboux gradients.  The
phase argument is transformed contravariantly; the point is evaluated at its
PT image. -/
def generalMetricBVPointObservablePTExchange
    (observable : GeneralMetricBVPointObservable period hPeriod) :
    GeneralMetricBVPointObservable period hPeriod where
  parity := observable.parity
  value := fun phase point =>
    observable.value (smoothGeneralMetricBVPTExchange period hPeriod phase)
      (reflectedSpherePT period hPeriod point)
  fieldGradient := fun phase =>
    smoothGeneralMetricTensorPairPTExchange period hPeriod
      (observable.fieldGradient
        (smoothGeneralMetricBVPTExchange period hPeriod phase))
  antifieldGradient := fun phase =>
    smoothGeneralMetricTensorPairPTExchange period hPeriod
      (observable.antifieldGradient
        (smoothGeneralMetricBVPTExchange period hPeriod phase))

@[simp]
theorem generalMetricBVPointObservablePTExchange_involutive
    (observable : GeneralMetricBVPointObservable period hPeriod) :
    generalMetricBVPointObservablePTExchange period hPeriod
        (generalMetricBVPointObservablePTExchange period hPeriod observable) =
      observable := by
  cases observable
  simp [generalMetricBVPointObservablePTExchange,
    reflectedSpherePT_involutive]

/-- The pointwise odd antibracket is a PT scalar under coherent exchange of
the metrics, phase and both observables. -/
theorem generalMetricBVOddAntibracketAt_ptExchange
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricBVOddAntibracketAt period hPeriod
        (smoothGeneralLorentzMetricPTExchange period hPeriod metrics)
        (generalMetricBVPointObservablePTExchange period hPeriod first)
        (generalMetricBVPointObservablePTExchange period hPeriod second)
        (smoothGeneralMetricBVPTExchange period hPeriod phase) point =
      generalMetricBVOddAntibracketAt period hPeriod metrics first second phase
        (reflectedSpherePT period hPeriod point) := by
  simp only [generalMetricBVOddAntibracketAt,
    generalMetricBVPointObservablePTExchange,
    smoothGeneralMetricBVPTExchange_involutive]
  rw [generalMetricTensorPairPairingAt_ptExchange period hPeriod metrics,
    generalMetricTensorPairPairingAt_ptExchange period hPeriod metrics]

end

end P0EFTJanusMappingTorusGeneralLorentzMetricBVPTCovariance4D
end JanusFormal
