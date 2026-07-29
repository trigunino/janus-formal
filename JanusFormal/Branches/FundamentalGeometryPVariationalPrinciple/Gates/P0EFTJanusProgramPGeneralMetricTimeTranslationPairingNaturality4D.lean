import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricTimeTranslationSkew4D

/-!
# Naturalité temporelle du pairing métrique bulk

Ce gate prouve la naturalité pointwise du pairing tensoriel sous le vrai flot
temporel, puis son invariance intégrée pour le fond intrinsèque fixé.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGeneralMetricTimeTranslationPairingNaturality4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusTensorialDiffeomorphismRepresentation4D
open P0EFTJanusProgramPGeneralMetricTimeTranslationSkew4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev MetricPair :=
  SmoothGeneralMetricTensorPair period hPeriod

private abbrev BackgroundPair :=
  SmoothGeneralLorentzMetric period hPeriod ×
    SmoothGeneralLorentzMetric period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveTangentFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real
      (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

private theorem raisedGeneralMetricTensorAt_timeTranslation_pullback
    (parameter : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (raisedGeneralMetricTensorAt period hPeriod
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          (effectiveTimeFlowDiffeomorph period hPeriod parameter) metric)
        (smoothDiffeomorphismTensorPullback period hPeriod
          (effectiveTimeFlowDiffeomorph period hPeriod parameter) tensor)
        point).toLinearMap =
      (diffeomorphismDerivative period hPeriod
          (effectiveTimeFlowDiffeomorph period hPeriod parameter) point).toLinearEquiv.symm.conj
        (raisedGeneralMetricTensorAt period hPeriod metric tensor
          ((effectiveTimeFlowDiffeomorph period hPeriod parameter) point)).toLinearMap := by
  apply LinearMap.ext
  intro vector
  apply
    ((smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod parameter) metric).musical
        point).injective
  apply ContinuousLinearMap.ext
  intro test
  simp [raisedGeneralMetricTensorAt,
    smoothGeneralLorentzMetricDiffeomorphismPullback,
    smoothDiffeomorphismTensorPullback,
    diffeomorphismTensorPullback,
    diffeomorphismDerivative,
    SmoothCovariantTwoTensor.toTensorField,
    pullbackMusical,
    pullbackCovector]
  rw [← (effectiveTimeFlowDiffeomorph period hPeriod parameter)
    |>.mfderivToContinuousLinearEquiv_coe (by simp)]
  congr 1

private theorem generalMetricTensorPairingAt_timeTranslation_pullback
    (parameter : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          (effectiveTimeFlowDiffeomorph period hPeriod parameter) metric)
        (smoothDiffeomorphismTensorPullback period hPeriod
          (effectiveTimeFlowDiffeomorph period hPeriod parameter) first)
        (smoothDiffeomorphismTensorPullback period hPeriod
          (effectiveTimeFlowDiffeomorph period hPeriod parameter) second)
        point =
      generalMetricTensorPairingAt period hPeriod metric first second
        (effectiveTimeFlow period hPeriod parameter point) := by
  rw [generalMetricTensorPairingAt,
    raisedGeneralMetricTensorAt_timeTranslation_pullback
      period hPeriod parameter metric first point,
    raisedGeneralMetricTensorAt_timeTranslation_pullback
      period hPeriod parameter metric second point]
  let derivative :=
    (diffeomorphismDerivative period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod parameter) point).toLinearEquiv
  have hProduct :
      (derivative.symm.conj
          (raisedGeneralMetricTensorAt period hPeriod metric first
            ((effectiveTimeFlowDiffeomorph
              period hPeriod parameter) point)).toLinearMap) *
          (derivative.symm.conj
            (raisedGeneralMetricTensorAt period hPeriod metric second
              ((effectiveTimeFlowDiffeomorph
                period hPeriod parameter) point)).toLinearMap) =
        derivative.symm.conj
          ((raisedGeneralMetricTensorAt period hPeriod metric first
              ((effectiveTimeFlowDiffeomorph
                period hPeriod parameter) point)).toLinearMap *
            (raisedGeneralMetricTensorAt period hPeriod metric second
              ((effectiveTimeFlowDiffeomorph
                period hPeriod parameter) point)).toLinearMap) := by
    exact (LinearEquiv.conj_comp derivative.symm _ _).symm
  rw [hProduct]
  exact LinearMap.trace_conj' _ derivative.symm

/-- Pointwise naturality under simultaneous pullback by the genuine complete
time-translation diffeomorphism. -/
theorem generalMetricTensorPairPairingAt_timeTranslation_pullback
    (parameter : Real)
    (metrics : BackgroundPair period hPeriod)
    (first second : MetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairPairingAt period hPeriod
        (generalMetricTimeTranslationBackgroundOrbit
          period hPeriod parameter metrics)
        (generalMetricTimeTranslationTensorOrbit
          period hPeriod parameter first)
        (generalMetricTimeTranslationTensorOrbit
          period hPeriod parameter second)
        point =
      generalMetricTensorPairPairingAt period hPeriod metrics first second
        (effectiveTimeFlow period hPeriod parameter point) := by
  unfold generalMetricTensorPairPairingAt
    generalMetricTimeTranslationBackgroundOrbit
    generalMetricTimeTranslationTensorOrbit
  rw [generalMetricTensorPairingAt_timeTranslation_pullback
      period hPeriod parameter metrics.1 first.1 second.1 point,
    generalMetricTensorPairingAt_timeTranslation_pullback
      period hPeriod parameter metrics.2 first.2 second.2 point]

/-- For the intrinsic background, the finite tensor orbit preserves the
canonical integrated pairing. -/
theorem canonicalGeneralMetricTensorPairPairing_intrinsic_timeTranslation_invariant
    (parameter : Real)
    (first second : MetricPair period hPeriod) :
    canonicalGeneralMetricTensorPairPairing period hPeriod
        (intrinsicGeneralLorentzMetricPair period hPeriod)
        (generalMetricTimeTranslationTensorOrbit
          period hPeriod parameter first)
        (generalMetricTimeTranslationTensorOrbit
          period hPeriod parameter second) =
      canonicalGeneralMetricTensorPairPairing period hPeriod
        (intrinsicGeneralLorentzMetricPair period hPeriod) first second := by
  calc
    _ = canonicalGeneralMetricTensorPairPairing period hPeriod
        (generalMetricTimeTranslationBackgroundOrbit period hPeriod parameter
          (intrinsicGeneralLorentzMetricPair period hPeriod))
        (generalMetricTimeTranslationTensorOrbit
          period hPeriod parameter first)
        (generalMetricTimeTranslationTensorOrbit
          period hPeriod parameter second) := by
      rw [intrinsicGeneralLorentzMetricPair_timeTranslation_fixed]
    _ = _ := by
      unfold canonicalGeneralMetricTensorPairPairing
      simp_rw [generalMetricTensorPairPairingAt_timeTranslation_pullback
        period hPeriod parameter
          (intrinsicGeneralLorentzMetricPair period hPeriod)]
      exact effectiveTimeFlow_integral_invariant period hPeriod parameter
        (fun point =>
          generalMetricTensorPairPairingAt period hPeriod
            (intrinsicGeneralLorentzMetricPair period hPeriod)
            first second point)

/-- The integrated pairing along the genuine time-translation orbit has
zero derivative.  This uses the proved finite invariance and no
infinitesimal action. -/
theorem canonicalGeneralMetricTensorPairPairing_intrinsic_timeTranslation_hasDerivAt_zero
    (first second : MetricPair period hPeriod) :
    HasDerivAt
      (fun parameter =>
        canonicalGeneralMetricTensorPairPairing period hPeriod
          (intrinsicGeneralLorentzMetricPair period hPeriod)
          (generalMetricTimeTranslationTensorOrbit
            period hPeriod parameter first)
          (generalMetricTimeTranslationTensorOrbit
            period hPeriod parameter second))
      0 0 := by
  have hFunction :
      (fun parameter =>
        canonicalGeneralMetricTensorPairPairing period hPeriod
          (intrinsicGeneralLorentzMetricPair period hPeriod)
          (generalMetricTimeTranslationTensorOrbit
            period hPeriod parameter first)
          (generalMetricTimeTranslationTensorOrbit
            period hPeriod parameter second)) =
        fun _ : Real =>
          canonicalGeneralMetricTensorPairPairing period hPeriod
            (intrinsicGeneralLorentzMetricPair period hPeriod)
            first second := by
    funext parameter
    exact
      canonicalGeneralMetricTensorPairPairing_intrinsic_timeTranslation_invariant
        period hPeriod parameter first second
  rw [hFunction]
  exact hasDerivAt_const 0 _

end
end P0EFTJanusProgramPGeneralMetricTimeTranslationPairingNaturality4D
end JanusFormal
