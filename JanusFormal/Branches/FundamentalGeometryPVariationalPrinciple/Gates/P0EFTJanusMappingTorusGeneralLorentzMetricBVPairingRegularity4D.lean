import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D

/-!
# Regularity of the bulk general-metric BV pairing

In tangent/dual trivializations, the raised tensor is the product of the
inverse local metric matrix with the local tensor matrix.  Smooth section
coefficients are continuous, inversion is smooth at every invertible metric
matrix, and finite-dimensional trace is continuous.  Thus every represented
bulk pairing density is continuous and integrable on the compact quotient.

This discharges the continuity and `L¹` contracts used by the integrated
ultralocal master gate.  No derivative-dependent or nonlocal BV functional is
constructed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators Topology
open Bundle ContinuousLinearMap MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev ModelTangent := CoverCoordinates

private abbrev ModelCotangent :=
  ModelTangent →L[Real] Real

private abbrev GeneralMetricCotangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  GeneralMetricTangentFiber period hPeriod point →L[Real] Real

private abbrev ModelEndomorphism :=
  ModelTangent →L[Real] ModelTangent

local instance effectiveTangentFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real
      (GeneralMetricTangentFiber period hPeriod point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

/-! ## Local inverse-matrix calculation -/

/-- Coefficients of a smooth covariant tensor in tangent and dual
trivializations based at `anchor`. -/
private def generalMetricTensorCoordinates
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) :
    ModelTangent →L[Real] ModelCotangent :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (GeneralMetricTangentFiber period hPeriod) ModelCotangent
    (GeneralMetricCotangentFiber period hPeriod)
    anchor current anchor current (tensor.tensor current)

private theorem generalMetricTensorCoordinates_continuousAt
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    ContinuousAt
      (generalMetricTensorCoordinates period hPeriod tensor anchor) anchor := by
  have hSmooth := tensor.tensor.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hSmooth
  exact hSmooth.2.continuousAt

private def generalMetricCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) :
    ModelTangent →L[Real] ModelCotangent :=
  generalMetricTensorCoordinates period hPeriod metric.tensor anchor current

private theorem generalMetricCoordinates_isInvertible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    (generalMetricCoordinates period hPeriod metric anchor anchor).IsInvertible := by
  have hTangent : anchor ∈
      (trivializationAt ModelTangent
        (GeneralMetricTangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelTangent
      (GeneralMetricTangentFiber period hPeriod) anchor
  have hCotangent : anchor ∈
      (trivializationAt ModelCotangent
        (GeneralMetricCotangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelCotangent
      (GeneralMetricCotangentFiber period hPeriod) anchor
  have hFiber :
      metric.tensor.tensor anchor =
        (metric.musical anchor :
          GeneralMetricTangentFiber period hPeriod anchor →L[Real]
            GeneralMetricCotangentFiber period hPeriod anchor) :=
    (metric.musical_eq_tensor anchor).symm
  unfold generalMetricCoordinates generalMetricTensorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent, hFiber]
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

private def raisedGeneralMetricTensorCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) :
    ModelEndomorphism :=
  (generalMetricCoordinates period hPeriod metric anchor current).inverse.comp
    (generalMetricTensorCoordinates period hPeriod tensor anchor current)

private theorem raisedGeneralMetricTensorCoordinates_eq_inCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod)
    (hTangent : current ∈
      (trivializationAt ModelTangent
        (GeneralMetricTangentFiber period hPeriod) anchor).baseSet)
    (hCotangent : current ∈
      (trivializationAt ModelCotangent
        (GeneralMetricCotangentFiber period hPeriod) anchor).baseSet) :
    raisedGeneralMetricTensorCoordinates period hPeriod metric tensor
        anchor current =
      ContinuousLinearMap.inCoordinates ModelTangent
        (GeneralMetricTangentFiber period hPeriod) ModelTangent
        (GeneralMetricTangentFiber period hPeriod)
        anchor current anchor current
        (raisedGeneralMetricTensorAt period hPeriod metric tensor current) := by
  have hFiber :
      metric.tensor.tensor current =
        (metric.musical current :
          GeneralMetricTangentFiber period hPeriod current →L[Real]
            GeneralMetricCotangentFiber period hPeriod current) :=
    (metric.musical_eq_tensor current).symm
  unfold raisedGeneralMetricTensorCoordinates generalMetricCoordinates
    generalMetricTensorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent, hFiber,
    ContinuousLinearMap.inCoordinates_eq hTangent hCotangent,
    ContinuousLinearMap.inCoordinates_eq hTangent hTangent]
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm]
  apply ContinuousLinearMap.ext
  intro vector
  simp only [raisedGeneralMetricTensorAt,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.symm_apply_apply]

private def modelTraceLinearMap : ModelEndomorphism →ₗ[Real] Real :=
  (LinearMap.trace Real ModelTangent).comp
    (ContinuousLinearMap.coeLM Real)

private def modelTrace : ModelEndomorphism →L[Real] Real :=
  LinearMap.toContinuousLinearMap modelTraceLinearMap

@[simp]
private theorem modelTrace_apply (endomorphism : ModelEndomorphism) :
    modelTrace endomorphism =
      LinearMap.trace Real ModelTangent endomorphism.toLinearMap :=
  rfl

private def modelGeneralMetricTensorPairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) : Real :=
  modelTrace
    ((raisedGeneralMetricTensorCoordinates period hPeriod metric first
        anchor current).comp
      (raisedGeneralMetricTensorCoordinates period hPeriod metric second
        anchor current))

private theorem modelGeneralMetricTensorPairing_continuousAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    ContinuousAt
      (modelGeneralMetricTensorPairing period hPeriod metric first second anchor)
      anchor := by
  have hMetric : ContinuousAt
      (generalMetricCoordinates period hPeriod metric anchor) anchor :=
    generalMetricTensorCoordinates_continuousAt period hPeriod
      metric.tensor anchor
  have hInverse : ContinuousAt
      (fun current =>
        (generalMetricCoordinates period hPeriod metric anchor current).inverse)
      anchor :=
    (generalMetricCoordinates_isInvertible period hPeriod metric anchor
      |>.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hMetric
  have hFirst := generalMetricTensorCoordinates_continuousAt
    period hPeriod first anchor
  have hSecond := generalMetricTensorCoordinates_continuousAt
    period hPeriod second anchor
  have hRaisedFirst := hInverse.clm_comp hFirst
  have hRaisedSecond := hInverse.clm_comp hSecond
  exact modelTrace.continuous.continuousAt.comp
    (hRaisedFirst.clm_comp hRaisedSecond)

private theorem generalMetricTensorPairingAt_eq_model
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod)
    (hTangent : current ∈
      (trivializationAt ModelTangent
        (GeneralMetricTangentFiber period hPeriod) anchor).baseSet)
    (hCotangent : current ∈
      (trivializationAt ModelCotangent
        (GeneralMetricCotangentFiber period hPeriod) anchor).baseSet) :
    generalMetricTensorPairingAt period hPeriod metric first second current =
      modelGeneralMetricTensorPairing period hPeriod metric
        first second anchor current := by
  rw [modelGeneralMetricTensorPairing,
    raisedGeneralMetricTensorCoordinates_eq_inCoordinates period hPeriod
      metric first anchor current hTangent hCotangent,
    raisedGeneralMetricTensorCoordinates_eq_inCoordinates period hPeriod
      metric second anchor current hTangent hCotangent]
  rw [modelTrace_apply]
  unfold generalMetricTensorPairingAt
  let equivalence :=
    (trivializationAt ModelTangent
      (GeneralMetricTangentFiber period hPeriod) anchor).continuousLinearEquivAt
        Real current hTangent
  have hTrace := LinearMap.trace_conj'
    ((raisedGeneralMetricTensorAt period hPeriod metric first current).toLinearMap *
      (raisedGeneralMetricTensorAt period hPeriod metric second current).toLinearMap)
    equivalence.toLinearEquiv
  rw [← hTrace]
  congr 1
  apply LinearMap.ext
  intro vector
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hTangent,
    ContinuousLinearMap.inCoordinates_eq hTangent hTangent]
  change equivalence
      (raisedGeneralMetricTensorAt period hPeriod metric first current
        (raisedGeneralMetricTensorAt period hPeriod metric second current
          (equivalence.symm vector))) =
    equivalence
      (raisedGeneralMetricTensorAt period hPeriod metric first current
        (equivalence.symm
          (equivalence
            (raisedGeneralMetricTensorAt period hPeriod metric second current
              (equivalence.symm vector)))))
  rw [equivalence.symm_apply_apply]

/-! ## Global continuity and unconditional integrability -/

theorem generalMetricTensorPairingAt_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    Continuous (fun point : EffectiveQuotient period hPeriod =>
      generalMetricTensorPairingAt period hPeriod metric first second point) := by
  rw [continuous_iff_continuousAt]
  intro anchor
  have hLocal := modelGeneralMetricTensorPairing_continuousAt
    period hPeriod metric first second anchor
  apply hLocal.congr_of_eventuallyEq
  have hTangent : ∀ᶠ current in 𝓝 anchor,
      current ∈ (trivializationAt ModelTangent
        (GeneralMetricTangentFiber period hPeriod) anchor).baseSet :=
    (trivializationAt ModelTangent
      (GeneralMetricTangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ModelTangent
          (GeneralMetricTangentFiber period hPeriod) anchor)
  have hCotangent : ∀ᶠ current in 𝓝 anchor,
      current ∈ (trivializationAt ModelCotangent
        (GeneralMetricCotangentFiber period hPeriod) anchor).baseSet :=
    (trivializationAt ModelCotangent
      (GeneralMetricCotangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ModelCotangent
          (GeneralMetricCotangentFiber period hPeriod) anchor)
  filter_upwards [hTangent, hCotangent] with current hTangent' hCotangent'
  exact generalMetricTensorPairingAt_eq_model period hPeriod metric
    first second anchor current hTangent' hCotangent'

/-- Exact continuity property consumed by the integrated bulk gate. -/
abbrev GeneralMetricTensorPairPairingContinuous
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod) : Prop :=
  Continuous (fun point : EffectiveQuotient period hPeriod =>
    generalMetricTensorPairPairingAt period hPeriod metrics first second point)

theorem generalMetricTensorPairPairingAt_continuous
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod) :
    GeneralMetricTensorPairPairingContinuous
      period hPeriod metrics first second :=
  (generalMetricTensorPairingAt_continuous period hPeriod
    metrics.1 first.1 second.1).add
      (generalMetricTensorPairingAt_continuous period hPeriod
        metrics.2 first.2 second.2)

theorem generalMetricInversePairingContinuityContract_proved
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) :
    GeneralMetricInversePairingContinuityContract period hPeriod metrics :=
  generalMetricTensorPairPairingAt_continuous period hPeriod metrics

theorem generalMetricTensorPairPairingL1_unconditional
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod) :
    GeneralMetricTensorPairPairingL1
      period hPeriod metrics first second :=
  generalMetricTensorPairPairingL1_of_continuous period hPeriod metrics
    first second
    (generalMetricTensorPairPairingAt_continuous
      period hPeriod metrics first second)

theorem generalLorentzMetricBVUltralocalMasterActionDensity_integrable_unconditional
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    Integrable
      (fun point : EffectiveQuotient period hPeriod =>
        generalLorentzMetricBVUltralocalMasterActionAt
          period hPeriod metrics phase point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  generalLorentzMetricBVUltralocalMasterActionDensity_integrable
    period hPeriod metrics phase
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)

theorem generalMetricBVOddAntibracketDensity_integrable_unconditional
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    Integrable
      (fun point : EffectiveQuotient period hPeriod =>
        generalMetricBVOddAntibracketAt period hPeriod metrics
          first second phase point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  generalMetricBVOddAntibracketDensity_integrable period hPeriod metrics
    first second phase
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)

theorem canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_expansion_unconditional
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod)
    (parameter : Real) :
    canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine
        period hPeriod metrics phase variation parameter =
      canonicalGeneralLorentzMetricBVUltralocalMasterAction
          period hPeriod metrics phase +
        parameter *
          canonicalGeneralLorentzMetricBVUltralocalMasterFirstVariation
            period hPeriod metrics phase variation +
        parameter ^ 2 / 2 *
          canonicalGeneralMetricTensorPairPairing period hPeriod metrics
            variation.2 variation.2 :=
  canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_expansion
    period hPeriod metrics phase variation parameter
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)

theorem canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_hasDerivAt_unconditional
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod) :
    HasDerivAt
      (canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine
        period hPeriod metrics phase variation)
      (canonicalGeneralLorentzMetricBVUltralocalMasterFirstVariation
        period hPeriod metrics phase variation)
      0 :=
  canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_hasDerivAt
    period hPeriod metrics phase variation
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)

theorem canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_hasDerivAt_gradient_unconditional
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod) :
    HasDerivAt
      (canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine
        period hPeriod metrics phase variation)
      (canonicalGeneralMetricTensorPairPairing period hPeriod metrics
        ((generalLorentzMetricBVUltralocalMasterObservable
          period hPeriod metrics).antifieldGradient phase)
        variation.2)
      0 :=
  canonicalGeneralLorentzMetricBVUltralocalMasterAffineLine_hasDerivAt_gradient
    period hPeriod metrics phase variation
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)
    (generalMetricTensorPairPairingL1_unconditional
      period hPeriod metrics _ _)

end

end P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
end JanusFormal
