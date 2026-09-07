import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedVolumeMaxwellStressResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeCoefficientMaxwellIntrinsicFirstVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInducedMaxwellResidual4D

/-! # Complete smooth Maxwell metric residual at the chart centre

The native mobile-frame derivative includes the stress, the positive
fixed-volume correction, and the actual induced gauge variation.
-/

namespace JanusFormal
namespace P0EFTJanusStrongMaxwellMetricResidual4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
open P0EFTJanusFixedVolumeMaxwellStressResidual4D
open P0EFTJanusMetricInducedSmoothGaugeVelocity4D
open P0EFTJanusGaugeCoefficientMaxwellIntrinsicFirstVariation4D
open P0EFTJanusMetricInducedMaxwellResidual4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- The induced native coefficient derivative is the canonical gauge residual. -/
theorem metricInducedGaugeVelocity_fderiv_eq_canonicalPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      (gaugePotentialFrameCoefficients period hPeriod metric potential)
    fderiv Real (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) 0)
      coefficients
      ((1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod
        (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)) coefficients) =
      canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod metric
        (regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric potential)
        (metricInducedGaugePotential period hPeriod metric tensor potential) := by
  dsimp only
  have hVelocity := metricInducedGaugePotential_toC2 period hPeriod metric tensor potential
  rw [regularGeneralMetricC2InducedGaugeVelocityCLM_apply] at hVelocity
  rw [← hVelocity,
    gaugeCoefficientMaxwellAction_fderiv_zeroMetric_eq_canonicalResidualPairing]

/-- All three terms of the genuine mobile-frame metric variation. -/
def strongMaxwellMetricResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  smoothSymmetricTensorAdd period hPeriod
    (regularFrameFixedVolumeMaxwellStressResidual period hPeriod metric potential)
    (metricInducedMaxwellResidual period hPeriod metric potential)

theorem strongMaxwellMetricResidual_integral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    (∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
      (regularFrameFixedVolumeMaxwellStressResidual period hPeriod metric potential)
      tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
    (∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
      (metricInducedMaxwellResidual period hPeriod metric potential)
      tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
    ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
      (strongMaxwellMetricResidual period hPeriod metric potential)
      tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  have hFirst := generalMetricTensorPairingAt_continuous period hPeriod metric.metric
    (regularFrameFixedVolumeMaxwellStressResidual period hPeriod metric potential) tensor
  have hSecond := generalMetricTensorPairingAt_continuous period hPeriod metric.metric
    (metricInducedMaxwellResidual period hPeriod metric potential) tensor
  rw [← integral_add (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (hFirst.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hSecond.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply congrArg (fun density : EffectiveQuotient period hPeriod → Real =>
    ∫ point, density point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  funext point
  exact (generalMetricTensorPairingAt_add_left period hPeriod metric.metric _ _ tensor point).symm

/-- Actual native derivative, with no Maxwell stationarity assumption. -/
theorem strongMaxwellMetricCenterFirstVariation_eq_residualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      (gaugePotentialFrameCoefficients period hPeriod metric potential)
    fderiv Real
      (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        variation coefficients) 0
      (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
      (strongMaxwellMetricResidual period hPeriod metric potential)
      tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  dsimp only
  rw [regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_fderiv_zero_smoothPotential,
    regularGeneralMetricC0FixedVolumeMaxwellAction_fderiv_zero_eq_residualIntegral,
    metricInducedGaugeVelocity_fderiv_eq_canonicalPairing,
    canonicalMaxwellResidualPairing_metricInducedGaugePotential_eq_metricIntegral]
  exact strongMaxwellMetricResidual_integral period hPeriod metric potential tensor

end
end P0EFTJanusStrongMaxwellMetricResidual4D
end JanusFormal

