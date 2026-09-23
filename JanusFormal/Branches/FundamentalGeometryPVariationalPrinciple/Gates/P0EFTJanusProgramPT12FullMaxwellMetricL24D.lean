import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellStressCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InducedMaxwellMetricL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricResidual4D

/-! Concrete actual L2 estimate for the complete mobile-frame Maxwell metric derivative. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12FullMaxwellMetricL24D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
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

open scoped InnerProductSpace
open P0EFTJanusProgramPT12RegularTensorCovectorL24D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusStrongMaxwellMetricResidual4D

variable (metric : RegularGeneralLorentzMetric period hPeriod)
  (potential : SmoothAbelianGaugePotential period hPeriod)

open P0EFTJanusProgramPT12MaxwellStressCoefficients4D
open P0EFTJanusProgramPT12InducedMaxwellMetricL24D

/-- The stress and positive volume correction in the actual tensor L2 space. -/
def fixedVolumeMaxwellMetricRiesz : GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  regularTensorCovectorActualL2 period hPeriod metric
    (fixedVolumeMaxwellCoefficient period hPeriod metric potential)

theorem fixedVolumeMaxwellMetricRiesz_pairing
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (fixedVolumeMaxwellMetricRiesz period hPeriod metric potential)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
      (regularFrameFixedVolumeMaxwellStressResidual period hPeriod metric potential) tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold fixedVolumeMaxwellMetricRiesz
  rw [regularTensorCovectorActualL2_pairing]
  apply integral_congr_ae
  filter_upwards [] with point
  exact fixedVolumeMaxwellCoefficient_pairing period hPeriod metric potential tensor point

/-- All three mobile-frame Maxwell metric terms, without stationarity assumptions. -/
def fullMaxwellMetricRiesz : GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  fixedVolumeMaxwellMetricRiesz period hPeriod metric potential +
    inducedMaxwellMetricRiesz period hPeriod metric potential

theorem fullMaxwellMetricRiesz_pairing
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (fullMaxwellMetricRiesz period hPeriod metric potential)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
      (strongMaxwellMetricResidual period hPeriod metric potential) tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold fullMaxwellMetricRiesz
  rw [inner_add_left, fixedVolumeMaxwellMetricRiesz_pairing, inducedMaxwellMetricRiesz_pairing,
    canonicalMaxwellResidualPairing_metricInducedGaugePotential_eq_metricIntegral]
  exact strongMaxwellMetricResidual_integral period hPeriod metric potential tensor

/-- Native derivative of the full mobile-frame, fixed-volume Maxwell action. -/
def fullMaxwellMetricVariation (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Real :=
  let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
    (gaugePotentialFrameCoefficients period hPeriod metric potential)
  fderiv Real
    (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      variation coefficients) 0
    (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)

theorem fullMaxwellMetricVariation_eq_inner
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    fullMaxwellMetricVariation period hPeriod metric potential tensor =
      inner Real (fullMaxwellMetricRiesz period hPeriod metric potential)
        (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) := by
  rw [fullMaxwellMetricRiesz_pairing]
  exact strongMaxwellMetricCenterFirstVariation_eq_residualIntegral period hPeriod metric potential tensor

def fullMaxwellMetricCovector : GlobalGeneralMetricTensorFrameL2 period hPeriod →L[Real] Real :=
  innerSL Real (fullMaxwellMetricRiesz period hPeriod metric potential)

theorem fullMaxwellMetricCovector_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    fullMaxwellMetricCovector period hPeriod metric potential
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
      fullMaxwellMetricVariation period hPeriod metric potential tensor :=
  (fullMaxwellMetricVariation_eq_inner period hPeriod metric potential tensor).symm

theorem fullMaxwellMetricVariation_bound
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ‖fullMaxwellMetricVariation period hPeriod metric potential tensor‖ ≤
      ‖fullMaxwellMetricRiesz period hPeriod metric potential‖ *
        ‖globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor‖ := by
  rw [fullMaxwellMetricVariation_eq_inner]
  exact norm_inner_le_norm _ _

end
end P0EFTJanusProgramPT12FullMaxwellMetricL24D
end JanusFormal
