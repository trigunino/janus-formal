import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricResidual4D

/-! Concrete actual L2 estimate for the induced Maxwell metric derivative. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12InducedMaxwellMetricL24D

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

/-- A concrete Riesz vector for the induced Maxwell metric variation. -/
def inducedMaxwellMetricRiesz : GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  regularTensorCovectorActualL2 period hPeriod metric
    (metricInducedMaxwellResidualCoefficient period hPeriod metric potential)

theorem inducedMaxwellMetricRiesz_pairing
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (inducedMaxwellMetricRiesz period hPeriod metric potential)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod metric
      (regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric potential)
      (metricInducedGaugePotential period hPeriod metric tensor potential) := by
  rw [canonicalMaxwellResidualPairing_metricInducedGaugePotential_eq_metricIntegral]
  exact regularTensorCovectorActualL2_pairing period hPeriod metric
    (metricInducedMaxwellResidualCoefficient period hPeriod metric potential) tensor

/-- The actual native coefficient derivative on the induced positive velocity. -/
def inducedMaxwellMetricVariation (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Real :=
  let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
    (gaugePotentialFrameCoefficients period hPeriod metric potential)
  fderiv Real (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
    period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) 0) coefficients
    ((1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod
      (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)) coefficients)

theorem inducedMaxwellMetricVariation_eq_inner
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inducedMaxwellMetricVariation period hPeriod metric potential tensor =
      inner Real (inducedMaxwellMetricRiesz period hPeriod metric potential)
        (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) := by
  rw [inducedMaxwellMetricRiesz_pairing]
  exact metricInducedGaugeVelocity_fderiv_eq_canonicalPairing period hPeriod metric potential tensor

def inducedMaxwellMetricCovector : GlobalGeneralMetricTensorFrameL2 period hPeriod →L[Real] Real :=
  innerSL Real (inducedMaxwellMetricRiesz period hPeriod metric potential)

theorem inducedMaxwellMetricCovector_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inducedMaxwellMetricCovector period hPeriod metric potential
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
      inducedMaxwellMetricVariation period hPeriod metric potential tensor :=
  (inducedMaxwellMetricVariation_eq_inner period hPeriod metric potential tensor).symm

/-- An unconditional zeroth-order estimate; no metric derivatives occur on the right. -/
theorem inducedMaxwellMetricVariation_bound
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ‖inducedMaxwellMetricVariation period hPeriod metric potential tensor‖ ≤
      ‖inducedMaxwellMetricRiesz period hPeriod metric potential‖ *
        ‖globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor‖ := by
  rw [inducedMaxwellMetricVariation_eq_inner]
  exact norm_inner_le_norm _ _

end
end P0EFTJanusProgramPT12InducedMaxwellMetricL24D
end JanusFormal
