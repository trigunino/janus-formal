import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameFixedVolumeRicciResidual4D

/-! # Fixed-volume Einstein--Hilbert variation without a base volume gauge

The native scalar-curvature product rule gives the stored-volume Ricci
residual and the actual Palatini divergence. Neither term is discarded.
-/

namespace JanusFormal
namespace P0EFTJanusFixedVolumeEinsteinHilbertWeightedPalatini4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusRegularFrameFixedVolumeRicciResidual4D

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

/-- Ricci weighted by the scalar volume actually stored in the action. -/
def regularFrameStoredVolumeRicciResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real) : SmoothSymmetricCovariantTwoTensor period hPeriod :=
  smoothBulkScalarSMulTensor period hPeriod
    ((-(1 / (2 * gravitationalCoupling))) • metric.volume)
    (regularFrameSymmetricRicciTensor period hPeriod metric)

theorem regularFrameStoredVolumeRicciResidual_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameStoredVolumeRicciResidual period hPeriod metric gravitationalCoupling)
        tensor point =
      (-(1 / (2 * gravitationalCoupling)) * metric.volume point) *
        generalMetricTensorPairingAt period hPeriod metric.metric
          (regularFrameSymmetricRicciTensor period hPeriod metric) tensor point := by
  unfold regularFrameStoredVolumeRicciResidual
  rw [generalMetricTensorPairingAt_symmetric,
    generalMetricTensorPairingAt_smoothBulkScalarSMul_right,
    generalMetricTensorPairingAt_symmetric]
  rfl

/-- The previously constructed Ricci residual is recovered in canonical-volume gauge. -/
theorem regularFrameStoredVolumeRicciResidual_eq_of_canonicalVolumeGauge
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric) :
    regularFrameStoredVolumeRicciResidual period hPeriod metric gravitationalCoupling =
      regularFrameFixedVolumeRicciResidual period hPeriod metric gravitationalCoupling := by
  unfold regularFrameStoredVolumeRicciResidual regularFrameFixedVolumeRicciResidual
  rw [hGauge]

/-- Direct scalar-curvature differentiation retains the full Palatini term;
the cosmological constant contributes no fixed-volume derivative. -/
theorem regularFrameFixedVolumeEinsteinHilbertDensityDerivative_eq_storedRicci_add_palatini
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero
        period hPeriod metric couplings
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point =
      generalMetricTensorPairingAt period hPeriod metric.metric
          (regularFrameStoredVolumeRicciResidual period hPeriod metric couplings.gravitationalCoupling)
          tensor point +
        (metric.volume point / (2 * couplings.gravitationalCoupling)) *
          regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor point := by
  rw [regularGeneralMetricC0FixedVolumeEinsteinHilbertDensityDerivativeAtZero_apply]
  change metric.volume point * ((1 / (2 * couplings.gravitationalCoupling)) *
    regularGeneralMetricC0ScalarCurvatureDerivativeAtZero period hPeriod metric
      (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point) = _
  rw [regularGeneralMetricC0ScalarCurvatureDerivativeAtZero_pointwise,
    regularGeneralMetricC0PalatiniScalarVelocity_eq_smoothDivergence]
  dsimp only [inverseMetricScalarVelocity]
  rw [regularFrameRicciInverseVelocity_pairing_invariant,
    regularFrameStoredVolumeRicciResidual_pairing]
  ring

/-- The actual fixed-volume derivative is its stored Ricci pairing plus the
weighted Palatini divergence, with no volume-gauge or stationarity assumption. -/
theorem regularFrameFixedVolumeEinsteinHilbertDerivative_eq_storedRicci_add_palatini
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        couplings (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      (∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameStoredVolumeRicciResidual period hPeriod metric couplings.gravitationalCoupling)
        tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
      ∫ point, (metric.volume point / (2 * couplings.gravitationalCoupling)) *
        regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  have hRicci :=
    (generalMetricTensorPairingAt_continuous period hPeriod metric.metric
      (regularFrameStoredVolumeRicciResidual period hPeriod metric couplings.gravitationalCoupling)
      tensor).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  have hPalatini : Integrable (fun point =>
      metric.volume point / (2 * couplings.gravitationalCoupling) *
        regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    ((metric.volume.contMDiff_toFun.continuous.div_const (2 * couplings.gravitationalCoupling)).mul
      (regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor).contMDiff_toFun.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  unfold regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
  rw [ContinuousLinearMap.comp_apply, regularGeneralMetricC0IntegralCLM_apply,
    ← integral_add hRicci hPalatini]
  exact congrArg (fun integrand : EffectiveQuotient period hPeriod → Real =>
    ∫ point, integrand point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (funext (regularFrameFixedVolumeEinsteinHilbertDensityDerivative_eq_storedRicci_add_palatini
      period hPeriod metric couplings tensor))

end
end P0EFTJanusFixedVolumeEinsteinHilbertWeightedPalatini4D
end JanusFormal
