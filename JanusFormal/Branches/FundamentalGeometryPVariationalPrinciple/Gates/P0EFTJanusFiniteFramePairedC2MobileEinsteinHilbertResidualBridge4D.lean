import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2EinsteinHilbertDerivativeRecenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2EinsteinHilbertEulerSectors4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D

/-! # Paired mobile Einstein--Hilbert residual at the physical metric center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2MobileEinsteinHilbertResidualBridge4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 8000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTEulerDecomposition4D
open P0EFTJanusFiniteFramePairedC2EinsteinHilbertEulerSectors4D
open P0EFTJanusFiniteFrameRegularC2MobileEinsteinHilbertResidualBridge4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertDerivativeRecenter4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The two complete mobile EH residuals, one in each metric sector. -/
def regularFramePairedMobileEinsteinHilbertResidual
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusCouplings minusCouplings : EinsteinHilbertCouplings) :
    SmoothGeneralMetricTensorPair period hPeriod :=
  (regularFrameMobileEinsteinHilbertResidual period hPeriod plusBase plusCouplings,
    regularFrameMobileEinsteinHilbertResidual period hPeriod minusBase minusCouplings)

/-- The actual paired finite EH Euler at `(g₊, g₋)`, encoded in the common
`g₊` chart, is the pairing with both mobile residuals. -/
theorem finiteFramePairedC2EinsteinHilbertEuler_physicalCenter_smooth_lifts_eq_residualPairing
    (frame : SmoothD8Frame period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hPlusCanonicalVolume : plusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod plusBase.metric)
    (hMinusCanonicalVolume : minusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod minusBase.metric)
    (hShift : smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame plusBase.metric)
    (plusCouplings minusCouplings : EinsteinHilbertCouplings)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    let shift := smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
      (minusBase.metric.tensor - plusBase.metric.tensor)
    let center := (0, shift)
    let direction :=
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation,
        smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation)
    let test := globalMinimalPhysicalMetricTestOfPair period hPeriod
      (plusVariation, minusVariation)
    finiteFramePairedC2EinsteinHilbertEuler period hPeriod frame frame plusBase.metric
        plusBase.metric plusCouplings minusCouplings center direction =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric)
        (regularFramePairedMobileEinsteinHilbertResidual period hPeriod plusBase minusBase
          plusCouplings minusCouplings) test := by
  dsimp only
  let shift := smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
    (minusBase.metric.tensor - plusBase.metric.tensor)
  let plusDirection :=
    smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation
  let minusDirection :=
    smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation
  have hCenter : (0, shift) ∈ finiteFramePairedC2EinsteinHilbertDomain period hPeriod frame frame
      plusBase.metric plusBase.metric :=
    ⟨zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame plusBase.metric, hShift⟩
  rw [finiteFramePairedC2EinsteinHilbertEuler_eq_sector_eulers period hPeriod frame frame
    plusBase.metric plusBase.metric plusCouplings minusCouplings (0, shift) hCenter]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  rw [finiteFrameC2EinsteinHilbertEuler_zero_smooth_lift_eq_mobileResidualPairing period hPeriod
      frame plusBase hPlusCanonicalVolume plusCouplings plusVariation,
    finiteFrameC2EinsteinHilbertEuler_smooth_recenter_eq_mobileResidualPairing period hPeriod frame
      plusBase minusBase hShift hMinusCanonicalVolume minusVariation minusCouplings]
  have hPlus :=
    (generalMetricTensorPairingAt_continuous period hPeriod plusBase.metric
      (regularFrameMobileEinsteinHilbertResidual period hPeriod plusBase plusCouplings)
      plusVariation).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  have hMinus :=
    (generalMetricTensorPairingAt_continuous period hPeriod minusBase.metric
      (regularFrameMobileEinsteinHilbertResidual period hPeriod minusBase minusCouplings)
      minusVariation).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  unfold regularGeneralMetricC2PairedMetricResidualPairing
  rw [globalMinimalPhysicalMetricTestPair_ofPair]
  unfold canonicalGeneralMetricTensorPairPairing
  rw [← integral_add hPlus hMinus]
  apply integral_congr_ae
  filter_upwards [] with point
  rfl

end
end P0EFTJanusFiniteFramePairedC2MobileEinsteinHilbertResidualBridge4D
end JanusFormal
