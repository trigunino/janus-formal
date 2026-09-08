import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2MobileInteractionResidualBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2MobileEinsteinHilbertResidualBridge4D

/-! # Physical metric Euler as a regular residual plus the BRST metric term -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 8000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFiniteRankFunctionalMaster4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinHilbertEulerSectors4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D
open P0EFTJanusFiniteFrameRegularC2MobileInteractionResidualBridge4D
open P0EFTJanusFiniteFramePairedC2MobileEinsteinHilbertResidualBridge4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusPairedInteractionOffCenterResidual4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

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

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The mobile Einstein--Hilbert and interaction residuals in the two metric sectors. -/
def regularFramePairedMobileEinsteinHilbertInteractionResidual
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor))
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    SmoothGeneralMetricTensorPair period hPeriod :=
  smoothGeneralMetricTensorPairAdd period hPeriod
    (regularFramePairedMobileEinsteinHilbertResidual period hPeriod plusBase minusBase
      couplings.plusEinstein couplings.minusEinstein)
    (pairedInteractionMobileSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
      interactionScale coefficients)

theorem regularFramePairedMobileEinsteinHilbertInteractionResidual_pairing
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor))
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric)
        (regularFramePairedMobileEinsteinHilbertInteractionResidual period hPeriod
          plusBase minusBase hRoot couplings interactionScale coefficients) test =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
          (plusBase.metric, minusBase.metric)
          (regularFramePairedMobileEinsteinHilbertResidual period hPeriod plusBase minusBase
            couplings.plusEinstein couplings.minusEinstein) test +
        regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
          (plusBase.metric, minusBase.metric)
          (pairedInteractionMobileSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
            interactionScale coefficients) test := by
  unfold regularFramePairedMobileEinsteinHilbertInteractionResidual
    regularGeneralMetricC2PairedMetricResidualPairing
  exact canonicalGeneralMetricTensorPairPairing_add_left period hPeriod
    (plusBase.metric, minusBase.metric)
    (regularFramePairedMobileEinsteinHilbertResidual period hPeriod plusBase minusBase
      couplings.plusEinstein couplings.minusEinstein)
    (pairedInteractionMobileSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
      interactionScale coefficients)
    (globalMinimalPhysicalMetricTestPair period hPeriod test)

/-- At the physical center, the metric Euler is the pairing with the complete
mobile EH-interaction residual, plus the exact metric restriction of the finite
full-BRST Euler. -/
theorem finiteFramePairedC2PhysicalMetricEuler_zero_smooth_lifts_eq_residualPairing_add_fullBRST
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hPlusCanonicalVolume : plusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod plusBase.metric)
    (hMinusCanonicalVolume : minusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod minusBase.metric)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hShift : smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame plusBase.metric)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
    let finiteDirection :=
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation,
        smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation)
    let test := globalMinimalPhysicalMetricTestOfPair period hPeriod
      (plusVariation, minusVariation)
    finiteFramePairedC2PhysicalMetricEuler period hPeriod geometry frame hFiniteRegular couplings
        interactionScale coefficients 0 finiteDirection =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
          (plusBase.metric, minusBase.metric)
        (regularFramePairedMobileEinsteinHilbertInteractionResidual period hPeriod
            plusBase minusBase hRoot couplings interactionScale coefficients) test +
        finiteFramePairedC2FullBRSTGaugeEuler period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric couplings
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame 0)
          (finiteDirection, 0) := by
  dsimp only
  let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let hFiniteRegular :=
    regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let shift := smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
    (minusBase.metric.tensor - plusBase.metric.tensor)
  let finiteDirection :=
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation,
      smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation)
  let test := globalMinimalPhysicalMetricTestOfPair period hPeriod
    (plusVariation, minusVariation)
  change
    finiteFramePairedC2PhysicalMetricEuler period hPeriod geometry frame hFiniteRegular couplings
        interactionScale coefficients 0 finiteDirection =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
          (plusBase.metric, minusBase.metric)
          (regularFramePairedMobileEinsteinHilbertInteractionResidual period hPeriod
            plusBase minusBase
              (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
              couplings interactionScale coefficients) test +
        finiteFramePairedC2FullBRSTGaugeEuler period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric couplings
          (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame 0)
          (finiteDirection, 0)
  have hGeometryMinusTensor : geometry.minusMetric.tensor = minusBase.metric.tensor := by
    dsimp only [geometry]
    rw [regularGeneralMetricC2LorentzChartGeometry_minusMetric,
      regularGeneralMetricC2LorentzChartMetric_tensor]
    abel
  have hCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame = shift := by
    unfold finiteFramePairedC2MinusCenter
    change smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
      (geometry.minusMetric.tensor - plusBase.metric.tensor) = shift
    rw [hGeometryMinusTensor]
  have hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric := by
    rw [hCenter]
    change shift ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame plusBase.metric
    exact hShift
  have hPhysicalZero := zero_mem_finiteFramePairedC2PhysicalDomain period hPeriod geometry frame
    hFiniteRegular hMinusCenter
  have hPairCenter : (0, shift) ∈
      finiteFramePairedC2EinsteinHilbertDomain period hPeriod frame frame
        plusBase.metric plusBase.metric :=
    ⟨zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame plusBase.metric, hShift⟩
  have hEinstein :=
    finiteFramePairedC2EinsteinHilbertEuler_physicalCenter_smooth_lifts_eq_residualPairing
      period hPeriod frame plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hShift
      couplings.plusEinstein couplings.minusEinstein plusVariation minusVariation
  dsimp only at hEinstein
  rw [finiteFramePairedC2EinsteinHilbertEuler_eq_sector_eulers period hPeriod frame frame
    plusBase.metric plusBase.metric couplings.plusEinstein couplings.minusEinstein
      (0, shift) hPairCenter] at hEinstein
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd'] at hEinstein
  have hEinsteinGeometry :
      finiteFrameC2EinsteinHilbertEuler period hPeriod frame geometry.plusMetric
          couplings.plusEinstein 0 finiteDirection.1 +
        finiteFrameC2EinsteinHilbertEuler period hPeriod frame geometry.plusMetric
          couplings.minusEinstein shift finiteDirection.2 =
        regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
          (plusBase.metric, minusBase.metric)
          (regularFramePairedMobileEinsteinHilbertResidual period hPeriod plusBase minusBase
            couplings.plusEinstein couplings.minusEinstein) test := by
    change
      finiteFrameC2EinsteinHilbertEuler period hPeriod frame plusBase.metric
          couplings.plusEinstein 0
            (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
              plusVariation) +
        finiteFrameC2EinsteinHilbertEuler period hPeriod frame plusBase.metric
          couplings.minusEinstein shift
            (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
              minusVariation) = _
    exact hEinstein
  have hInteraction :=
    pairedFiniteFrameC2InteractionEuler_zero_smooth_lifts_eq_mobileMetricResidualPairing
      period hPeriod interactionScale coefficients plusBase minusBase hPlusCanonicalVolume hChart
      frame hZero plusVariation minusVariation
  dsimp only at hInteraction
  have hInteractionGeometry :
      pairedFiniteFrameC2InteractionEuler period hPeriod geometry frame hFiniteRegular
          interactionScale coefficients 0 finiteDirection =
        regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
          (plusBase.metric, minusBase.metric)
          (pairedInteractionMobileSmoothMetricResidualPair period hPeriod plusBase minusBase
            (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
            interactionScale coefficients) test := by
    dsimp only [geometry, hFiniteRegular, finiteDirection, test]
    exact hInteraction
  rw [finiteFramePairedC2PhysicalMetricEuler_apply period hPeriod geometry frame hFiniteRegular
    couplings interactionScale coefficients 0 hPhysicalZero finiteDirection]
  simp only [finiteFramePairedC2PhysicalRecenter_zero, hCenter, Prod.fst_zero]
  rw [hEinsteinGeometry, hInteractionGeometry]
  rw [regularFramePairedMobileEinsteinHilbertInteractionResidual_pairing period hPeriod plusBase
    minusBase (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
      couplings interactionScale coefficients test]
  abel

end
end P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D
end JanusFormal
