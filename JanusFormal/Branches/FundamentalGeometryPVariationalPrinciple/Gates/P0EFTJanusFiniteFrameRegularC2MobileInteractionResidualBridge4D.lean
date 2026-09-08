import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2VolumeDefectResidualBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedInteractionOffCenterResidual4D

/-! # Complete mobile interaction residual across the finite/regular bridge -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2MobileInteractionResidualBridge4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 6000

noncomputable section

open MeasureTheory
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
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D
open P0EFTJanusFiniteFrameRegularC2MobileInteractionDerivativeBridge4D
open P0EFTJanusFiniteFrameRegularC2VolumeDefectResidualBridge4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusPairedInteractionOffCenterResidual4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

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
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Sum of the fixed-volume spectral residual and the exact mobile-volume
residual. -/
def pairedInteractionMobileSmoothMetricResidualPair
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor))
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    SmoothGeneralMetricTensorPair period hPeriod :=
  smoothGeneralMetricTensorPairAdd period hPeriod
    (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
      interactionScale coefficients)
    (pairedInteractionMobileVolumeResidualPair period hPeriod plusBase minusBase hRoot
      interactionScale coefficients)

/-- The complete mobile residual pairing splits into its fixed spectral and
volume-variation parts. -/
theorem pairedInteractionMobileSmoothMetricResidualPair_pairing
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric)
        (pairedInteractionMobileSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
          interactionScale coefficients) test =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
          (plusBase.metric, minusBase.metric)
          (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
            interactionScale coefficients) test +
        regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
          (plusBase.metric, minusBase.metric)
          (pairedInteractionMobileVolumeResidualPair period hPeriod plusBase minusBase hRoot
            interactionScale coefficients) test := by
  unfold pairedInteractionMobileSmoothMetricResidualPair
    regularGeneralMetricC2PairedMetricResidualPairing
  exact canonicalGeneralMetricTensorPairPairing_add_left period hPeriod
    (plusBase.metric, minusBase.metric)
    (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
      interactionScale coefficients)
    (pairedInteractionMobileVolumeResidualPair period hPeriod plusBase minusBase hRoot
      interactionScale coefficients)
    (globalMinimalPhysicalMetricTestPair period hPeriod test)

/-- The actual mobile finite-frame Euler at the paired center is the canonical
pairing with one complete smooth regular tensor residual pair. -/
theorem pairedFiniteFrameC2InteractionEuler_zero_smooth_lifts_eq_mobileMetricResidualPairing
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : plusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod plusBase.metric)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
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
    pairedFiniteFrameC2InteractionEuler period hPeriod geometry frame hFiniteRegular
        interactionScale coefficients 0 finiteDirection =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric)
        (pairedInteractionMobileSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
          interactionScale coefficients) test := by
  dsimp only
  rw [pairedFiniteFrameC2InteractionEuler_zero_smooth_lifts_regular_add_volumeDefect
    period hPeriod interactionScale coefficients plusBase minusBase hCanonicalVolume hChart frame
      hZero plusVariation minusVariation]
  have hFixed := pairedInteractionNativeCenterActionDerivative_eq_metricResidualPairing
    period hPeriod plusBase minusBase hZero interactionScale coefficients
      (globalMinimalPhysicalMetricTestOfPair period hPeriod (plusVariation, minusVariation))
  simp only [globalMinimalPhysicalMetricTestOfPair] at hFixed
  rw [hFixed]
  rw [pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero_smooth_lifts_eq_metricResidualPairing
    period hPeriod interactionScale coefficients plusBase minusBase hCanonicalVolume hChart frame
      hZero plusVariation minusVariation]
  exact (pairedInteractionMobileSmoothMetricResidualPair_pairing period hPeriod plusBase minusBase
    (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
    interactionScale coefficients
    (globalMinimalPhysicalMetricTestOfPair period hPeriod
      (plusVariation, minusVariation))).symm

end
end P0EFTJanusFiniteFrameRegularC2MobileInteractionResidualBridge4D
end JanusFormal
