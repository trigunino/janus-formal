import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2FullBRSTMetricCenterVanishing4D

/-! # Physical metric stationarity is the regular residual equation -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2PhysicalMetricStationarityResidual4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D
open P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D
open P0EFTJanusFiniteFramePairedC2FullBRSTMetricCenterVanishing4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

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

/-- The finite physical metric Euler vanishes exactly when its unique regular
mobile Einstein--Hilbert--interaction tensor residual vanishes. -/
theorem finiteFramePairedC2PhysicalMetricEuler_zero_iff_residual
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
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
    finiteFramePairedC2PhysicalMetricEuler period hPeriod geometry frame hFiniteRegular couplings
        interactionScale coefficients 0 = 0 ↔
      regularFramePairedMobileEinsteinHilbertInteractionResidual period hPeriod
        plusBase minusBase hRoot couplings interactionScale coefficients = 0 := by
  dsimp only
  let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let hFiniteRegular :=
    regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let residual := regularFramePairedMobileEinsteinHilbertInteractionResidual period hPeriod
    plusBase minusBase
      (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
      couplings interactionScale coefficients
  let euler := finiteFramePairedC2PhysicalMetricEuler period hPeriod geometry frame
    hFiniteRegular couplings interactionScale coefficients 0
  change euler = 0 ↔ residual = 0
  constructor
  · intro hEuler
    apply (regularGeneralMetricC2PairedMetricResidualPairing_separates period hPeriod
      (plusBase.metric, minusBase.metric) residual).mp
    intro test
    have hEval :=
      finiteFramePairedC2PhysicalMetricEuler_zero_smooth_lifts_eq_residualPairing
        period hPeriod plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hChart frame
        hShift hZero couplings interactionScale coefficients (test .plus) (test .minus)
    dsimp only at hEval
    change euler
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric (test .plus),
          smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric (test .minus)) =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric) residual
        (globalMinimalPhysicalMetricTestOfPair period hPeriod
          (globalMinimalPhysicalMetricTestPair period hPeriod test)) at hEval
    rw [globalMinimalPhysicalMetricTestOfPair_pair, hEuler] at hEval
    exact hEval.symm
  · intro hResidual
    let embedding := Prod.map
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric)
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric)
    have hDense :=
      (smoothToGeneralMetricRelativeC2Core_denseRange period hPeriod frame plusBase.metric).prodMap
        (smoothToGeneralMetricRelativeC2Core_denseRange period hPeriod frame plusBase.metric)
    have hPairingZero :=
      (regularGeneralMetricC2PairedMetricResidualPairing_separates period hPeriod
        (plusBase.metric, minusBase.metric) residual).mpr hResidual
    have hOnCore : ∀ pair : SmoothGeneralMetricTensorPair period hPeriod,
        euler (embedding pair) = 0 := by
      intro pair
      have hEval :=
        finiteFramePairedC2PhysicalMetricEuler_zero_smooth_lifts_eq_residualPairing
          period hPeriod plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hChart frame
          hShift hZero couplings interactionScale coefficients pair.1 pair.2
      dsimp only at hEval
      change euler (embedding pair) =
        regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
          (plusBase.metric, minusBase.metric) residual
          (globalMinimalPhysicalMetricTestOfPair period hPeriod pair) at hEval
      exact hEval.trans (hPairingZero
        (globalMinimalPhysicalMetricTestOfPair period hPeriod pair))
    have hFunctions : (fun direction => euler direction) = fun _ => (0 : Real) :=
      hDense.equalizer euler.continuous continuous_const (by
        funext pair
        exact hOnCore pair)
    apply ContinuousLinearMap.ext
    intro direction
    simpa using congrFun hFunctions direction

end
end P0EFTJanusFiniteFrameRegularC2PhysicalMetricStationarityResidual4D
end JanusFormal
