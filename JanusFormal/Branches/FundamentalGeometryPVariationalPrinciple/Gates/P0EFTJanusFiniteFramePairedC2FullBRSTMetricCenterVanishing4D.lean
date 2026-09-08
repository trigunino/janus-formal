import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D

/-! # Vanishing of the finite full-BRST metric derivative at zero fields -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2FullBRSTMetricCenterVanishing4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 8000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTDensity4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D
open P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
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

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

theorem finiteFrameC2AbelianBRSTAction_zero_fields
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) :
    finiteFrameC2AbelianBRSTAction period hPeriod frame baseMetric (metric, 0) = 0 := by
  simp [finiteFrameC2AbelianBRSTAction, finiteFrameC2AbelianBRSTDensity]

theorem finiteFramePairedC2AbelianBRSTAction_zero_fields
    (plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusBase minusBase : SmoothGeneralLorentzMetric period hPeriod)
    (metric : GeneralMetricRelativeC2Core period hPeriod plusFrame plusBase ×
      GeneralMetricRelativeC2Core period hPeriod minusFrame minusBase) :
    finiteFramePairedC2AbelianBRSTAction period hPeriod plusFrame minusFrame plusBase minusBase
      ((metric.1, 0), (metric.2, 0)) = 0 := by
  simp [finiteFramePairedC2AbelianBRSTAction,
    finiteFrameC2AbelianBRSTAction_zero_fields]

theorem finiteFrameC2DiffeomorphismBRSTAction_zero_nonminimal
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric tensor : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) :
    finiteFrameC2DiffeomorphismBRSTAction period hPeriod frame baseMetric
      (metric, (tensor, 0)) = 0 := by
  simp [finiteFrameC2DiffeomorphismBRSTAction,
    finiteFrameC2DiffeomorphismBRSTDensity,
    finiteFrameDiffeomorphismBRSTAttachNonminimalC2_apply,
    finiteFrameDiffeomorphismBRSTC0Polynomial]

theorem finiteFramePairedDiffeomorphismBRSTAction_zero_nonminimal
    (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusReference minusReference : SmoothGeneralLorentzMetric period hPeriod)
    (metric : GeneralMetricRelativeC2Core period hPeriod plusFrame plusReference ×
      GeneralMetricRelativeC2Core period hPeriod minusFrame minusReference)
    (couplings : GlobalCandidateAActionCouplings) :
    finiteFramePairedDiffeomorphismBRSTAction period hPeriod source plusFrame minusFrame
      plusReference minusReference couplings (metric, 0) = 0 := by
  simp [finiteFramePairedDiffeomorphismBRSTAction,
    finiteFramePairedDiffeomorphismBRSTPlusInput_apply,
    finiteFramePairedDiffeomorphismBRSTMinusInput_apply,
    finiteFrameSharedMetricDiffeomorphismBRSTInput_apply,
    finiteFrameC2DiffeomorphismBRSTAction_zero_nonminimal]

theorem finiteFramePairedC2FullBRSTGaugeAction_zero_fields
    (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusReference minusReference : SmoothGeneralLorentzMetric period hPeriod)
    (metric : GeneralMetricRelativeC2Core period hPeriod plusFrame plusReference ×
      GeneralMetricRelativeC2Core period hPeriod minusFrame minusReference)
    (couplings : GlobalCandidateAActionCouplings) :
    finiteFramePairedC2FullBRSTGaugeAction period hPeriod source plusFrame minusFrame
      plusReference minusReference couplings (metric, 0) = 0 := by
  simp [finiteFramePairedC2FullBRSTGaugeAction,
    finiteFramePairedC2FullBRSTGaugeAbelianProjection_apply,
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_apply,
    finiteFramePairedC2AbelianBRSTAction_zero_fields,
    finiteFramePairedDiffeomorphismBRSTAction_zero_nonminimal]

/-- With every gauge and nonminimal field zero, the full-BRST action is
identically zero along the metric fiber, so its metric derivative vanishes. -/
theorem finiteFramePairedC2FullBRSTGaugeEuler_zero_fields_metric_apply
    (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusReference minusReference : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (base direction : GeneralMetricRelativeC2Core period hPeriod plusFrame plusReference ×
      GeneralMetricRelativeC2Core period hPeriod minusFrame minusReference)
    (hBase : (base, 0) ∈ finiteFramePairedC2FullBRSTGaugeDomain period hPeriod source
      plusFrame minusFrame plusReference minusReference) :
    finiteFramePairedC2FullBRSTGaugeEuler period hPeriod source plusFrame minusFrame
        plusReference minusReference couplings (base, 0) (direction, 0) = 0 := by
  let Fields := FiniteFramePairedC2AbelianGaugeFields period hPeriod plusFrame minusFrame ×
    FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source
  let MetricPair := GeneralMetricRelativeC2Core period hPeriod plusFrame plusReference ×
    GeneralMetricRelativeC2Core period hPeriod minusFrame minusReference
  have hFull := finiteFramePairedC2FullBRSTGaugeAction_hasFDerivAt period hPeriod source
    plusFrame minusFrame plusReference minusReference couplings (base, (0 : Fields)) hBase
  have hMetric := hFull.comp base
    (hasFDerivAt_prodMk_left (𝕜 := Real) base (0 : Fields))
  simp only [Function.comp_def] at hMetric
  have hFunctions :
      (fun current : MetricPair =>
        finiteFramePairedC2FullBRSTGaugeAction period hPeriod source plusFrame minusFrame
          plusReference minusReference couplings (current, (0 : Fields))) =
        (fun _ : MetricPair => (0 : Real)) := by
    funext current
    exact finiteFramePairedC2FullBRSTGaugeAction_zero_fields period hPeriod source plusFrame
      minusFrame plusReference minusReference current couplings
  rw [hFunctions] at hMetric
  have hMaps := hMetric.unique (hasFDerivAt_const (x := base) (c := (0 : Real)))
  have hApply := DFunLike.congr_fun hMaps direction
  simpa [ContinuousLinearMap.comp_apply] using hApply

/-- At zero gauge fields, the physical metric Euler at the genuine paired
center is exactly the single mobile Einstein--Hilbert--interaction residual
pairing. -/
theorem finiteFramePairedC2PhysicalMetricEuler_zero_smooth_lifts_eq_residualPairing
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
          plusBase minusBase hRoot couplings interactionScale coefficients) test := by
  dsimp only
  let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let hFiniteRegular :=
    regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
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
            couplings interactionScale coefficients) test
  have hGeometryMinusTensor : geometry.minusMetric.tensor = minusBase.metric.tensor := by
    dsimp only [geometry]
    rw [regularGeneralMetricC2LorentzChartGeometry_minusMetric,
      regularGeneralMetricC2LorentzChartMetric_tensor]
    abel
  have hCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame =
      smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
        (minusBase.metric.tensor - plusBase.metric.tensor) := by
    unfold finiteFramePairedC2MinusCenter
    change smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
      (geometry.minusMetric.tensor - plusBase.metric.tensor) = _
    rw [hGeometryMinusTensor]
  have hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric := by
    rw [hCenter]
    change smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
      (minusBase.metric.tensor - plusBase.metric.tensor) ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame plusBase.metric
    exact hShift
  have hBRSTBase :
      ((0, finiteFramePairedC2MinusCenter period hPeriod geometry frame), 0) ∈
        finiteFramePairedC2FullBRSTGaugeDomain period hPeriod frame frame frame
          geometry.plusMetric geometry.plusMetric :=
    ⟨⟨zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric,
      hMinusCenter⟩, Set.mem_univ _⟩
  have hBridge :=
    finiteFramePairedC2PhysicalMetricEuler_zero_smooth_lifts_eq_residualPairing_add_fullBRST
      period hPeriod plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hChart frame
      hShift hZero couplings interactionScale coefficients plusVariation minusVariation
  dsimp only at hBridge
  have hBRST := finiteFramePairedC2FullBRSTGaugeEuler_zero_fields_metric_apply period hPeriod
    frame frame frame geometry.plusMetric geometry.plusMetric couplings
    (0, finiteFramePairedC2MinusCenter period hPeriod geometry frame) finiteDirection hBRSTBase
  rw [hBridge]
  simp only [finiteFramePairedC2PhysicalRecenter_zero]
  rw [hBRST, add_zero]


end
end P0EFTJanusFiniteFramePairedC2FullBRSTMetricCenterVanishing4D
end JanusFormal
