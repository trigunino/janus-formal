import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2MobileEinsteinHilbertResidualBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ProjectedEinsteinHilbertAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzChartAffineRecenterGeometry4D

/-! # Finite-frame Einstein--Hilbert derivative under a smooth metric recentering -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2EinsteinHilbertDerivativeRecenter4D

set_option autoImplicit false
set_option maxHeartbeats 5000000
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
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
open P0EFTJanusFiniteFrameC2ProjectedEinsteinHilbertAgreement4D
open P0EFTJanusFiniteFrameC2ProjectedScalarGlobalAgreement4D
open P0EFTJanusFiniteFrameRegularC2MobileEinsteinHilbertResidualBridge4D

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

private theorem hasDerivAt_action_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {action : E → Real} {base : E} {derivative : E →L[Real] Real}
    (hAction : HasFDerivAt action derivative base) (direction : E) :
    HasDerivAt (fun t : Real => action (base + t • direction))
      (derivative direction) 0 := by
  have hLine : HasDerivAt (fun t : Real => base + t • direction) direction 0 := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const (x := (0 : Real)) (c := base)).fun_add
        ((hasDerivAt_id' (0 : Real)).smul_const direction)
  simpa only [Function.comp_def] using
    hAction.comp_hasDerivAt_of_eq 0 hLine (by simp only [zero_smul, add_zero])

private theorem hasDerivAt_action_origin_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {action : E → Real} {derivative : E →L[Real] Real}
    (hAction : HasFDerivAt action derivative 0) (direction : E) :
    HasDerivAt (fun t : Real => action (t • direction)) (derivative direction) 0 := by
  simpa only [zero_add] using hasDerivAt_action_affine_line hAction direction

private theorem affine_line_eventually_mem_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {domain : Set E} (hOpen : IsOpen domain) {base : E} (hBase : base ∈ domain)
    (direction : E) :
    ∀ᶠ t : Real in 𝓝 0, base + t • direction ∈ domain := by
  have hContinuous : Continuous (fun t : Real => base + t • direction) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hAt : (fun t : Real => base + t • direction) 0 ∈ domain := by
    simpa only [zero_smul, add_zero] using hBase
  exact hContinuous.continuousAt.eventually (hOpen.mem_nhds hAt)

private theorem smul_line_eventually_mem_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {domain : Set E} (hOpen : IsOpen domain) (hZero : (0 : E) ∈ domain)
    (direction : E) :
    ∀ᶠ t : Real in 𝓝 0, t • direction ∈ domain := by
  simpa only [zero_add] using
    affine_line_eventually_mem_open hOpen hZero direction

/-- A smooth finite EH action is the canonical global scalar-curvature
integral, independently of its finite-frame base metric. -/
theorem finiteFrameC2EinsteinHilbertAction_smooth_eq_global
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + tensor)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)
    (couplings : EinsteinHilbertCouplings) :
    finiteFrameC2EinsteinHilbertAction period hPeriod frame baseMetric couplings
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) =
      ∫ point, globalMetricVolumeRatio period hPeriod metric point *
        ((1 / (2 * couplings.gravitationalCoupling)) *
          (globalSmoothScalarCurvature period hPeriod metric point -
            2 * couplings.cosmologicalConstant))
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [finiteFrameC2EinsteinHilbertAction_smooth period hPeriod frame baseMetric couplings tensor
    metric hMetric hVariation]
  apply integral_congr_ae
  filter_upwards [] with point
  unfold finiteFrameSmoothProjectedEinsteinHilbertDensity
  have hScalar := congrArg (fun field : SmoothScalarField period hPeriod => field point)
    (finiteFrameSmoothProjectedScalarCurvature_eq_global period hPeriod frame baseMetric metric)
  change globalMetricVolumeRatio period hPeriod metric point *
      ((1 / (2 * couplings.gravitationalCoupling)) *
        (finiteFrameSmoothProjectedScalarCurvature period hPeriod frame baseMetric metric point -
          2 * couplings.cosmologicalConstant)) = _
  rw [hScalar]

/-- The old and recentered finite EH charts represent the same action germ
along every smooth tensor direction. -/
theorem finiteFrameC2EinsteinHilbertAction_line_eventuallyEq_recenter
    (frame : SmoothD8Frame period hPeriod)
    (oldBase newBase : RegularGeneralLorentzMetric period hPeriod)
    (hShift : smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric
        (newBase.metric.tensor - oldBase.metric.tensor) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame oldBase.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    let shift := smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric
      (newBase.metric.tensor - oldBase.metric.tensor)
    let oldDirection := smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric tensor
    let newDirection := smoothToGeneralMetricRelativeC2Core period hPeriod frame newBase.metric tensor
    (fun t : Real => finiteFrameC2EinsteinHilbertAction period hPeriod frame oldBase.metric couplings
      (shift + t • oldDirection)) =ᶠ[𝓝 0]
    (fun t : Real => finiteFrameC2EinsteinHilbertAction period hPeriod frame newBase.metric couplings
      (t • newDirection)) := by
  dsimp only
  let shiftTensor := newBase.metric.tensor - oldBase.metric.tensor
  let shift := smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric shiftTensor
  let oldDirection := smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric tensor
  let newDirection := smoothToGeneralMetricRelativeC2Core period hPeriod frame newBase.metric tensor
  let regularDirection := regularGeneralMetricSmoothC2Variation period hPeriod newBase tensor
  have hOldEvent : ∀ᶠ t : Real in 𝓝 0,
      shift + t • oldDirection ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame oldBase.metric :=
    affine_line_eventually_mem_open
      (generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame oldBase.metric) hShift
      oldDirection
  have hNewEvent : ∀ᶠ t : Real in 𝓝 0,
      t • newDirection ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame newBase.metric :=
    smul_line_eventually_mem_open
      (generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame newBase.metric)
      (zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame newBase.metric)
      newDirection
  have hRegularEvent : ∀ᶠ t : Real in 𝓝 0,
      t • regularDirection ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod newBase :=
    smul_line_eventually_mem_open
      (regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod newBase)
      (zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod newBase)
      regularDirection
  filter_upwards [hOldEvent, hNewEvent, hRegularEvent] with t htOld htNew htRegular
  have htOld' : smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric
      (shiftTensor + t • tensor) ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame oldBase.metric := by
    simpa only [shift, oldDirection, map_add, map_smul] using htOld
  have htNew' : smoothToGeneralMetricRelativeC2Core period hPeriod frame newBase.metric
      (t • tensor) ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame newBase.metric := by
    simpa only [newDirection, map_smul] using htNew
  have htRegular' : regularGeneralMetricSmoothC2Variation period hPeriod newBase (t • tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod newBase := by
    simpa only [regularDirection, regularGeneralMetricSmoothC2Variation, map_smul] using htRegular
  let varied := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod newBase
    (t • tensor) htRegular'
  have hVaried : varied.metric.tensor = newBase.metric.tensor + t • tensor :=
    regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod newBase (t • tensor) htRegular'
  have hOldMetric : varied.metric.tensor = oldBase.metric.tensor + (shiftTensor + t • tensor) := by
    rw [hVaried]
    dsimp only [shiftTensor]
    abel
  have hOldAction := finiteFrameC2EinsteinHilbertAction_smooth_eq_global period hPeriod frame
    oldBase.metric varied.metric (shiftTensor + t • tensor) hOldMetric htOld' couplings
  have hNewAction := finiteFrameC2EinsteinHilbertAction_smooth_eq_global period hPeriod frame
    newBase.metric varied.metric (t • tensor) hVaried htNew' couplings
  simpa only [shift, oldDirection, newDirection, shiftTensor, map_add, map_smul] using
    hOldAction.trans hNewAction.symm

/-- The finite EH derivative at a smooth shifted metric is the center
derivative in the recentered finite chart. -/
theorem finiteFrameC2EinsteinHilbertEuler_smooth_recenter
    (frame : SmoothD8Frame period hPeriod)
    (oldBase newBase : RegularGeneralLorentzMetric period hPeriod)
    (hShift : smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric
        (newBase.metric.tensor - oldBase.metric.tensor) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame oldBase.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    let shift := smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric
      (newBase.metric.tensor - oldBase.metric.tensor)
    finiteFrameC2EinsteinHilbertEuler period hPeriod frame oldBase.metric couplings shift
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric tensor) =
      finiteFrameC2EinsteinHilbertEuler period hPeriod frame newBase.metric couplings 0
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame newBase.metric tensor) := by
  dsimp only
  let shift := smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric
    (newBase.metric.tensor - oldBase.metric.tensor)
  let oldDirection := smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric tensor
  let newDirection := smoothToGeneralMetricRelativeC2Core period hPeriod frame newBase.metric tensor
  have hOldLine := hasDerivAt_action_affine_line
    (finiteFrameC2EinsteinHilbertAction_hasFDerivAt period hPeriod frame oldBase.metric couplings
      shift hShift) oldDirection
  have hNewLine := hasDerivAt_action_origin_line
    (finiteFrameC2EinsteinHilbertAction_hasFDerivAt period hPeriod frame newBase.metric couplings 0
      (zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame newBase.metric)) newDirection
  have hGerm := finiteFrameC2EinsteinHilbertAction_line_eventuallyEq_recenter period hPeriod frame
    oldBase newBase hShift tensor couplings
  exact hOldLine.unique (hNewLine.congr_of_eventuallyEq hGerm)

/-- After recentering, the off-center finite EH Euler has the mobile strong
residual of the new metric. -/
theorem finiteFrameC2EinsteinHilbertEuler_smooth_recenter_eq_mobileResidualPairing
    (frame : SmoothD8Frame period hPeriod)
    (oldBase newBase : RegularGeneralLorentzMetric period hPeriod)
    (hShift : smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric
        (newBase.metric.tensor - oldBase.metric.tensor) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame oldBase.metric)
    (hNewCanonicalVolume : newBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod newBase.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    let shift := smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric
      (newBase.metric.tensor - oldBase.metric.tensor)
    finiteFrameC2EinsteinHilbertEuler period hPeriod frame oldBase.metric couplings shift
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame oldBase.metric tensor) =
      ∫ point, generalMetricTensorPairingAt period hPeriod newBase.metric
        (regularFrameMobileEinsteinHilbertResidual period hPeriod newBase couplings)
        tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  dsimp only
  rw [finiteFrameC2EinsteinHilbertEuler_smooth_recenter period hPeriod frame oldBase newBase hShift
    tensor couplings]
  exact finiteFrameC2EinsteinHilbertEuler_zero_smooth_lift_eq_mobileResidualPairing period hPeriod
    frame newBase hNewCanonicalVolume couplings tensor

end
end P0EFTJanusFiniteFrameC2EinsteinHilbertDerivativeRecenter4D
end JanusFormal
