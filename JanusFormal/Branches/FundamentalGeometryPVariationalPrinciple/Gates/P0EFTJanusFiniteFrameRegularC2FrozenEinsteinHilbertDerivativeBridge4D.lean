import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2EinsteinHilbertFrozenVolumeDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzChartAffineRecenterGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStoredVolumePalatiniMetricResidual4D

/-! # Frozen Einstein--Hilbert derivative across the finite-frame/regular bridge -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2FrozenEinsteinHilbertDerivativeBridge4D

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
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothScalarCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2ProjectedScalarGlobalAgreement4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertFrozenVolumeDecomposition4D
open P0EFTJanusLorentzChartAffineRecenterGeometry4D
open P0EFTJanusStoredVolumePalatiniMetricResidual4D

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

private theorem hasDerivAt_action_origin_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {action : E → Real} {derivative : E →L[Real] Real}
    (hAction : HasFDerivAt action derivative 0) (direction : E) :
    HasDerivAt (fun t : Real => action (t • direction)) (derivative direction) 0 := by
  have hLine : HasDerivAt (fun t : Real => (0 : E) + t • direction) direction 0 := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const (x := (0 : Real)) (c := (0 : E))).fun_add
        ((hasDerivAt_id' (0 : Real)).smul_const direction)
  simpa only [Function.comp_def, zero_add] using
    hAction.comp_hasDerivAt_of_eq 0 hLine (by simp only [zero_smul, add_zero])

private theorem smul_line_eventually_mem_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {domain : Set E} (hOpen : IsOpen domain) (hZero : (0 : E) ∈ domain)
    (direction : E) :
    ∀ᶠ t : Real in 𝓝 0, t • direction ∈ domain := by
  have hContinuous : Continuous (fun t : Real => t • direction) :=
    continuous_id.smul continuous_const
  have hAt : (fun t : Real => t • direction) 0 ∈ domain := by
    simpa only [zero_smul] using hZero
  exact hContinuous.continuousAt.eventually (hOpen.mem_nhds hAt)

/-- On a common admissible smooth lift and in canonical-volume gauge, the
finite frozen density is the regular fixed-volume density. -/
theorem finiteFrameC2FrozenVolumeEinsteinHilbertDensity_smooth_regular
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : metric.volume =
      globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hFinite : smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame metric.metric)
    (hRegular : regularGeneralMetricSmoothC2Variation period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (couplings : EinsteinHilbertCouplings) :
    finiteFrameC2FrozenVolumeEinsteinHilbertDensity period hPeriod frame metric.metric couplings
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor) =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod metric couplings
        (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) := by
  let varied := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric tensor hRegular
  have hVaried : varied.metric.tensor = metric.metric.tensor + tensor :=
    regularGeneralMetricC2LorentzChartMetric_tensor period hPeriod metric tensor hRegular
  have hFiniteScalar :=
    finiteFrameProjectedScalarCurvatureC0_smooth_eq_global period hPeriod frame metric.metric
      varied.metric tensor hVaried hFinite.1
  have hRegularScalar :=
    regularGeneralMetricC0ScalarCurvature_smooth period hPeriod metric tensor varied.metric
      hVaried hRegular.1
  unfold finiteFrameC2FrozenVolumeEinsteinHilbertDensity
    regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity
  rw [finiteFrameCanonicalVolumeC0_zero, ← hCanonicalVolume, hFiniteScalar]
  simp only [regularGeneralMetricSmoothC2Variation] at hRegularScalar ⊢
  rw [hRegularScalar]
  rfl

/-- Integration preserves the smooth finite/regular fixed-volume agreement. -/
theorem finiteFrameC2FrozenVolumeEinsteinHilbertAction_smooth_regular
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : metric.volume =
      globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hFinite : smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame metric.metric)
    (hRegular : regularGeneralMetricSmoothC2Variation period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (couplings : EinsteinHilbertCouplings) :
    finiteFrameC2FrozenVolumeEinsteinHilbertAction period hPeriod frame metric.metric couplings
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor) =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
        (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) := by
  have hDensity :=
    finiteFrameC2FrozenVolumeEinsteinHilbertDensity_smooth_regular period hPeriod metric
      hCanonicalVolume frame tensor hFinite hRegular couplings
  unfold finiteFrameC2FrozenVolumeEinsteinHilbertAction
    regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
  calc
    _ = ∫ point,
        finiteFrameC2FrozenVolumeEinsteinHilbertDensity period hPeriod frame metric.metric couplings
          (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor) point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod :=
      finiteFrameBRSTCanonicalIntegralCLM_apply period hPeriod _
    _ = ∫ point,
        regularGeneralMetricC0FixedVolumeEinsteinHilbertDensity period hPeriod metric couplings
          (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun point =>
        congrArg (fun field : C(EffectiveQuotient period hPeriod, Real) => field point) hDensity)
    _ = _ := (regularGeneralMetricC0IntegralCLM_apply period hPeriod
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) _).symm

/-- The finite frozen action and regular fixed-volume action have the same germ
at zero along every common smooth tensor line. -/
theorem finiteFrameC2FrozenVolumeEinsteinHilbertAction_line_eventuallyEq_regular
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : metric.volume =
      globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    (fun t : Real => finiteFrameC2FrozenVolumeEinsteinHilbertAction period hPeriod frame
      metric.metric couplings
        (t • smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor)) =ᶠ[𝓝 0]
    (fun t : Real => regularGeneralMetricC0FixedVolumeEinsteinHilbertAction period hPeriod metric
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
        (t • regularGeneralMetricSmoothC2Variation period hPeriod metric tensor)) := by
  let finiteDirection :=
    smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor
  let regularDirection := regularGeneralMetricSmoothC2Variation period hPeriod metric tensor
  have hFiniteEvent : ∀ᶠ t : Real in 𝓝 0,
      t • finiteDirection ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame metric.metric :=
    smul_line_eventually_mem_open
      (generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame metric.metric)
      (zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame metric.metric)
      finiteDirection
  have hRegularEvent : ∀ᶠ t : Real in 𝓝 0,
      t • regularDirection ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod metric :=
    smul_line_eventually_mem_open
      (regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod metric)
      (zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
      regularDirection
  filter_upwards [hFiniteEvent, hRegularEvent] with t htFinite htRegular
  have htFinite' :
      smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric (t • tensor) ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame metric.metric := by
    simpa only [map_smul] using htFinite
  have htRegular' : regularGeneralMetricSmoothC2Variation period hPeriod metric (t • tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric := by
    simpa only [regularDirection, regularGeneralMetricSmoothC2Variation, map_smul] using htRegular
  simpa only [finiteDirection, regularDirection, regularGeneralMetricSmoothC2Variation,
    map_smul] using
    finiteFrameC2FrozenVolumeEinsteinHilbertAction_smooth_regular period hPeriod metric
      hCanonicalVolume frame (t • tensor) htFinite' htRegular' couplings

/-- The actual finite frozen Euler at zero is the regular fixed-volume action
derivative on every common smooth lift. -/
theorem finiteFrameC2FrozenVolumeEinsteinHilbertEuler_zero_smooth_regularDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : metric.volume =
      globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    finiteFrameC2FrozenVolumeEinsteinHilbertEuler period hPeriod frame metric.metric couplings 0
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor) =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
        (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor) := by
  have hFiniteLine := hasDerivAt_action_origin_line
    (finiteFrameC2FrozenVolumeEinsteinHilbertAction_hasFDerivAt_zero period hPeriod frame
      metric.metric couplings)
    (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor)
  have hRegularLine := hasDerivAt_action_origin_line
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_hasFDerivAt_zero period hPeriod metric
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings)
    (regularGeneralMetricSmoothC2Variation period hPeriod metric tensor)
  have hGerm :=
    finiteFrameC2FrozenVolumeEinsteinHilbertAction_line_eventuallyEq_regular period hPeriod metric
      hCanonicalVolume frame tensor couplings
  exact hFiniteLine.unique (hRegularLine.congr_of_eventuallyEq hGerm)

/-- Thus the finite frozen Euler has the already established strong stored-volume
Einstein--Hilbert residual on every smooth direction. -/
theorem finiteFrameC2FrozenVolumeEinsteinHilbertEuler_zero_smooth_eq_storedVolumeResidualPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hCanonicalVolume : metric.volume =
      globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (frame : SmoothD8Frame period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (couplings : EinsteinHilbertCouplings) :
    finiteFrameC2FrozenVolumeEinsteinHilbertEuler period hPeriod frame metric.metric couplings 0
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame metric.metric tensor) =
      ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod metric
          couplings.gravitationalCoupling) tensor point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [finiteFrameC2FrozenVolumeEinsteinHilbertEuler_zero_smooth_regularDerivative period hPeriod
    metric hCanonicalVolume frame tensor couplings]
  simpa only [regularGeneralMetricSmoothC2Variation, regularGeneralMetricC2SmoothDirection] using
    regularFrameFixedVolumeEinsteinHilbertDerivative_eq_ungaugedResidualIntegral period hPeriod
      metric couplings tensor

end
end P0EFTJanusFiniteFrameRegularC2FrozenEinsteinHilbertDerivativeBridge4D
end JanusFormal
