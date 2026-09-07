import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D

/-! # First variation of the authentic moving-frame Maxwell action

The metric derivative splits into the fixed-frame metric derivative and the
gauge derivative evaluated on the root-induced velocity. No gauge equation or
vanishing current is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellPairingDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2FixedVolumeMaxwellActionBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- Chain rule on a graph, retaining both partial derivatives. -/
private theorem fderiv_graph_eq_partial_add
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (action : E → G → Real) (coefficients : G)
    (transport : E → G) (velocity : E →L[Real] G)
    (hJoint : DifferentiableAt Real
      (fun input : E × G => action input.1 input.2) (0, coefficients))
    (hTransport : HasFDerivAt transport velocity 0)
    (hCenter : transport 0 = coefficients) (direction : E) :
    fderiv Real (fun variation => action variation (transport variation)) 0 direction =
      fderiv Real (fun variation => action variation coefficients) 0 direction +
        fderiv Real (action 0) coefficients (velocity direction) := by
  let joint := fun input : E × G => action input.1 input.2
  let derivative := fderiv Real joint (0, coefficients)
  have hJoint' : HasFDerivAt joint derivative (0, coefficients) :=
    hJoint.hasFDerivAt
  have hMetric : HasFDerivAt (fun variation => action variation coefficients)
      (derivative.comp (ContinuousLinearMap.inl Real E G)) 0 := by
    simpa only [Function.comp_def, joint] using
      hJoint'.comp (0 : E) (hasFDerivAt_prodMk_left (𝕜 := Real) (0 : E) coefficients)
  have hGauge : HasFDerivAt (action 0)
      (derivative.comp (ContinuousLinearMap.inr Real E G)) coefficients := by
    simpa only [Function.comp_def, joint] using
      hJoint'.comp coefficients (hasFDerivAt_prodMk_right (0 : E) coefficients)
  have hAtGraph : HasFDerivAt joint derivative (0, transport 0) := by
    simpa only [hCenter] using hJoint'
  have hMobile : HasFDerivAt
      (fun variation => action variation (transport variation))
      (derivative.comp ((ContinuousLinearMap.id Real E).prod velocity)) 0 := by
    simpa only [Function.comp_def, joint, id_eq] using
      hAtGraph.comp (0 : E) ((hasFDerivAt_id (0 : E)).prodMk hTransport)
  rw [hMobile.fderiv, hMetric.fderiv, hGauge.fderiv]
  change derivative (direction, velocity direction) =
    derivative (direction, 0) + derivative (0, velocity direction)
  have hPair : (direction, velocity direction) =
      (direction, (0 : G)) + ((0 : E), velocity direction) := by
    ext <;> simp
  rw [hPair, map_add]

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C2Matrix := C2FiniteMatrix period hPeriod 4
private abbrev GaugeC2Core := RegularGeneralMetricC2GaugeCoefficientCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

@[simp]
theorem gaugeCoefficientC2CoreFrameTransport_identity
    (coefficients : GaugeC2Core period hPeriod) :
    gaugeCoefficientC2CoreFrameTransport period hPeriod
      (c2FiniteMatrixIdentity period hPeriod 4) coefficients = coefficients := by
  have hSymmetric (first second : Fin 4) :
      c2FiniteMatrixIdentity period hPeriod 4 first second =
        c2FiniteMatrixIdentity period hPeriod 4 second first := by
    apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
    simp only [smoothFiniteMatrixIdentity, eq_comm]
  funext baseIndex component
  let matrix : C2Matrix period hPeriod := fun row _ => coefficients row component
  have hProduct := congrArg (fun value : C2Matrix period hPeriod => value baseIndex 0)
    (c2FiniteMatrixProduct_identity_left period hPeriod 4 matrix)
  change (∑ movingIndex : Fin 4,
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (c2FiniteMatrixIdentity period hPeriod 4 movingIndex baseIndex)
      (coefficients movingIndex component)) = coefficients baseIndex component
  simpa only [c2FiniteMatrixProduct_apply, matrix, hSymmetric] using hProduct

@[simp]
theorem regularGeneralMetricC2MobileGaugeCoefficientTransport_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeC2Core period hPeriod) :
    regularGeneralMetricC2MobileGaugeCoefficientTransport period hPeriod metric
      0 coefficients = coefficients := by
  simp only [regularGeneralMetricC2MobileGaugeCoefficientTransport, map_zero,
    c2IdentityRootBranch_zero, gaugeCoefficientC2CoreFrameTransport_identity]

/-- The induced gauge velocity is a continuous linear function of the
metric direction. Its sign is positive for the transpose-root transport. -/
def regularGeneralMetricC2InducedGaugeVelocityCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeC2Core period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real] GaugeC2Core period hPeriod :=
  (1 / 2 : Real) •
    (gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod coefficients).comp
      (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric)

@[simp]
theorem regularGeneralMetricC2InducedGaugeVelocityCLM_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeC2Core period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC2InducedGaugeVelocityCLM period hPeriod metric coefficients direction =
      (1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod
        (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric direction)
        coefficients := by
  simp only [regularGeneralMetricC2InducedGaugeVelocityCLM, smul_apply,
    ContinuousLinearMap.comp_apply, gaugeCoefficientC2CoreFrameTransportLeftCLM_apply]

theorem regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_differentiableAt_center
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (coefficients : GaugeC2Core period hPeriod) :
    DifferentiableAt Real
      (fun input : RegularGeneralMetricC2Core period hPeriod metric ×
          GaugeC2Core period hPeriod =>
        regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure input.1 input.2)
      (0, coefficients) := by
  have hOpen : IsOpen
      (regularGeneralMetricC2GaugeCoefficientMaxwellDomain period hPeriod metric) :=
    (regularGeneralMetricC2Domain_isOpen period hPeriod metric).prod isOpen_univ
  have hCenter : (0, coefficients) ∈
      regularGeneralMetricC2GaugeCoefficientMaxwellDomain period hPeriod metric :=
    ⟨zero_mem_regularGeneralMetricC2Domain period hPeriod metric, Set.mem_univ _⟩
  exact ((regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
    period hPeriod metric measure).contDiffAt (hOpen.mem_nhds hCenter)).differentiableAt
      (by norm_num)

/-- Exact derivative of the moving-frame action at the metric centre. The
second summand is the genuine coefficient derivative on the induced velocity. -/
theorem regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_fderiv_zero_split
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (coefficients : GaugeC2Core period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure variation coefficients) 0 direction =
      fderiv Real
          (fun variation => regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
            period hPeriod metric measure variation coefficients) 0 direction +
        fderiv Real
          (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
            period hPeriod metric measure 0) coefficients
          ((1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod
            (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM
              period hPeriod metric direction) coefficients) := by
  have hSplit := fderiv_graph_eq_partial_add
    (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod metric measure) coefficients
    (fun variation => regularGeneralMetricC2MobileGaugeCoefficientTransport
      period hPeriod metric variation coefficients)
    (regularGeneralMetricC2InducedGaugeVelocityCLM period hPeriod metric coefficients)
    (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_differentiableAt_center
      period hPeriod metric measure coefficients)
    (regularGeneralMetricC2MobileGaugeCoefficientTransport_hasFDerivAt_zero
      period hPeriod metric coefficients)
    (regularGeneralMetricC2MobileGaugeCoefficientTransport_zero
      period hPeriod metric coefficients) direction
  simpa only [regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction,
    regularGeneralMetricC2InducedGaugeVelocityCLM_apply] using hSplit

/-- On a smooth potential the metric summand is exactly the established
fixed-potential, fixed-volume action, for every completed metric direction. -/
theorem regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_fderiv_zero_smoothPotential
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      (gaugePotentialFrameCoefficients period hPeriod metric potential)
    fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure variation coefficients) 0 direction =
      fderiv Real
          (regularGeneralMetricC0FixedVolumeMaxwellAction
            period hPeriod metric measure potential potential) 0 direction +
        fderiv Real
          (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
            period hPeriod metric measure 0) coefficients
          ((1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod
            (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM
              period hPeriod metric direction) coefficients) := by
  dsimp only
  have hFixed :
      (fun variation => regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric measure variation
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            (gaugePotentialFrameCoefficients period hPeriod metric potential))) =
      regularGeneralMetricC0FixedVolumeMaxwellAction
        period hPeriod metric measure potential potential := by
    funext variation
    exact regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_frameCoefficients
      period hPeriod metric measure variation potential
  rw [← hFixed]
  exact regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_fderiv_zero_split
    period hPeriod metric measure _ direction

/-- Positive-sign correction when the normalized Maxwell action freezes its volume. -/
def regularGeneralMetricC2FixedVolumeMaxwellCorrection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) : Real :=
  (1 / 4 : Real) * canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (regularGeneralMetricC2VolumeDerivativeAtZero period hPeriod metric direction)
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (globalSmoothMaxwellPairing period hPeriod metric.metric potential potential)))

theorem regularGeneralMetricC2FixedVolumeMaxwellCorrection_eq_integral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC2FixedVolumeMaxwellCorrection
        period hPeriod metric measure potential direction =
      ∫ point, (1 / 4 : Real) *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (regularGeneralMetricC2VolumeDerivativeAtZero period hPeriod metric direction) point *
        globalMaxwellPairing period hPeriod metric.metric potential potential point ∂measure := by
  rw [regularGeneralMetricC2FixedVolumeMaxwellCorrection,
    canonicalPhysicalC2ScalarIntegralCLM_apply, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point => by
    change (1 / 4 : Real) *
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (regularGeneralMetricC2VolumeDerivativeAtZero period hPeriod metric direction) point *
        globalMaxwellPairing period hPeriod metric.metric potential potential point) = _
    ring

theorem regularGeneralMetricC0FixedVolumeMaxwellAction_fderiv_zero_eq_variable_add_correction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    fderiv Real (regularGeneralMetricC0FixedVolumeMaxwellAction
        period hPeriod metric measure potential potential) 0 direction =
      regularGeneralMetricC2IntegratedMaxwellActionDerivativeAtZero
        period hPeriod metric measure potential direction +
      regularGeneralMetricC2FixedVolumeMaxwellCorrection
        period hPeriod metric measure potential direction := by
  let pairing := regularGeneralMetricC2MaxwellPairing
    period hPeriod metric potential potential
  let product := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
    (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod metric.volume)
  let integral := canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure
  have hFixed : regularGeneralMetricC0FixedVolumeMaxwellAction
      period hPeriod metric measure potential potential =
      (fun variation => -(1 / 4 : Real) * integral (product (pairing variation))) := by
    funext variation
    unfold regularGeneralMetricC0FixedVolumeMaxwellAction
    rw [regularGeneralMetricC0IntegralCLM_apply]
    dsimp only [integral]
    rw [canonicalPhysicalC2ScalarIntegralCLM_apply, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun point => by
      change metric.volume point * (-(1 / 4 : Real) *
          canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (pairing variation) point) =
        -(1 / 4 : Real) * (metric.volume point *
          canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (pairing variation) point)
      ring
  have hPairing := regularGeneralMetricC2MaxwellPairing_hasFDerivAt_zero
    period hPeriod metric potential potential
  have hDerivative := (integral.hasFDerivAt.comp
    (0 : RegularGeneralMetricC2Core period hPeriod metric)
    (product.hasFDerivAt.comp (0 : RegularGeneralMetricC2Core period hPeriod metric)
      hPairing)).const_mul (-(1 / 4 : Real))
  have hFixedDerivative :
      fderiv Real (regularGeneralMetricC0FixedVolumeMaxwellAction
        period hPeriod metric measure potential potential) 0 direction =
      -(1 / 4 : Real) * integral (product
        (regularGeneralMetricC2MaxwellPairingDerivativeAtZero
          period hPeriod metric potential potential direction)) := by
    rw [hFixed]
    simpa only [Function.comp_def, smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, pairing]
      using congrArg (fun derivative => derivative direction) hDerivative.fderiv
  rw [hFixedDerivative]
  simp only [regularGeneralMetricC2IntegratedMaxwellActionDerivativeAtZero,
    regularGeneralMetricC2IntegratedMaxwellPairingDerivativeAtZero,
    smul_apply, ContinuousLinearMap.comp_apply]
  rw [regularGeneralMetricC2MaxwellDensityDerivativeAtZero_smoothBase, map_add]
  change -(1 / 4 : Real) * integral (product
      (regularGeneralMetricC2MaxwellPairingDerivativeAtZero
        period hPeriod metric potential potential direction)) =
    -(1 / 4 : Real) * (integral (product
      (regularGeneralMetricC2MaxwellPairingDerivativeAtZero
        period hPeriod metric potential potential direction)) +
      integral (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (regularGeneralMetricC2VolumeDerivativeAtZero period hPeriod metric direction)
        (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (globalSmoothMaxwellPairing period hPeriod metric.metric potential potential)))) +
    (1 / 4 : Real) * integral (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (regularGeneralMetricC2VolumeDerivativeAtZero period hPeriod metric direction)
      (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (globalSmoothMaxwellPairing period hPeriod metric.metric potential potential)))
  ring

/-- The authentic smooth metric variation contains stress, volume correction,
and the induced gauge derivative, without any stationarity hypothesis. -/
theorem strongMaxwellMetricCenterFirstVariation_eq_stress_add_volume_add_inducedGauge
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      (gaugePotentialFrameCoefficients period hPeriod metric potential)
    let direction := regularGeneralMetricC2SmoothDirection period hPeriod metric tensor
    fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure variation coefficients) 0 direction =
      (∫ point, metric.volume point / 2 *
        generalMetricTensorPairingAt period hPeriod metric.metric
          (regularGeneralMetricMaxwellStressTensor period hPeriod metric potential)
          tensor point ∂measure) +
      regularGeneralMetricC2FixedVolumeMaxwellCorrection
        period hPeriod metric measure potential direction +
      fderiv Real (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric measure 0) coefficients
        ((1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod
          (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM
            period hPeriod metric direction) coefficients) := by
  dsimp only
  rw [regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_fderiv_zero_smoothPotential,
    regularGeneralMetricC0FixedVolumeMaxwellAction_fderiv_zero_eq_variable_add_correction,
    regularGeneralMetricC2IntegratedMaxwellActionDerivative_smooth_invariant]

end
end P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
end JanusFormal
