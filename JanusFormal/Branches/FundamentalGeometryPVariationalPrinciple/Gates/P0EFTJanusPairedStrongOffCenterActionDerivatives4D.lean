import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMaxwellCenterFirstVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMobileMaxwellDerivativeRecenter4D

/-! # Native action derivatives of paired strong metric tests away from zero

The metric coordinate and translated gauge packet are evaluated at the actual
admissible physical point. Only the gauge component of the test is zero.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongOffCenterActionDerivatives4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

private theorem fderiv_projected_eq
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup M] [NormedSpace Real M]
    (action : M → Real) (projection : E →L[Real] M)
    (point direction : E) (hAction : DifferentiableAt Real action (projection point)) :
    fderiv Real (fun current => action (projection current)) point direction =
      fderiv Real action (projection point) (projection direction) := by
  have h := hAction.hasFDerivAt.comp point projection.hasFDerivAt
  exact congrArg (fun derivative => derivative direction) h.fderiv

private theorem fderiv_scaled_projected_eq_metricSlice
    {E M G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup M] [NormedSpace Real M]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (action : M → G → Real) (coefficients : G) (scale : Real)
    (metricProjection : E →L[Real] M) (gaugeProjection : E →L[Real] G)
    (point direction : E)
    (hJoint : DifferentiableAt Real
      (fun input : M × G => action input.1 input.2)
      (metricProjection point, coefficients + gaugeProjection point))
    (hGauge : gaugeProjection direction = 0) :
    fderiv Real (fun current => scale *
        action (metricProjection current) (coefficients + gaugeProjection current))
        point direction =
      scale * fderiv Real
        (fun metric => action metric (coefficients + gaugeProjection point))
        (metricProjection point) (metricProjection direction) := by
  let derivative := fderiv Real (fun input : M × G => action input.1 input.2)
    (metricProjection point, coefficients + gaugeProjection point)
  have hInput : HasFDerivAt
      (fun current => (metricProjection current, coefficients + gaugeProjection current))
      (metricProjection.prod gaugeProjection) point := by
    simpa only [zero_add] using metricProjection.hasFDerivAt.prodMk
      ((hasFDerivAt_const (x := point) (c := coefficients)).fun_add
        gaugeProjection.hasFDerivAt)
  have hScaled : HasFDerivAt (fun current => scale *
      action (metricProjection current) (coefficients + gaugeProjection current))
      (scale • derivative.comp (metricProjection.prod gaugeProjection)) point := by
    simpa only [Function.comp_def] using
      (hJoint.hasFDerivAt.comp point hInput).const_mul scale
  have hMetric : HasFDerivAt
      (fun metric => action metric (coefficients + gaugeProjection point))
      (derivative.comp (ContinuousLinearMap.inl Real M G)) (metricProjection point) := by
    simpa only [Function.comp_def] using
      hJoint.hasFDerivAt.comp (metricProjection point)
        (hasFDerivAt_prodMk_left (𝕜 := Real) (metricProjection point)
          (coefficients + gaugeProjection point))
  rw [hScaled.fderiv, hMetric.fderiv]
  change scale * derivative (metricProjection direction, gaugeProjection direction) =
    scale * derivative (metricProjection direction, 0)
  rw [hGauge]

open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAffineTarget4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusMobileMaxwellDerivativeRecenter4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
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

attribute [local irreducible]
  regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
  regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
  regularGeneralMetricC0FixedVolumeEinsteinHilbertAction

section Paired
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod configuration.physical
  couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

/-- Native fixed-volume plus EH derivative at the actual admissible point. -/
theorem pairedStrongEinsteinHilbertPlusDerivative_eq_fixedVolume_fderiv
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hPoint : point ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      fderiv Real (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
        period hPeriod plusBase measure couplings.plusEinstein)
        (regularGeneralMetricSmoothC2Variation period hPeriod plusBase
          (point.1.completeVariation.fullMetricPerturbation .plus))
        (regularGeneralMetricC2SmoothDirection period hPeriod plusBase (test .plus)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let corePoint := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
    configuration data analysis realization plusBase minusBase point
  let coreDirection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
    configuration data analysis realization plusBase minusBase
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test)
  let projection :
      RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase →L[Real]
        RegularGeneralMetricC2Core period hPeriod plusBase :=
    (ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _)
  have hMetricPoint : corePoint.1.1 =
      regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (point.1.completeVariation.fullMetricPerturbation .plus) := rfl
  have hMetricDirection : coreDirection.1.1 =
      regularGeneralMetricC2SmoothDirection period hPeriod plusBase (test .plus) := rfl
  have hAt : DifferentiableAt Real (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
      period hPeriod plusBase measure couplings.plusEinstein) (projection corePoint) :=
    ((regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_contDiffOn_two
      period hPeriod plusBase measure couplings.plusEinstein).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod plusBase).mem_nhds
        hPoint.plus_mem.1)).differentiableAt (by norm_num)
  have hNative := fderiv_projected_eq
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
      period hPeriod plusBase measure couplings.plusEinstein)
    projection corePoint coreDirection hAt
  change fderiv Real (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
    period hPeriod plusBase minusBase measure couplings.plusEinstein) corePoint coreDirection = _
  unfold regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
  simpa only [projection, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', hMetricPoint, hMetricDirection] using hNative

/-- Native fixed-volume minus EH derivative at the actual admissible point. -/
theorem pairedStrongEinsteinHilbertMinusDerivative_eq_fixedVolume_fderiv
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hPoint : point ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      fderiv Real (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
        period hPeriod minusBase measure couplings.minusEinstein)
        (regularGeneralMetricSmoothC2Variation period hPeriod minusBase
          (point.1.completeVariation.fullMetricPerturbation .minus))
        (regularGeneralMetricC2SmoothDirection period hPeriod minusBase (test .minus)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let corePoint := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
    configuration data analysis realization plusBase minusBase point
  let coreDirection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
    configuration data analysis realization plusBase minusBase
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test)
  let projection :
      RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase →L[Real]
        RegularGeneralMetricC2Core period hPeriod minusBase :=
    (ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.fst Real _ _)
  have hMetricPoint : corePoint.1.2 =
      regularGeneralMetricSmoothC2Variation period hPeriod minusBase
        (point.1.completeVariation.fullMetricPerturbation .minus) := rfl
  have hMetricDirection : coreDirection.1.2 =
      regularGeneralMetricC2SmoothDirection period hPeriod minusBase (test .minus) := rfl
  have hAt : DifferentiableAt Real (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
      period hPeriod minusBase measure couplings.minusEinstein) (projection corePoint) :=
    ((regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_contDiffOn_two
      period hPeriod minusBase measure couplings.minusEinstein).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod minusBase).mem_nhds
        hPoint.minus_mem.1)).differentiableAt (by norm_num)
  have hNative := fderiv_projected_eq
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction
      period hPeriod minusBase measure couplings.minusEinstein)
    projection corePoint coreDirection hAt
  change fderiv Real (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
    period hPeriod plusBase minusBase measure couplings.minusEinstein) corePoint coreDirection = _
  unfold regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
  simpa only [projection, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', hMetricPoint, hMetricDirection] using hNative

/-- Native mobile plus Maxwell derivative with its translated gauge packet. -/
theorem pairedStrongMaxwellPlusDerivative_eq_native_fderiv
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hPoint : point ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      couplings.plusMaxwellScale * fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod plusBase measure variation
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            (configuration.physical.coefficientFields.gauge.1 +
              point.1.completeVariation.independent.gauge.1)))
        (regularGeneralMetricSmoothC2Variation period hPeriod plusBase
          (point.1.completeVariation.fullMetricPerturbation .plus))
        (regularGeneralMetricC2SmoothDirection period hPeriod plusBase (test .plus)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let corePoint := globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
    configuration data analysis realization plusBase minusBase point
  let coreDirection := globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
    configuration data analysis realization plusBase minusBase
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test)
  let metricProjection :
      RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
        RegularGeneralMetricC2Core period hPeriod plusBase :=
    (ContinuousLinearMap.fst Real _ _).comp
      ((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _))
  let gaugeProjection :
      RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
        GaugeC2Core period hPeriod :=
    (ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.snd Real _ _)
  have hMetricPoint : corePoint.1.1.1 =
      regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (point.1.completeVariation.fullMetricPerturbation .plus) := rfl
  have hMetricDirection : coreDirection.1.1.1 =
      regularGeneralMetricC2SmoothDirection period hPeriod plusBase (test .plus) := rfl
  have hPacket : smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      configuration.physical.coefficientFields.gauge.1 + corePoint.2.1 =
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (configuration.physical.coefficientFields.gauge.1 +
          point.1.completeVariation.independent.gauge.1) := by
    change smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        configuration.physical.coefficientFields.gauge.1 +
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        point.1.completeVariation.independent.gauge.1 = _
    exact ((smoothGaugeCoefficientC2CoreLinearMap period hPeriod).map_add _ _).symm
  have hGauge : gaugeProjection coreDirection = 0 := by
    change smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      ((regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
        period hPeriod configuration.physical test).1.completeVariation.independent.gauge.1) = 0
    rw [regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_independent]
    exact map_zero _
  have hJoint := mobileMaxwellJointAction_differentiableAt period hPeriod plusBase measure
    (metricProjection corePoint)
    (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      configuration.physical.coefficientFields.gauge.1 + gaugeProjection corePoint)
    hPoint.plus_mem
  have hNative := fderiv_scaled_projected_eq_metricSlice
    (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod plusBase measure)
    (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      configuration.physical.coefficientFields.gauge.1)
    couplings.plusMaxwellScale metricProjection gaugeProjection
    corePoint coreDirection hJoint hGauge
  change fderiv Real (fun core => couplings.plusMaxwellScale *
    regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
      period hPeriod configuration.physical plusBase minusBase measure core)
    corePoint coreDirection = _
  simpa only [regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction,
    regularGeneralMetricC2PairedPlusGaugeCoefficientInput,
    metricProjection, gaugeProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    hMetricPoint, hMetricDirection, hPacket] using hNative

/-- Native mobile minus Maxwell derivative with its translated gauge packet. -/
theorem pairedStrongMaxwellMinusDerivative_eq_native_fderiv
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hPoint : point ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      couplings.minusMaxwellScale * fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod minusBase measure variation
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            (configuration.physical.coefficientFields.gauge.2 +
              point.1.completeVariation.independent.gauge.2)))
        (regularGeneralMetricSmoothC2Variation period hPeriod minusBase
          (point.1.completeVariation.fullMetricPerturbation .minus))
        (regularGeneralMetricC2SmoothDirection period hPeriod minusBase (test .minus)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let corePoint := globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
    configuration data analysis realization plusBase minusBase point
  let coreDirection := globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
    configuration data analysis realization plusBase minusBase
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test)
  let metricProjection :
      RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
        RegularGeneralMetricC2Core period hPeriod minusBase :=
    (ContinuousLinearMap.snd Real _ _).comp
      ((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _))
  let gaugeProjection :
      RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
        GaugeC2Core period hPeriod :=
    (ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.snd Real _ _)
  have hMetricPoint : corePoint.1.1.2 =
      regularGeneralMetricSmoothC2Variation period hPeriod minusBase
        (point.1.completeVariation.fullMetricPerturbation .minus) := rfl
  have hMetricDirection : coreDirection.1.1.2 =
      regularGeneralMetricC2SmoothDirection period hPeriod minusBase (test .minus) := rfl
  have hPacket : smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      configuration.physical.coefficientFields.gauge.2 + corePoint.2.2 =
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (configuration.physical.coefficientFields.gauge.2 +
          point.1.completeVariation.independent.gauge.2) := by
    change smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        configuration.physical.coefficientFields.gauge.2 +
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        point.1.completeVariation.independent.gauge.2 = _
    exact ((smoothGaugeCoefficientC2CoreLinearMap period hPeriod).map_add _ _).symm
  have hGauge : gaugeProjection coreDirection = 0 := by
    change smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      ((regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
        period hPeriod configuration.physical test).1.completeVariation.independent.gauge.2) = 0
    rw [regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_independent]
    exact map_zero _
  have hJoint := mobileMaxwellJointAction_differentiableAt period hPeriod minusBase measure
    (metricProjection corePoint)
    (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      configuration.physical.coefficientFields.gauge.2 + gaugeProjection corePoint)
    hPoint.minus_mem
  have hNative := fderiv_scaled_projected_eq_metricSlice
    (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod minusBase measure)
    (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      configuration.physical.coefficientFields.gauge.2)
    couplings.minusMaxwellScale metricProjection gaugeProjection
    corePoint coreDirection hJoint hGauge
  change fderiv Real (fun core => couplings.minusMaxwellScale *
    regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
      period hPeriod configuration.physical plusBase minusBase measure core)
    corePoint coreDirection = _
  simpa only [regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction,
    regularGeneralMetricC2PairedMinusGaugeCoefficientInput,
    metricProjection, gaugeProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    hMetricPoint, hMetricDirection, hPacket] using hNative

end Paired
end
end P0EFTJanusPairedStrongOffCenterActionDerivatives4D
end JanusFormal
