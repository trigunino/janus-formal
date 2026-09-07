import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAffineTarget4D

/-! # Paired strong Maxwell metric variations at the chart centre

Both strong derivatives retain their coupling, fixed-volume stress correction,
and induced gauge derivative. No stationarity or nonzero coupling is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongMaxwellCenterFirstVariation4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
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
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAffineTarget4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D

private theorem fderiv_scaled_projected_eq_metricSlice
    {E M G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup M] [NormedSpace Real M]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (action : M → G → Real) (coefficients : G) (scale : Real)
    (metricProjection : E →L[Real] M) (gaugeProjection : E →L[Real] G)
    (hJoint : DifferentiableAt Real
      (fun input : M × G => action input.1 input.2) (0, coefficients))
    (direction : E) (hGauge : gaugeProjection direction = 0) :
    fderiv Real (fun point => scale *
        action (metricProjection point) (coefficients + gaugeProjection point)) 0 direction =
      scale * fderiv Real (fun metric => action metric coefficients) 0
        (metricProjection direction) := by
  let derivative := fderiv Real
    (fun input : M × G => action input.1 input.2) (0, coefficients)
  have hInput : HasFDerivAt
      (fun point => (metricProjection point, coefficients + gaugeProjection point))
      (metricProjection.prod gaugeProjection) 0 := by
    simpa only [Pi.add_apply, zero_add] using metricProjection.hasFDerivAt.prodMk
      ((hasFDerivAt_const (x := (0 : E)) (c := coefficients)).add
        gaugeProjection.hasFDerivAt)
  have hAtInput : HasFDerivAt (fun input : M × G => action input.1 input.2)
      derivative (metricProjection 0, coefficients + gaugeProjection 0) := by
    simpa only [map_zero, add_zero] using hJoint.hasFDerivAt
  have hScaled : HasFDerivAt (fun point => scale *
      action (metricProjection point) (coefficients + gaugeProjection point))
      (scale • derivative.comp (metricProjection.prod gaugeProjection)) 0 := by
    simpa only [Function.comp_def] using (hAtInput.comp 0 hInput).const_mul scale
  have hMetric : HasFDerivAt (fun metric => action metric coefficients)
      (derivative.comp (ContinuousLinearMap.inl Real M G)) 0 := by
    simpa only [Function.comp_def] using hJoint.hasFDerivAt.comp (0 : M)
      (hasFDerivAt_prodMk_left (𝕜 := Real) (0 : M) coefficients)
  rw [hScaled.fderiv, hMetric.fderiv]
  change scale * derivative (metricProjection direction, gaugeProjection direction) =
    scale * derivative (metricProjection direction, 0)
  rw [hGauge]

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

private theorem mobileMaxwellAction_differentiableAt_center
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (coefficients : GaugeC2Core period hPeriod) :
    DifferentiableAt Real
      (fun input : RegularGeneralMetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
        regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure input.1 input.2) (0, coefficients) := by
  have hOpen : IsOpen
      (regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain period hPeriod metric) :=
    (regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod metric).prod isOpen_univ
  have hCenter : (0, coefficients) ∈
      regularGeneralMetricC2MobileGaugeCoefficientMaxwellDomain period hPeriod metric :=
    ⟨zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod metric, Set.mem_univ _⟩
  exact ((regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_contDiffOn_two
    period hPeriod metric measure).contDiffAt (hOpen.mem_nhds hCenter)).differentiableAt
      (by norm_num)

private theorem pairedPlusScaledMaxwell_fderiv_zero_of_gauge_zero
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (scale : Real)
    (direction : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase)
    (hGauge : direction.2.1 = 0) :
    fderiv Real (fun core => scale * regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction
        period hPeriod configuration plusBase minusBase measure core) 0 direction =
      scale * fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod plusBase measure variation
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod configuration.coefficientFields.gauge.1))
        0 direction.1.1.1 := by
  let metricProjection :
      RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
        RegularGeneralMetricC2Core period hPeriod plusBase :=
    (ContinuousLinearMap.fst Real _ _).comp
      ((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _))
  let gaugeProjection :
      RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
        GaugeC2Core period hPeriod :=
    (ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.snd Real _ _)
  have h := fderiv_scaled_projected_eq_metricSlice
    (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod plusBase measure)
    (smoothGaugeCoefficientC2CoreLinearMap period hPeriod configuration.coefficientFields.gauge.1)
    scale metricProjection gaugeProjection
    (mobileMaxwellAction_differentiableAt_center period hPeriod plusBase measure _)
    direction hGauge
  simpa only [regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction,
    regularGeneralMetricC2PairedPlusGaugeCoefficientInput,
    metricProjection, gaugeProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using h

private theorem pairedMinusScaledMaxwell_fderiv_zero_of_gauge_zero
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (scale : Real)
    (direction : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase)
    (hGauge : direction.2.2 = 0) :
    fderiv Real (fun core => scale * regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction
        period hPeriod configuration plusBase minusBase measure core) 0 direction =
      scale * fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod minusBase measure variation
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod configuration.coefficientFields.gauge.2))
        0 direction.1.1.2 := by
  let metricProjection :
      RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
        RegularGeneralMetricC2Core period hPeriod minusBase :=
    (ContinuousLinearMap.snd Real _ _).comp
      ((ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _))
  let gaugeProjection :
      RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase →L[Real]
        GaugeC2Core period hPeriod :=
    (ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.snd Real _ _)
  have h := fderiv_scaled_projected_eq_metricSlice
    (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod minusBase measure)
    (smoothGaugeCoefficientC2CoreLinearMap period hPeriod configuration.coefficientFields.gauge.2)
    scale metricProjection gaugeProjection
    (mobileMaxwellAction_differentiableAt_center period hPeriod minusBase measure _)
    direction hGauge
  simpa only [regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction,
    regularGeneralMetricC2PairedMinusGaugeCoefficientInput,
    metricProjection, gaugeProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using h

/-- The complete native expression proved in Gate587, including the induced gauge term. -/
def nativeMaxwellMetricCenterFirstVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Real :=
  let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
    (gaugePotentialFrameCoefficients period hPeriod metric potential)
  let direction := regularGeneralMetricC2SmoothDirection period hPeriod metric tensor
  (∫ point, metric.volume point / 2 *
    generalMetricTensorPairingAt period hPeriod metric.metric
      (regularGeneralMetricMaxwellStressTensor period hPeriod metric potential) tensor point ∂measure) +
    regularGeneralMetricC2FixedVolumeMaxwellCorrection period hPeriod metric measure potential direction +
    fderiv Real (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod metric measure 0) coefficients
      ((1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod
        (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric direction) coefficients)

theorem nativeMaxwellMetricCenterFirstVariation_eq_fderiv
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    nativeMaxwellMetricCenterFirstVariation period hPeriod metric measure potential tensor =
      fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric measure variation
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            (gaugePotentialFrameCoefficients period hPeriod metric potential))) 0
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) := by
  symm
  simpa only [nativeMaxwellMetricCenterFirstVariation] using
    strongMaxwellMetricCenterFirstVariation_eq_stress_add_volume_add_inducedGauge
      period hPeriod metric measure potential tensor

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

/-- The plus strong Maxwell metric derivative is its scaled complete native variation. -/
theorem pairedStrongMaxwellPlusDerivative_zero_eq_nativeFirstVariation
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure 0
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      couplings.plusMaxwellScale * nativeMaxwellMetricCenterFirstVariation
        period hPeriod plusBase measure
        (regularFrameGaugePotentialFromCoefficients period hPeriod plusBase
          configuration.physical.coefficientFields.gauge.1) (test .plus) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let projected := globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
    period hPeriod configuration data analysis realization plusBase minusBase
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test)
  have hMetric : projected.1.1.1 =
      regularGeneralMetricC2SmoothDirection period hPeriod plusBase (test .plus) := rfl
  have hGauge : projected.2.1 = 0 := by
    change smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      ((regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
        period hPeriod configuration.physical test).1.completeVariation.independent.gauge.1) = 0
    rw [regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_independent]
    exact map_zero _
  have hNative := pairedPlusScaledMaxwell_fderiv_zero_of_gauge_zero period hPeriod
    configuration.physical plusBase minusBase measure couplings.plusMaxwellScale projected hGauge
  have hStrong :
      regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure 0
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      couplings.plusMaxwellScale * fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod plusBase measure variation
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            configuration.physical.coefficientFields.gauge.1)) 0
        (regularGeneralMetricC2SmoothDirection period hPeriod plusBase (test .plus)) := by
    simpa only [regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative,
      ContinuousLinearMap.comp_apply, map_zero, hMetric] using hNative
  rw [hStrong]
  apply congrArg (fun value : Real => couplings.plusMaxwellScale * value)
  simpa only [nativeMaxwellMetricCenterFirstVariation, gaugePotentialFrameCoefficients_reconstructed]
    using strongMaxwellMetricCenterFirstVariation_eq_stress_add_volume_add_inducedGauge
      period hPeriod plusBase measure
      (regularFrameGaugePotentialFromCoefficients period hPeriod plusBase
        configuration.physical.coefficientFields.gauge.1) (test .plus)

/-- The minus strong Maxwell metric derivative is its scaled complete native variation. -/
theorem pairedStrongMaxwellMinusDerivative_zero_eq_nativeFirstVariation
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure 0
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      couplings.minusMaxwellScale * nativeMaxwellMetricCenterFirstVariation
        period hPeriod minusBase measure
        (regularFrameGaugePotentialFromCoefficients period hPeriod minusBase
          configuration.physical.coefficientFields.gauge.2) (test .minus) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let projected := globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
    period hPeriod configuration data analysis realization plusBase minusBase
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test)
  have hMetric : projected.1.1.2 =
      regularGeneralMetricC2SmoothDirection period hPeriod minusBase (test .minus) := rfl
  have hGauge : projected.2.2 = 0 := by
    change smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      ((regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
        period hPeriod configuration.physical test).1.completeVariation.independent.gauge.2) = 0
    rw [regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_independent]
    exact map_zero _
  have hNative := pairedMinusScaledMaxwell_fderiv_zero_of_gauge_zero period hPeriod
    configuration.physical plusBase minusBase measure couplings.minusMaxwellScale projected hGauge
  have hStrong :
      regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure 0
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      couplings.minusMaxwellScale * fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod minusBase measure variation
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            configuration.physical.coefficientFields.gauge.2)) 0
        (regularGeneralMetricC2SmoothDirection period hPeriod minusBase (test .minus)) := by
    simpa only [regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative,
      ContinuousLinearMap.comp_apply, map_zero, hMetric] using hNative
  rw [hStrong]
  apply congrArg (fun value : Real => couplings.minusMaxwellScale * value)
  simpa only [nativeMaxwellMetricCenterFirstVariation, gaugePotentialFrameCoefficients_reconstructed]
    using strongMaxwellMetricCenterFirstVariation_eq_stress_add_volume_add_inducedGauge
      period hPeriod minusBase measure
      (regularFrameGaugePotentialFromCoefficients period hPeriod minusBase
        configuration.physical.coefficientFields.gauge.2) (test .minus)

end Paired
end
end P0EFTJanusPairedStrongMaxwellCenterFirstVariation4D
end JanusFormal
