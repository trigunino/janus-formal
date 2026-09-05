import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

/-! # Invariant Einstein pairings in the paired strong metric equation

At the chart centre, each historical fixed-volume gravity derivative is its
invariant Einstein pairing minus the exact volume correction. Canonical
volume gauge is required only at the two base metrics.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

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
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The invariant Einstein tensor contribution to a smooth metric variation. -/
def regularFrameEinsteinHilbertInvariantBulk
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Real :=
  ∫ point, -(1 / (2 * couplings.gravitationalCoupling)) *
    generalMetricTensorPairingAt period hPeriod metric.metric
      (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
        couplings.cosmologicalConstant) tensor point
    ∂(generalLorentzVolumeMeasure period hPeriod metric.metric)

/-- The volume term retained by the fixed-volume paired action. -/
def regularFrameEinsteinHilbertVolumeCorrection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Real :=
  ∫ point,
    (((1 / (2 * couplings.gravitationalCoupling)) •
      (regularGeneralMetricC0ScalarCurvature period hPeriod metric 0 -
        regularGeneralMetricC0Constant period hPeriod
          (2 * couplings.cosmologicalConstant))) •
      regularGeneralMetricC0VolumeDerivativeAtZero period hPeriod metric
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)) point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Fixed volume gives the Einstein pairing minus its exact density variation;
no gauge condition along the variation is assumed. -/
theorem regularFrameFixedVolumeEinsteinHilbertDerivative_invariantBulk_sub_volumeCorrection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        couplings (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      regularFrameEinsteinHilbertInvariantBulk period hPeriod metric couplings tensor -
        regularFrameEinsteinHilbertVolumeCorrection period hPeriod metric couplings tensor := by
  apply eq_sub_iff_add_eq.mpr
  unfold regularFrameEinsteinHilbertInvariantBulk
  rw [← regularFrameEinsteinHilbertDerivative_invariantBulk_of_canonicalVolumeGauge
    period hPeriod metric couplings tensor hGauge,
    regularGeneralMetricC0EinsteinHilbertActionDerivative_fixedVolume_discrepancy]
  apply congrArg (fun correction : Real =>
    regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
      period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      couplings (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) + correction)
  unfold regularFrameEinsteinHilbertVolumeCorrection
  apply integral_congr_ae
  filter_upwards [] with point
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    ContinuousMap.mul_apply, smul_eq_mul]

private theorem pairedPlusFixedVolumeEinsteinHilbert_fderiv_zero
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (direction : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase) :
    fderiv Real (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
        period hPeriod plusBase minusBase measure couplings) 0 direction =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod plusBase measure couplings direction.1.1 := by
  let projection :
      RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase →L[Real]
        RegularGeneralMetricC2Core period hPeriod plusBase :=
    (ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _)
  have hDerivative : HasFDerivAt
      (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction
        period hPeriod plusBase minusBase measure couplings)
      ((regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod plusBase measure couplings).comp projection) 0 :=
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_hasFDerivAt_zero
      period hPeriod plusBase measure couplings).comp 0 projection.hasFDerivAt
  exact congrArg (fun derivative => derivative direction) hDerivative.fderiv

private theorem pairedMinusFixedVolumeEinsteinHilbert_fderiv_zero
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (couplings : EinsteinHilbertCouplings)
    (direction : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase) :
    fderiv Real (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
        period hPeriod plusBase minusBase measure couplings) 0 direction =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod minusBase measure couplings direction.1.2 := by
  let projection :
      RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase →L[Real]
        RegularGeneralMetricC2Core period hPeriod minusBase :=
    (ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.fst Real _ _)
  have hDerivative : HasFDerivAt
      (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction
        period hPeriod plusBase minusBase measure couplings)
      ((regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod minusBase measure couplings).comp projection) 0 :=
    (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_hasFDerivAt_zero
      period hPeriod minusBase measure couplings).comp 0 projection.hasFDerivAt
  exact congrArg (fun derivative => derivative direction) hDerivative.fderiv

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

/-- The plus strong gravity block at the centre is its native fixed-volume derivative. -/
theorem pairedStrongEinsteinHilbertPlusDerivative_zero_eq_fixedVolume
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure 0
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod plusBase measure couplings.plusEinstein
        (regularGeneralMetricC2SmoothDirection period hPeriod plusBase (test .plus)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hProjection :
      (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test)).1.1 =
        regularGeneralMetricC2SmoothDirection period hPeriod plusBase (test .plus) := rfl
  simpa only [regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative,
    ContinuousLinearMap.comp_apply, map_zero, hProjection] using
    pairedPlusFixedVolumeEinsteinHilbert_fderiv_zero period hPeriod plusBase minusBase
      measure couplings.plusEinstein
      (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test))

/-- The minus strong gravity block at the centre is its native fixed-volume derivative. -/
theorem pairedStrongEinsteinHilbertMinusDerivative_zero_eq_fixedVolume
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure 0
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod minusBase measure couplings.minusEinstein
        (regularGeneralMetricC2SmoothDirection period hPeriod minusBase (test .minus)) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hProjection :
      (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test)).1.2 =
        regularGeneralMetricC2SmoothDirection period hPeriod minusBase (test .minus) := rfl
  simpa only [regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative,
    ContinuousLinearMap.comp_apply, map_zero, hProjection] using
    pairedMinusFixedVolumeEinsteinHilbert_fderiv_zero period hPeriod plusBase minusBase
      measure couplings.minusEinstein
      (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test))

/-- The total metric equation at the chart centre contains both invariant
Einstein pairings with their exact fixed-volume corrections. The interaction
and Maxwell derivatives are the original terms of the strong action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongMetric_eq_invariantEinsteinWithVolumeCorrection
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (hPlusGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod plusBase)
    (hMinusGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
    let hPoint := zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase hBase
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure 0 direction =
      ((((regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative
              period hPeriod configuration data analysis realization plusBase minusBase
              measure 0 hPoint direction +
            (regularFrameEinsteinHilbertInvariantBulk period hPeriod plusBase
                couplings.plusEinstein (test .plus) -
              regularFrameEinsteinHilbertVolumeCorrection period hPeriod plusBase
                couplings.plusEinstein (test .plus))) +
          (regularFrameEinsteinHilbertInvariantBulk period hPeriod minusBase
              couplings.minusEinstein (test .minus) -
            regularFrameEinsteinHilbertVolumeCorrection period hPeriod minusBase
              couplings.minusEinstein (test .minus))) +
        regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
          period hPeriod configuration data analysis realization plusBase minusBase
          measure 0 direction) +
      regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase
        measure 0 direction) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  dsimp only
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongMetric_eq_allActionDerivatives
    period hPeriod configuration data analysis realization plusBase minusBase hBase
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) 0
    (zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase hBase) test]
  rw [pairedStrongEinsteinHilbertPlusDerivative_zero_eq_fixedVolume,
    pairedStrongEinsteinHilbertMinusDerivative_zero_eq_fixedVolume,
    regularFrameFixedVolumeEinsteinHilbertDerivative_invariantBulk_sub_volumeCorrection
      period hPeriod plusBase couplings.plusEinstein (test .plus) hPlusGauge,
    regularFrameFixedVolumeEinsteinHilbertDerivative_invariantBulk_sub_volumeCorrection
      period hPeriod minusBase couplings.minusEinstein (test .minus) hMinusGauge]

end Paired
end
end P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
end JanusFormal
