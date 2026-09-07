import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMaxwellCenterFirstVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D

/-! # Both weighted strong Maxwell metric residuals at the centre -/

namespace JanusFormal
namespace P0EFTJanusPairedStrongMaxwellResidualPairing4D

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

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusPairedStrongMaxwellCenterFirstVariation4D
open P0EFTJanusStrongMaxwellMetricResidual4D

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

local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

def pairedStrongMaxwellMetricResidualPair
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    SmoothGeneralMetricTensorPair period hPeriod :=
  (smoothSymmetricTensorSMul period hPeriod couplings.plusMaxwellScale
    (strongMaxwellMetricResidual period hPeriod plusBase
      (regularFrameGaugePotentialFromCoefficients period hPeriod plusBase
        configuration.coefficientFields.gauge.1)),
   smoothSymmetricTensorSMul period hPeriod couplings.minusMaxwellScale
    (strongMaxwellMetricResidual period hPeriod minusBase
      (regularFrameGaugePotentialFromCoefficients period hPeriod minusBase
        configuration.coefficientFields.gauge.2)))

theorem pairedWeightedMetricResidualIntegral_eq_pairing
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusResidual minusResidual : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (plusScale minusScale : Real)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    plusScale * (∫ point, generalMetricTensorPairingAt period hPeriod plusBase.metric
      plusResidual (test .plus) point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
    minusScale * (∫ point, generalMetricTensorPairingAt period hPeriod minusBase.metric
      minusResidual (test .minus) point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
    regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
      (plusBase.metric, minusBase.metric)
      (smoothSymmetricTensorSMul period hPeriod plusScale plusResidual,
        smoothSymmetricTensorSMul period hPeriod minusScale minusResidual) test := by
  have hPlus := ((generalMetricTensorPairingAt_continuous period hPeriod plusBase.metric
    plusResidual (test .plus)).const_mul plusScale).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  have hMinus := ((generalMetricTensorPairingAt_continuous period hPeriod minusBase.metric
    minusResidual (test .minus)).const_mul minusScale).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  unfold regularGeneralMetricC2PairedMetricResidualPairing
    canonicalGeneralMetricTensorPairPairing generalMetricTensorPairPairingAt
    globalMinimalPhysicalMetricTestPair
  simp_rw [generalMetricTensorPairingAt_smul_left]
  rw [← integral_const_mul, ← integral_const_mul]
  exact (integral_add hPlus hMinus).symm

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

theorem pairedStrongMaxwellDerivatives_zero_eq_metricResidualPairing
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test
    regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
      period hPeriod configuration data analysis realization plusBase minusBase measure 0 direction +
    regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
      period hPeriod configuration data analysis realization plusBase minusBase measure 0 direction =
    regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
      (plusBase.metric, minusBase.metric)
      (pairedStrongMaxwellMetricResidualPair period hPeriod configuration.physical couplings
        plusBase minusBase) test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  dsimp only
  rw [pairedStrongMaxwellPlusDerivative_zero_eq_nativeFirstVariation,
    pairedStrongMaxwellMinusDerivative_zero_eq_nativeFirstVariation,
    nativeMaxwellMetricCenterFirstVariation_eq_fderiv,
    nativeMaxwellMetricCenterFirstVariation_eq_fderiv,
    strongMaxwellMetricCenterFirstVariation_eq_residualIntegral,
    strongMaxwellMetricCenterFirstVariation_eq_residualIntegral]
  exact pairedWeightedMetricResidualIntegral_eq_pairing period hPeriod plusBase minusBase
    _ _ couplings.plusMaxwellScale couplings.minusMaxwellScale test

end Paired
end
end P0EFTJanusPairedStrongMaxwellResidualPairing4D
end JanusFormal
