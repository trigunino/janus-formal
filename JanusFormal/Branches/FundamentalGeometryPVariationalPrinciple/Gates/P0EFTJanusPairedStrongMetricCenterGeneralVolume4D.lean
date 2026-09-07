import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricCenterTotalResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStoredVolumePalatiniMetricResidual4D

/-! # Total strong metric residual at the centre for arbitrary stored volumes -/

namespace JanusFormal
namespace P0EFTJanusPairedStrongMetricCenterGeneralVolume4D

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
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFiniteRankFunctionalMaster4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusPairedInteractionMetricCenterSylvester4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusPairedStrongInteractionResidualPairing4D
open P0EFTJanusRegularFrameFixedVolumeRicciResidual4D
open P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusPairedStrongMaxwellResidualPairing4D
open P0EFTJanusPairedStrongMetricCenterTotalResidual4D
open P0EFTJanusStoredVolumePalatiniMetricResidual4D

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

/-- The actual interaction, complete fixed-volume gravity, and Maxwell residuals. -/
def pairedStrongMetricCenterGeneralVolumeResidual
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) :
    SmoothGeneralMetricTensorPair period hPeriod :=
  let hZero := pairedStrongInteraction_zero_mem_lorentzMatrixDomain period hPeriod
    configuration plusBase minusBase hBase
  let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
  smoothGeneralMetricTensorPairAdd period hPeriod
    (smoothGeneralMetricTensorPairAdd period hPeriod
      (pairedInteractionSmoothMetricResidualPair period hPeriod plusBase minusBase hRoot
        couplings.interactionScale couplings.interactionCoefficients)
      (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod plusBase couplings.plusEinstein.gravitationalCoupling,
        regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod minusBase couplings.minusEinstein.gravitationalCoupling))
    (pairedStrongMaxwellMetricResidualPair period hPeriod configuration.physical couplings plusBase minusBase)

private theorem assembleFiveBlocks {interaction gravityPlus gravityMinus maxwellPlus maxwellMinus
    interactionPairing gravityPairing maxwellPairing : Real}
    (hInteraction : interaction = interactionPairing)
    (hGravity : gravityPlus + gravityMinus = gravityPairing)
    (hMaxwell : maxwellPlus + maxwellMinus = maxwellPairing) :
    (((interaction + gravityPlus) + gravityMinus) + maxwellPlus) + maxwellMinus =
      (interactionPairing + gravityPairing) + maxwellPairing := by
  linarith only [hInteraction, hGravity, hMaxwell]

section Strong
variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical
    couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
    period hPeriod couplings.matterMassSquared)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

/-- Both actual strong gravity blocks retain their complete stored-volume Palatini residual. -/
theorem pairedStrongEinsteinHilbertDerivatives_zero_eq_ungaugedMetricResidualPairing
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
      period hPeriod configuration.physical test
    regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure 0 direction +
      regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase minusBase measure 0 direction =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric)
        (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod plusBase couplings.plusEinstein.gravitationalCoupling,
          regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod minusBase couplings.minusEinstein.gravitationalCoupling)
        test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  dsimp only
  rw [pairedStrongEinsteinHilbertPlusDerivative_zero_eq_fixedVolume,
    pairedStrongEinsteinHilbertMinusDerivative_zero_eq_fixedVolume]
  rw [regularFrameFixedVolumeEinsteinHilbertDerivative_eq_ungaugedResidualIntegral
      period hPeriod plusBase couplings.plusEinstein (test .plus),
    regularFrameFixedVolumeEinsteinHilbertDerivative_eq_ungaugedResidualIntegral
      period hPeriod minusBase couplings.minusEinstein (test .minus)]
  have hPlus := (generalMetricTensorPairingAt_continuous period hPeriod plusBase.metric
    (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod plusBase
      couplings.plusEinstein.gravitationalCoupling) (test .plus)
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  have hMinus := (generalMetricTensorPairingAt_continuous period hPeriod minusBase.metric
    (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod minusBase
      couplings.minusEinstein.gravitationalCoupling) (test .minus)
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  unfold regularGeneralMetricC2PairedMetricResidualPairing
    canonicalGeneralMetricTensorPairPairing generalMetricTensorPairPairingAt
    globalMinimalPhysicalMetricTestPair
  exact (integral_add hPlus hMinus).symm

attribute [local irreducible]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.regularGeneralMetricC2PairedInteractionC2ActionDerivative
  P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D.regularGeneralMetricC2PairedRelativeRootDerivative
  P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D.regularGeneralMetricC2PairedLorentzMatrixDomain

/-- At the centre all five active metric blocks equal one concrete smooth residual pairing. -/
theorem pairedStrongMetricEuler_zero_eq_generalVolumeResidualPairing
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period hPeriod
        configuration data analysis realization plusBase minusBase hBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) 0
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric)
        (pairedStrongMetricCenterGeneralVolumeResidual period hPeriod configuration couplings
          plusBase minusBase hBase) test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  have hPoint := zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
    period hPeriod configuration.physical plusBase minusBase hBase
  have hBlocks :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongMetric_eq_allActionDerivatives
      period hPeriod configuration data analysis realization plusBase minusBase hBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) 0 hPoint test
  have hInteraction := pairedStrongInteractionActionDerivative_zero_eq_metricResidualPairing
    period hPeriod plusBase minusBase configuration data analysis realization hBase test
  have hGravity := pairedStrongEinsteinHilbertDerivatives_zero_eq_ungaugedMetricResidualPairing
    period hPeriod configuration data analysis realization plusBase minusBase test
  have hMaxwell := pairedStrongMaxwellDerivatives_zero_eq_metricResidualPairing
    period hPeriod configuration data analysis realization plusBase minusBase test
  have hSum := assembleFiveBlocks hInteraction hGravity hMaxwell
  calc
    _ = _ := hBlocks
    _ = _ := hSum
    _ = _ := by
      unfold pairedStrongMetricCenterGeneralVolumeResidual
      rw [pairedMetricResidualPairing_add, pairedMetricResidualPairing_add]

/-- Pure metric stationarity at the centre is equivalent to the two actual tensor equations. -/
theorem pairedStrongMetricEuler_zero_iff_generalVolumeResidual_components
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    (∀ test : GlobalMinimalPhysicalMetricTest period hPeriod,
      regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period hPeriod
        configuration data analysis realization plusBase minusBase hBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) 0
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
          period hPeriod configuration.physical test) = 0) ↔
      (pairedStrongMetricCenterGeneralVolumeResidual period hPeriod configuration couplings
        plusBase minusBase hBase).1 = 0 ∧
      (pairedStrongMetricCenterGeneralVolumeResidual period hPeriod configuration couplings
        plusBase minusBase hBase).2 = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  simp_rw [pairedStrongMetricEuler_zero_eq_generalVolumeResidualPairing period hPeriod
    configuration data analysis realization plusBase minusBase hBase]
  exact regularGeneralMetricC2PairedMetricResidualPairing_zero_iff_components period hPeriod
    (plusBase.metric, minusBase.metric)
    (pairedStrongMetricCenterGeneralVolumeResidual period hPeriod configuration couplings plusBase minusBase hBase)

end Strong
end
end P0EFTJanusPairedStrongMetricCenterGeneralVolume4D
end JanusFormal
