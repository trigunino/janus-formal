import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongInteractionResidualPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameFixedVolumeRicciResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricInvariantEinsteinVolumeCorrection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMaxwellResidualPairing4D

/-! # Smooth total metric residual of the authentic strong operator at the centre -/

namespace JanusFormal
namespace P0EFTJanusPairedStrongMetricCenterTotalResidual4D

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

/-- Additivity in the smooth residual uses the canonical integrated pairing. -/
theorem pairedMetricResidualPairing_add
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothGeneralMetricTensorPair period hPeriod)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    regularGeneralMetricC2PairedMetricResidualPairing period hPeriod metrics
        (smoothGeneralMetricTensorPairAdd period hPeriod first second) test =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod metrics first test +
        regularGeneralMetricC2PairedMetricResidualPairing period hPeriod metrics second test :=
  canonicalGeneralMetricTensorPairPairing_add_left period hPeriod metrics first second
    (globalMinimalPhysicalMetricTestPair period hPeriod test)

/-- The actual interaction, Ricci, and complete Maxwell residuals in both sectors. -/
def pairedStrongMetricCenterTotalResidual
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
      (regularFrameFixedVolumeRicciResidual period hPeriod plusBase couplings.plusEinstein.gravitationalCoupling,
        regularFrameFixedVolumeRicciResidual period hPeriod minusBase couplings.minusEinstein.gravitationalCoupling))
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

/-- The two actual strong gravity blocks are the weighted fixed-volume Ricci pair. -/
theorem pairedStrongEinsteinHilbertDerivatives_zero_eq_metricResidualPairing
    (hPlusGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod plusBase)
    (hMinusGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod minusBase)
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
        (regularFrameFixedVolumeRicciResidual period hPeriod plusBase couplings.plusEinstein.gravitationalCoupling,
          regularFrameFixedVolumeRicciResidual period hPeriod minusBase couplings.minusEinstein.gravitationalCoupling)
        test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  dsimp only
  rw [pairedStrongEinsteinHilbertPlusDerivative_zero_eq_fixedVolume,
    pairedStrongEinsteinHilbertMinusDerivative_zero_eq_fixedVolume]
  exact regularFrameFixedVolumeEinsteinHilbertDerivatives_eq_pairedResidualPairing
    period hPeriod plusBase minusBase couplings.plusEinstein couplings.minusEinstein test
    hPlusGauge hMinusGauge

attribute [local irreducible]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.regularGeneralMetricC2PairedInteractionC2ActionDerivative
  P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D.regularGeneralMetricC2PairedRelativeRootDerivative
  P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D.regularGeneralMetricC2PairedLorentzMatrixDomain

/-- At the centre all five active metric blocks equal one concrete smooth residual pairing. -/
theorem pairedStrongMetricEuler_zero_eq_totalResidualPairing
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (hPlusGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod plusBase)
    (hMinusGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod minusBase)
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
        (pairedStrongMetricCenterTotalResidual period hPeriod configuration couplings
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
  have hGravity := pairedStrongEinsteinHilbertDerivatives_zero_eq_metricResidualPairing
    period hPeriod configuration data analysis realization plusBase minusBase hPlusGauge hMinusGauge test
  have hMaxwell := pairedStrongMaxwellDerivatives_zero_eq_metricResidualPairing
    period hPeriod configuration data analysis realization plusBase minusBase test
  have hSum := assembleFiveBlocks hInteraction hGravity hMaxwell
  calc
    _ = _ := hBlocks
    _ = _ := hSum
    _ = _ := by
      unfold pairedStrongMetricCenterTotalResidual
      rw [pairedMetricResidualPairing_add, pairedMetricResidualPairing_add]

/-- Pure metric stationarity at the centre is equivalent to the two actual tensor equations. -/
theorem pairedStrongMetricEuler_zero_iff_totalResidual_components
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (hPlusGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod plusBase)
    (hMinusGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod minusBase) :
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
      (pairedStrongMetricCenterTotalResidual period hPeriod configuration couplings
        plusBase minusBase hBase).1 = 0 ∧
      (pairedStrongMetricCenterTotalResidual period hPeriod configuration couplings
        plusBase minusBase hBase).2 = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  simp_rw [pairedStrongMetricEuler_zero_eq_totalResidualPairing period hPeriod
    configuration data analysis realization plusBase minusBase hBase hPlusGauge hMinusGauge]
  exact regularGeneralMetricC2PairedMetricResidualPairing_zero_iff_components period hPeriod
    (plusBase.metric, minusBase.metric)
    (pairedStrongMetricCenterTotalResidual period hPeriod configuration couplings plusBase minusBase hBase)

end Strong
end
end P0EFTJanusPairedStrongMetricCenterTotalResidual4D
end JanusFormal
