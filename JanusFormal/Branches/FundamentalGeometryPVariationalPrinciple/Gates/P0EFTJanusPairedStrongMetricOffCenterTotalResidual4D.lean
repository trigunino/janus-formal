import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricCenterGeneralVolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedInteractionOffCenterResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedVolumeEinsteinHilbertDerivativeRecenter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMobileMaxwellOffCenterMetricResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongOffCenterActionDerivatives4D

/-! # Concrete total metric equations at every admissible physical point

All five actual strong metric derivatives are represented at the reconstructed
metrics: interaction, both complete stored-volume gravity terms, and both
weighted Maxwell terms including their recentering gauge contributions.
The remaining physical components are unrestricted. Metric stationarity is
equivalent to vanishing of the two resulting smooth tensors.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongMetricOffCenterTotalResidual4D
set_option autoImplicit false
set_option quotPrecheck false
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
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
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
open P0EFTJanusStoredVolumePalatiniMetricResidual4D
open P0EFTJanusPairedStrongMaxwellResidualPairing4D
open P0EFTJanusPairedStrongMetricCenterTotalResidual4D
open P0EFTJanusPairedInteractionOffCenterResidual4D
open P0EFTJanusFixedVolumeEinsteinHilbertDerivativeRecenter4D
open P0EFTJanusMobileMaxwellOffCenterMetricResidual4D
open P0EFTJanusPairedStrongOffCenterActionDerivatives4D

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

section Residual
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (couplings : GlobalCandidateAActionCouplings)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (physicalPoint : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
  (hPoint : physicalPoint ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
    period hPeriod configuration.physical plusBase minusBase)

local notation "shift" => physicalPoint.1.completeVariation.fullMetricPerturbation
local notation "hShift" => (show RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
  plusBase minusBase (shift .plus) (shift .minus) from hPoint)
local notation "newPlus" => regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase minusBase
  (shift .plus) (shift .minus) hShift
local notation "newMinus" => regularGeneralMetricC2PairedMinusMetric period hPeriod plusBase minusBase
  (shift .plus) (shift .minus) hShift
local notation "plusCoefficients" => configuration.physical.coefficientFields.gauge.1 +
  physicalPoint.1.completeVariation.independent.gauge.1
local notation "minusCoefficients" => configuration.physical.coefficientFields.gauge.2 +
  physicalPoint.1.completeVariation.independent.gauge.2

/-- Both Maxwell tensors include the actual gauge coefficients at the point. -/
def pairedStrongMaxwellOffCenterResidualPair : SmoothGeneralMetricTensorPair period hPeriod :=
  (smoothSymmetricTensorSMul period hPeriod couplings.plusMaxwellScale
    (mobileMaxwellOffCenterMetricResidual period hPeriod plusBase (shift .plus) (hShift).plus_mem plusCoefficients),
   smoothSymmetricTensorSMul period hPeriod couplings.minusMaxwellScale
    (mobileMaxwellOffCenterMetricResidual period hPeriod minusBase (shift .minus) (hShift).minus_mem minusCoefficients))

/-- Explicit total metric residual, requiring only the admissibility of the
physical point and retaining arbitrary stored volumes and all five blocks. -/
def pairedStrongMetricOffCenterResidual : SmoothGeneralMetricTensorPair period hPeriod :=
  smoothGeneralMetricTensorPairAdd period hPeriod
    (smoothGeneralMetricTensorPairAdd period hPeriod
      (pairedInteractionOffCenterResidualPair period hPeriod plusBase minusBase
        (shift .plus) (shift .minus) hShift couplings.interactionScale couplings.interactionCoefficients)
      (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod newPlus couplings.plusEinstein.gravitationalCoupling,
        regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod newMinus couplings.minusEinstein.gravitationalCoupling))
    (pairedStrongMaxwellOffCenterResidualPair period hPeriod configuration couplings
      plusBase minusBase physicalPoint hPoint)
end Residual

private theorem pairedMetricResidualIntegral_eq_pairing
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusResidual minusResidual : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    (∫ point, generalMetricTensorPairingAt period hPeriod plusBase.metric plusResidual
      (test .plus) point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
    (∫ point, generalMetricTensorPairingAt period hPeriod minusBase.metric minusResidual
      (test .minus) point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric) (plusResidual, minusResidual) test := by
  have hPlus := (generalMetricTensorPairingAt_continuous period hPeriod plusBase.metric
    plusResidual (test .plus)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  have hMinus := (generalMetricTensorPairingAt_continuous period hPeriod minusBase.metric
    minusResidual (test .minus)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  unfold regularGeneralMetricC2PairedMetricResidualPairing canonicalGeneralMetricTensorPairPairing
    generalMetricTensorPairPairingAt globalMinimalPhysicalMetricTestPair
  exact (integral_add hPlus hMinus).symm

private theorem assembleFiveBlocks {interaction gravityPlus gravityMinus maxwellPlus maxwellMinus
    interactionPairing gravityPairing maxwellPairing : Real}
    (hInteraction : interaction = interactionPairing)
    (hGravity : gravityPlus + gravityMinus = gravityPairing)
    (hMaxwell : maxwellPlus + maxwellMinus = maxwellPairing) :
    (((interaction + gravityPlus) + gravityMinus) + maxwellPlus) + maxwellMinus =
      (interactionPairing + gravityPairing) + maxwellPairing := by
  linarith only [hInteraction, hGravity, hMaxwell]

attribute [local irreducible]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.regularGeneralMetricC2PairedInteractionC2ActionDerivative
  P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D.regularGeneralMetricC2PairedRelativeRootDerivative
  regularGeneralMetricC2PairedLorentzMatrixDomain

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

section Point
variable (physicalPoint : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
  (hPoint : physicalPoint ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
    period hPeriod configuration.physical plusBase minusBase)
local notation "shift" => physicalPoint.1.completeVariation.fullMetricPerturbation
local notation "hShift" => (show RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
  plusBase minusBase (shift .plus) (shift .minus) from hPoint)
local notation "newPlus" => regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase minusBase
  (shift .plus) (shift .minus) hShift
local notation "newMinus" => regularGeneralMetricC2PairedMinusMetric period hPeriod plusBase minusBase
  (shift .plus) (shift .minus) hShift
local notation "plusCoefficients" => configuration.physical.coefficientFields.gauge.1 +
  physicalPoint.1.completeVariation.independent.gauge.1
local notation "minusCoefficients" => configuration.physical.coefficientFields.gauge.2 +
  physicalPoint.1.completeVariation.independent.gauge.2

/-- Both actual strong gravity blocks include the complete stored-volume residual. -/
theorem pairedStrongEinsteinHilbertDerivatives_offCenter_eq_metricResidualPairing
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod configuration.physical test
    regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative period hPeriod
        configuration data analysis realization plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint direction +
      regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative period hPeriod
        configuration data analysis realization plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint direction =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod ((newPlus).metric, (newMinus).metric)
        (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod newPlus couplings.plusEinstein.gravitationalCoupling,
          regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod newMinus couplings.minusEinstein.gravitationalCoupling) test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  have hPlus := (pairedStrongEinsteinHilbertPlusDerivative_eq_fixedVolume_fderiv period hPeriod
    configuration data analysis realization plusBase minusBase
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint hPoint test).trans
      (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_fderiv_eq_recenteredResidualIntegral
        period hPeriod plusBase (shift .plus) (test .plus) (hShift).plus_mem couplings.plusEinstein)
  have hMinus := (pairedStrongEinsteinHilbertMinusDerivative_eq_fixedVolume_fderiv period hPeriod
    configuration data analysis realization plusBase minusBase
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint hPoint test).trans
      (regularGeneralMetricC0FixedVolumeEinsteinHilbertAction_fderiv_eq_recenteredResidualIntegral
        period hPeriod minusBase (shift .minus) (test .minus) (hShift).minus_mem couplings.minusEinstein)
  exact (congrArg₂ (fun first second : Real => first + second) hPlus hMinus).trans
    (pairedMetricResidualIntegral_eq_pairing period hPeriod newPlus newMinus _ _ test)

/-- Both Maxwell blocks retain their weights and their actual gauge fields at the point. -/
theorem pairedStrongMaxwellDerivatives_offCenter_eq_metricResidualPairing
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod configuration.physical test
    regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative period hPeriod
        configuration data analysis realization plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint direction +
      regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative period hPeriod
        configuration data analysis realization plusBase minusBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint direction =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod ((newPlus).metric, (newMinus).metric)
        (pairedStrongMaxwellOffCenterResidualPair period hPeriod configuration couplings
          plusBase minusBase physicalPoint hPoint) test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  have hPlus := (pairedStrongMaxwellPlusDerivative_eq_native_fderiv period hPeriod
    configuration data analysis realization plusBase minusBase
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint hPoint test).trans
      (congrArg (fun value : Real => couplings.plusMaxwellScale * value)
        (mobileMaxwellAction_fderiv_recenter_eq_metricResidualIntegral period hPeriod
          plusBase (shift .plus) (hShift).plus_mem plusCoefficients (test .plus)))
  have hMinus := (pairedStrongMaxwellMinusDerivative_eq_native_fderiv period hPeriod
    configuration data analysis realization plusBase minusBase
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint hPoint test).trans
      (congrArg (fun value : Real => couplings.minusMaxwellScale * value)
        (mobileMaxwellAction_fderiv_recenter_eq_metricResidualIntegral period hPeriod
          minusBase (shift .minus) (hShift).minus_mem minusCoefficients (test .minus)))
  exact (congrArg₂ (fun first second : Real => first + second) hPlus hMinus).trans
    (pairedWeightedMetricResidualIntegral_eq_pairing period hPeriod newPlus newMinus _ _
      couplings.plusMaxwellScale couplings.minusMaxwellScale test)
end Point

/-- The genuine total strong metric Euler operator is the canonical pairing
of the explicit total residual at every admissible physical point. -/
theorem pairedStrongMetricEuler_offCenter_eq_totalResidualPairing
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible period hPeriod plusBase minusBase)
    (physicalPoint : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hPoint : physicalPoint ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    let shift := physicalPoint.1.completeVariation.fullMetricPerturbation
    let hShift : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase (shift .plus) (shift .minus) := hPoint
    let newPlus := regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase minusBase
      (shift .plus) (shift .minus) hShift
    let newMinus := regularGeneralMetricC2PairedMinusMetric period hPeriod plusBase minusBase
      (shift .plus) (shift .minus) hShift
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period hPeriod
        configuration data analysis realization plusBase minusBase hBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod configuration.physical test) =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod (newPlus.metric, newMinus.metric)
        (pairedStrongMetricOffCenterResidual period hPeriod configuration couplings
          plusBase minusBase physicalPoint hPoint) test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  have hBlocks := regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongMetric_eq_allActionDerivatives
    period hPeriod configuration data analysis realization plusBase minusBase hBase
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint hPoint test
  have hInteraction := pairedStrongInteractionActionDerivative_atPoint_eq_metricResidualPairing
    period hPeriod plusBase minusBase configuration data analysis realization physicalPoint hPoint test
  have hGravity := pairedStrongEinsteinHilbertDerivatives_offCenter_eq_metricResidualPairing
    period hPeriod configuration data analysis realization plusBase minusBase physicalPoint hPoint test
  have hMaxwell := pairedStrongMaxwellDerivatives_offCenter_eq_metricResidualPairing
    period hPeriod configuration data analysis realization plusBase minusBase physicalPoint hPoint test
  have hSum := assembleFiveBlocks hInteraction hGravity hMaxwell
  calc
    _ = _ := hBlocks
    _ = _ := hSum
    _ = _ := by
      unfold pairedStrongMetricOffCenterResidual
      rw [pairedMetricResidualPairing_add, pairedMetricResidualPairing_add]

/-- Metric stationarity at any admissible physical point is exactly the two
concrete tensor equations, with no restriction on its other field components. -/
theorem pairedStrongMetricEuler_offCenter_iff_residual_components
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible period hPeriod plusBase minusBase)
    (physicalPoint : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
    (hPoint : physicalPoint ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
    (∀ test : GlobalMinimalPhysicalMetricTest period hPeriod,
      regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period hPeriod
        configuration data analysis realization plusBase minusBase hBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) physicalPoint
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period hPeriod configuration.physical test) = 0) ↔
      (pairedStrongMetricOffCenterResidual period hPeriod configuration couplings
        plusBase minusBase physicalPoint hPoint).1 = 0 ∧
      (pairedStrongMetricOffCenterResidual period hPeriod configuration couplings
        plusBase minusBase physicalPoint hPoint).2 = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase (canonicalDivergenceFreeLLFrame period hPeriod)
  let shift := physicalPoint.1.completeVariation.fullMetricPerturbation
  have hShift : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
      plusBase minusBase (shift .plus) (shift .minus) := hPoint
  let newPlus := regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase minusBase
    (shift .plus) (shift .minus) hShift
  let newMinus := regularGeneralMetricC2PairedMinusMetric period hPeriod plusBase minusBase
    (shift .plus) (shift .minus) hShift
  apply Iff.trans ?_ (regularGeneralMetricC2PairedMetricResidualPairing_zero_iff_components
    period hPeriod (newPlus.metric, newMinus.metric)
    (pairedStrongMetricOffCenterResidual period hPeriod configuration couplings
      plusBase minusBase physicalPoint hPoint))
  constructor
  · intro hStationary test
    exact (pairedStrongMetricEuler_offCenter_eq_totalResidualPairing period hPeriod
      configuration data analysis realization plusBase minusBase hBase physicalPoint hPoint test).symm.trans
      (hStationary test)
  · intro hResidual test
    exact (pairedStrongMetricEuler_offCenter_eq_totalResidualPairing period hPeriod
      configuration data analysis realization plusBase minusBase hBase physicalPoint hPoint test).trans
      (hResidual test)

end Strong
end
end P0EFTJanusPairedStrongMetricOffCenterTotalResidual4D
end JanusFormal
