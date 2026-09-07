import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMetricOffCenterTotalResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual4D

/-! # Concrete metric tensors in the canonical eight-slot physical PDE system -/

namespace JanusFormal
namespace P0EFTJanusPairedStrongTensorComponentwisePDE4D

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

open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual4D
open P0EFTJanusPairedStrongMetricOffCenterTotalResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical
    couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
    period hPeriod couplings.matterMassSquared)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
    period hPeriod plusBase minusBase)
  (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
  (hPoint : point ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
    period hPeriod configuration.physical plusBase minusBase)

include hPoint in
/-- A genuine smooth tensor pair replaces the metric Riesz representative. -/
def pairedStrongMetricTensorResidualRepresentation :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let shift := point.1.completeVariation.fullMetricPerturbation
  let metrics :=
    ((regularGeneralMetricC2PairedPlusMetric period hPeriod plusBase minusBase
      (shift .plus) (shift .minus) hPoint).metric,
     (regularGeneralMetricC2PairedMinusMetric period hPeriod plusBase minusBase
      (shift .plus) (shift .minus) hPoint).metric)
  let residual := pairedStrongMetricOffCenterResidual period hPeriod configuration
    couplings plusBase minusBase point hPoint
  exact
    { Residual := SmoothGeneralMetricTensorPair period hPeriod
      zeroResidual := 0
      residual := residual
      pairing := regularGeneralMetricC2PairedMetricResidualPairing period hPeriod metrics
      represents := by
        intro test
        change regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
          period hPeriod configuration data analysis realization plusBase minusBase hBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
          (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
            period hPeriod configuration.physical test) = _
        exact pairedStrongMetricEuler_offCenter_eq_totalResidualPairing period hPeriod
          configuration data analysis realization plusBase minusBase hBase point hPoint test
      separates := regularGeneralMetricC2PairedMetricResidualPairing_separates
        period hPeriod metrics residual }

/-- The existing canonical gauge, LL, and SpinC equations retain their exact
representatives; the metric slot now contains the full off-centre tensor pair. -/
def pairedStrongTensorComponentwisePDEDataAt
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point :=
  { regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldSpinCTotalPDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase point hPoint hPlus hMinus with
    metric := pairedStrongMetricTensorResidualRepresentation period hPeriod
      configuration data analysis realization plusBase minusBase hBase point hPoint }

/-- The eight physical slots for the same authentic strong local action.
The normal and diffeomorphism slots here remain the previously proved
projection degeneracies; this is not the nonminimal full-BRST system. -/
def PairedStrongTensorComponentwiseSystemAt
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) : Prop :=
  RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
      (pairedStrongTensorComponentwisePDEDataAt period hPeriod configuration
        data analysis realization plusBase minusBase hBase point hPoint hPlus hMinus)

/-- Authentic strong criticality is exactly the concrete component system
at every admissible physical point, not only at the chart centre. -/
theorem pairedStrongEuler_eq_zero_iff_tensorComponentwiseSystem
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point = 0 ↔
      PairedStrongTensorComponentwiseSystemAt period hPeriod configuration data
        analysis realization plusBase minusBase hBase point hPoint hPlus hMinus :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
      (pairedStrongTensorComponentwisePDEDataAt period hPeriod configuration data
        analysis realization plusBase minusBase hBase point hPoint hPlus hMinus)

end
end P0EFTJanusPairedStrongTensorComponentwisePDE4D
end JanusFormal
