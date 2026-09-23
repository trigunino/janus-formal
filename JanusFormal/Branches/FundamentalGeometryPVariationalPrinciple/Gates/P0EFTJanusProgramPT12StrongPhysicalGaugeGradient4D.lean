import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongMaxwellBRSTMixedHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PhysicalGaugeHessianReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeReducedCoupledResidual4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongPhysicalGaugeGradient4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

open P0EFTJanusProgramPT12ProjectedGradientDerivative4D
open P0EFTJanusProgramPT12PairedMaxwellCenterC24D
open P0EFTJanusProgramPT12PairedMaxwellHessianPullback4D
open P0EFTJanusProgramPT12MaxwellNativeMixedHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)
  (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D period hPeriod couplings.matterMassSquared)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D
open P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPT12MaxwellPhysicalCoreProjection4D
open P0EFTJanusProgramPT12StrongMaxwellActionHessian4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D

open P0EFTJanusProgramPT12PhysicalGaugeHessianReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeReducedCoupledResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellWeakFirstVariation4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D

/-- The actual abelian core has precisely the existing pure strong gauge direction. -/
theorem abelianCore_physicalTangent_eq_strongGauge
    (test : GlobalPairedAbelianBRSTState period hPeriod) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
      (abelianCore period hPeriod configuration analysis test) =
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period hPeriod configuration.physical
      (globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod data test.potential) := by
  change (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod configuration 0 +
    globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod configuration data test +
    extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration 0 +
    extendedLLGaugeFixedTangentLinearMap period hPeriod configuration analysis 0).1 = _
  simp only [map_zero, zero_add, add_zero]
  rfl

variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible period hPeriod plusBase minusBase)
  (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical)
  (hPoint : point ∈ regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
    period hPeriod configuration.physical plusBase minusBase)
def strongPhysicalBlocksC2At :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    FullCoupledC2At (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase hBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact fullCoupledC2WithinAt_toAt
    (regularGeneralMetricC2PairedMinimalPhysicalNineBlockC2WithinAt period hPeriod configuration data analysis
      realization plusBase minusBase hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint)
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase) hPoint

include hPoint in
theorem strongPhysicalGradient_gauge_eq_maxwell
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    let blocks := regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase hBase
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection
      period hPeriod configuration.physical test
    actionGradient (fullCoupledPhysicalAction blocks) point direction =
      actionGradient blocks.maxwellPlus point direction + actionGradient blocks.maxwellMinus point direction := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hCandidate := regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_strongGauge_eq_zero
    period hPeriod configuration data analysis realization plusBase minusBase hBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint test
  have hEinstein := regularGeneralMetricC2PairedMinimalPhysicalEinsteinHilbert_actionGradient_strongGauge_eq_zero
    period hPeriod configuration data analysis realization plusBase minusBase hBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint test
  have hRobin := regularGeneralMetricC2PairedMinimalPhysicalRobin_actionGradient_eq_zero
    period hPeriod configuration data analysis realization plusBase minusBase hBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint
  have hFinite := regularGeneralMetricC2PairedMinimalPhysicalFiniteBV_actionGradient_eq_zero
    period hPeriod configuration data analysis realization plusBase minusBase hBase
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint
  refine physicalGradient_eq_maxwell_of_zero _ point _
    (strongPhysicalBlocksC2At period hPeriod configuration data analysis realization
      plusBase minusBase hBase point hPoint) hCandidate ?_ hEinstein.1 hEinstein.2 ?_
  · rw [hRobin]
    rfl
  · rw [hFinite]
    rfl

end
end P0EFTJanusProgramPT12StrongPhysicalGaugeGradient4D
end JanusFormal
