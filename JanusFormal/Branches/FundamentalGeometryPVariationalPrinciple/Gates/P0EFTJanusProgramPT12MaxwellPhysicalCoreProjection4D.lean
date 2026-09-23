import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongMaxwellActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertKernelSaturation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12MaxwellPhysicalCoreProjection4D

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
theorem pairedPlusProjection_minimal
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical) :
    pairedMaxwellPlusProjection period hPeriod plusBase minusBase
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod configuration.physical
        plusBase minusBase direction) =
    (regularGeneralMetricC2SmoothDirection period hPeriod plusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus),
     smoothGaugeCoefficientC2CoreLinearMap period hPeriod direction.1.completeVariation.independent.gauge.1) := rfl

theorem pairedPlusProjection_diagonalCore
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    pairedMaxwellPlusProjection period hPeriod plusBase minusBase
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod configuration.physical plusBase minusBase
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis core)) =
    (regularGeneralMetricC2SmoothDirection period hPeriod plusBase (core.1.metricPerturbation .plus),
     maxwellSmoothGaugeC2 period hPeriod data.plusGravity.metric (core.2.1.potential .plus)) := by
  rw [pairedPlusProjection_minimal, diagonalExtendedBulkMinimalPhysicalTangent_metric,
    diagonalExtendedBulkMinimalPhysicalTangent_gauge]
  rfl

theorem pairedPlusProjection_diffeomorphismCore
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    pairedMaxwellPlusProjection period hPeriod plusBase minusBase
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod configuration.physical plusBase minusBase
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
          (diffeomorphismCore period hPeriod configuration analysis field))) =
    (regularGeneralMetricC2SmoothDirection period hPeriod plusBase (field.metricPerturbation .plus), 0) := by
  rw [pairedPlusProjection_diagonalCore]
  change (_, maxwellSmoothGaugeC2 period hPeriod data.plusGravity.metric 0) = _
  rw [map_zero]
  rfl

theorem pairedPlusProjection_abelianCore
    (field : GlobalPairedAbelianBRSTState period hPeriod) :
    pairedMaxwellPlusProjection period hPeriod plusBase minusBase
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod configuration.physical plusBase minusBase
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
          (abelianCore period hPeriod configuration analysis field))) =
    (0, maxwellSmoothGaugeC2 period hPeriod data.plusGravity.metric (field.potential .plus)) := by
  rw [pairedPlusProjection_diagonalCore]
  change (regularGeneralMetricC2SmoothDirection period hPeriod plusBase 0, _) = _
  simp only [regularGeneralMetricC2SmoothDirection, map_zero]
  rfl
theorem pairedMinusProjection_minimal
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical) :
    pairedMaxwellMinusProjection period hPeriod plusBase minusBase
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod configuration.physical
        plusBase minusBase direction) =
    (regularGeneralMetricC2SmoothDirection period hPeriod minusBase
      (direction.1.completeVariation.fullMetricPerturbation .minus),
     smoothGaugeCoefficientC2CoreLinearMap period hPeriod direction.1.completeVariation.independent.gauge.2) := rfl

theorem pairedMinusProjection_diagonalCore
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    pairedMaxwellMinusProjection period hPeriod plusBase minusBase
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod configuration.physical plusBase minusBase
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis core)) =
    (regularGeneralMetricC2SmoothDirection period hPeriod minusBase (core.1.metricPerturbation .minus),
     maxwellSmoothGaugeC2 period hPeriod data.minusGravity.metric (core.2.1.potential .minus)) := by
  rw [pairedMinusProjection_minimal, diagonalExtendedBulkMinimalPhysicalTangent_metric,
    diagonalExtendedBulkMinimalPhysicalTangent_gauge]
  rfl

theorem pairedMinusProjection_diffeomorphismCore
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    pairedMaxwellMinusProjection period hPeriod plusBase minusBase
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod configuration.physical plusBase minusBase
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
          (diffeomorphismCore period hPeriod configuration analysis field))) =
    (regularGeneralMetricC2SmoothDirection period hPeriod minusBase (field.metricPerturbation .minus), 0) := by
  rw [pairedMinusProjection_diagonalCore]
  change (_, maxwellSmoothGaugeC2 period hPeriod data.minusGravity.metric 0) = _
  rw [map_zero]
  rfl

theorem pairedMinusProjection_abelianCore
    (field : GlobalPairedAbelianBRSTState period hPeriod) :
    pairedMaxwellMinusProjection period hPeriod plusBase minusBase
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod configuration.physical plusBase minusBase
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod configuration data analysis
          (abelianCore period hPeriod configuration analysis field))) =
    (0, maxwellSmoothGaugeC2 period hPeriod data.minusGravity.metric (field.potential .minus)) := by
  rw [pairedMinusProjection_diagonalCore]
  change (regularGeneralMetricC2SmoothDirection period hPeriod minusBase 0, _) = _
  simp only [regularGeneralMetricC2SmoothDirection, map_zero]
  rfl

end
end P0EFTJanusProgramPT12MaxwellPhysicalCoreProjection4D
end JanusFormal
