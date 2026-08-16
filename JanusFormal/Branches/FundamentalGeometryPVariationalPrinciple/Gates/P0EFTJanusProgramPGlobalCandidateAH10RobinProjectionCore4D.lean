import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSecondFrechetLinearPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D

/-!
# H10 Robin agreement from action-level projection data

The dense-core H11 route formerly accepted equality of two Robin Hessians as a
field.  This file lowers that requirement to the natural action-level data:

* the local Robin scalar is the completed H10 GHY action after one bounded
  linear projection;
* the completed boundary projection and the local projection agree on the
  typed smooth core.

The generic linear-pullback Hessian theorem then constructs the Robin Hessian
agreement automatically.  Thus no second-Fréchet identity is supplied by hand.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPSecondFrechetLinearPullback4D
open P0EFTJanusConvexHelmholtzReconstruction

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

private abbrev PhysicalCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev CommonHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance h10ProjectionBoundaryCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance h10ProjectionBoundaryCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance h10ProjectionBoundaryCoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreCompleteSpace period hPeriod metric

/-- Action-level Robin projection data.  The only comparison on the dense core
is equality of the projected boundary parameter, not equality of Hessians. -/
structure GlobalCandidateAH10RobinProjectionCoreData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real) where
  localProjection : chart.Model →L[Real]
    Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod
        data.plusGravity.metric) Real
  completedProjection :
    CommonHilbert period hPeriod configuration data analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real
  localProjection_base_zero :
    localProjection sameAction.chartBridge.basePoint = 0
  robinAction_eq :
    (globalCandidateACanonicalSixLocalBlocks period hPeriod chart).robin =
      fun state =>
        candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale data.plusGravity.metric (localProjection state)
  smoothCoreProjectionAgreement : ∀ core : PhysicalCore period hPeriod analysis,
    completedProjection
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis core) =
      localProjection
        (globalCandidateACanonicalSixCoreToChart period hPeriod configuration
          data analysis chart sameAction core)

/-- The local Robin Hessian is the pullback of the genuine H10 second Fréchet
derivative. -/
theorem globalCandidateALocalRobinHessian_eq_h10Pullback
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis chart sameAction einsteinScale) :
    fderiv Real
        (actionGradient
          (globalCandidateACanonicalSixLocalBlocks period hPeriod chart).robin)
        sameAction.chartBridge.basePoint =
      (candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
        einsteinScale data.plusGravity.metric).bilinearComp
          projection.localProjection projection.localProjection := by
  have hCompletedC2 :=
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffAt_two
      period hPeriod einsteinScale data.plusGravity.metric hTransverse
  have hCompletedAtProjection :
      ContDiffAt Real 2
        (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale data.plusGravity.metric)
        (projection.localProjection sameAction.chartBridge.basePoint) := by
    simpa [projection.localProjection_base_zero] using hCompletedC2
  have hPullback := secondFrechet_eq_bilinearComp_of_action_eq
    (globalCandidateACanonicalSixLocalBlocks period hPeriod chart).robin
    (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale data.plusGravity.metric)
    projection.localProjection sameAction.chartBridge.basePoint
    projection.robinAction_eq hCompletedAtProjection
  simpa [candidateANormalBoundaryTwoSheetGHYActionHessian] using hPullback

/-- Action-level projection data constructs the previous dense-core Robin
Hessian agreement packet. -/
def GlobalCandidateAH10RobinProjectionCoreData4D.toDenseCoreAgreement
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {einsteinScale : Real}
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis chart sameAction einsteinScale)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric) :
    GlobalCandidateAH10RobinDenseCoreAgreement4D period hPeriod configuration
      data analysis chart sameAction einsteinScale where
  boundaryProjection := projection.completedProjection
  robinCore_eq_chart := by
    ext first second
    unfold globalCandidateAH10RobinCoreLinearForm
      globalCandidateAH10RobinCommonDomainForm
    simp only [denseCoreChartBilinearPullback_apply,
      ContinuousLinearMap.bilinearComp_apply]
    rw [projection.smoothCoreProjectionAgreement first,
      projection.smoothCoreProjectionAgreement second]
    rw [globalCandidateALocalRobinHessian_eq_h10Pullback period hPeriod
      configuration data analysis chart sameAction einsteinScale hTransverse
        projection]
    rfl

/-- Direct public checkpoint eliminating a supplied Robin Hessian equality. -/
theorem global_candidateA_h10_robin_projection_core_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {einsteinScale : Real}
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis chart sameAction einsteinScale)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric) :
    GlobalCandidateAH10RobinDenseCoreAgreement4D period hPeriod configuration
      data analysis chart sameAction einsteinScale :=
  projection.toDenseCoreAgreement period hPeriod hTransverse

end
end P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
end JanusFormal
