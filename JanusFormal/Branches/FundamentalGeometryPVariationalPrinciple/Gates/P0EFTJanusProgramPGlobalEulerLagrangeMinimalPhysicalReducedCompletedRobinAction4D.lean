import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGaugeAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D

/-!
# Completed reduced Robin action

An H10 action-level projection that agrees with the canonical local chart on
the smooth core annihilates the closed minimal-physical null space.  It thus
descends to the reduced Hilbert completion.  Pulling back the genuine H10 GHY
functional gives a `C²` Robin action on its natural open domain and recovers
the established local Robin block on the quotient core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRobinAction4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedSmoothCoreHilbertCompletion4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMatterLLAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGaugeAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData)
      einsteinScale)

local instance completedRobinBoundaryCoreNormedAddCommGroup :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod
        data.plusGravity.metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod
    data.plusGravity.metric

local instance completedRobinBoundaryCoreNormedSpace :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod
        data.plusGravity.metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod
    data.plusGravity.metric

local instance completedRobinBoundaryCoreCompleteSpace :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod
        data.plusGravity.metric) :=
  candidateANormalBoundaryFunctionalCoreCompleteSpace period hPeriod
    data.plusGravity.metric

/-- The H10 projection kills the entire closed null space used in the minimal
physical Hilbert reduction. -/
theorem globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule_le_robinProjection_ker :
    globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
        configuration data analysis ≤
      projection.completedProjection.ker := by
  unfold globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule
  apply Submodule.topologicalClosure_minimal
  · intro state hState
    rcases hState with ⟨kernelCore, rfl⟩
    apply LinearMap.mem_ker.mpr
    change
      projection.completedProjection
          (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis kernelCore.1) = 0
    rw [projection.smoothCoreProjectionAgreement kernelCore.1]
    have hChart :
        globalCandidateACanonicalSixCoreToChart period hPeriod configuration
            data analysis
            (globalCandidateAMinimalPhysicalLocalVariationalChart period
              hPeriod configuration data analysis chartData)
            (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period
              hPeriod configuration data analysis chartData) kernelCore.1 = 0 := by
      apply LinearMap.mem_ker.mp
      rw [globalCandidateAMinimalPhysicalCanonicalCoreToChart_ker period
        hPeriod configuration data analysis chartData]
      exact kernelCore.2
    rw [hChart, map_zero]
  · exact projection.completedProjection.isClosed_ker

/-- The completed H10 projection is invariant under the canonical orthogonal
minimal-physical reduction. -/
theorem globalCandidateAMinimalPhysicalRobinProjection_reduction
    (state : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    projection.completedProjection
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis state) =
      projection.completedProjection state := by
  have hClosed :=
    common_sub_minimalPhysicalReduction_mem_closedNull period hPeriod
      configuration data analysis state
  have hKernel :=
    globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule_le_robinProjection_ker
      period hPeriod configuration data analysis chartData einsteinScale
        projection hClosed
  have hZero := LinearMap.mem_ker.mp hKernel
  rw [map_sub] at hZero
  exact (sub_eq_zero.mp hZero).symm

/-- Completed Robin boundary coordinate on the reduced Hilbert space. -/
def globalCandidateAMinimalPhysicalReducedRobinProjection :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real :=
  projection.completedProjection.comp
    (globalCandidateAMinimalPhysicalReducedHilbertInclusion period hPeriod
      configuration data analysis)

@[simp]
theorem globalCandidateAMinimalPhysicalReducedRobinProjection_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedRobinProjection period hPeriod
        configuration data analysis chartData einsteinScale projection
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      projection.localProjection
        (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
          configuration data analysis chartData
          (Submodule.Quotient.mk core)) := by
  rw [globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk,
    globalCandidateAMinimalPhysicalReducedCoreToChart_mk]
  change
    projection.completedProjection
        (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
          configuration data analysis
          (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
            configuration data analysis core)) = _
  rw [globalCandidateAMinimalPhysicalRobinProjection_reduction period hPeriod
    configuration data analysis chartData einsteinScale projection]
  change
    projection.completedProjection
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
          configuration data analysis core) = _
  exact projection.smoothCoreProjectionAgreement core

/-- Natural open reduced domain on which the completed GHY/Robin action is
`C²`. -/
def globalCandidateAMinimalPhysicalReducedRobinDomain : Set
    (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :=
  globalCandidateAMinimalPhysicalReducedRobinProjection period hPeriod
      configuration data analysis chartData einsteinScale projection ⁻¹'
    candidateANormalBoundaryGHYDomain period hPeriod data.plusGravity.metric

theorem globalCandidateAMinimalPhysicalReducedRobinDomain_isOpen :
    IsOpen
      (globalCandidateAMinimalPhysicalReducedRobinDomain period hPeriod
        configuration data analysis chartData einsteinScale projection) :=
  (candidateANormalBoundaryGHYDomain_isOpen period hPeriod
    data.plusGravity.metric).preimage
      (globalCandidateAMinimalPhysicalReducedRobinProjection period hPeriod
        configuration data analysis chartData einsteinScale projection).continuous

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedRobinDomain_zero_mem :
    (0 : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) ∈
      globalCandidateAMinimalPhysicalReducedRobinDomain period hPeriod
        configuration data analysis chartData einsteinScale projection := by
  change
    globalCandidateAMinimalPhysicalReducedRobinProjection period hPeriod
        configuration data analysis chartData einsteinScale projection 0 ∈
      candidateANormalBoundaryGHYDomain period hPeriod data.plusGravity.metric
  rw [map_zero]
  exact zero_mem_candidateANormalBoundaryGHYDomain period hPeriod
    data.plusGravity.metric hTransverse

/-- Genuine completed H10 Robin action on the reduced Hilbert space. -/
def globalCandidateAMinimalPhysicalReducedCompletedRobinAction :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis → Real :=
  fun state =>
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale data.plusGravity.metric
      (globalCandidateAMinimalPhysicalReducedRobinProjection period hPeriod
        configuration data analysis chartData einsteinScale projection state)

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedRobinAction_contDiffOn_two :
    ContDiffOn Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedRobinAction period
        hPeriod configuration data analysis chartData einsteinScale projection)
      (globalCandidateAMinimalPhysicalReducedRobinDomain period hPeriod
        configuration data analysis chartData einsteinScale projection) := by
  exact
    (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffOn_two
      period hPeriod einsteinScale data.plusGravity.metric hTransverse).comp
        (globalCandidateAMinimalPhysicalReducedRobinProjection period hPeriod
          configuration data analysis chartData einsteinScale
            projection).contDiff.contDiffOn
        (fun _ hState => hState)

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedRobinAction_contDiffAt_zero :
    ContDiffAt Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedRobinAction period
        hPeriod configuration data analysis chartData einsteinScale projection)
      0 := by
  exact
    (globalCandidateAMinimalPhysicalReducedCompletedRobinAction_contDiffOn_two
      period hPeriod configuration data analysis chartData einsteinScale
        hTransverse projection).contDiffAt
      ((globalCandidateAMinimalPhysicalReducedRobinDomain_isOpen period hPeriod
        configuration data analysis chartData einsteinScale projection).mem_nhds
        (globalCandidateAMinimalPhysicalReducedRobinDomain_zero_mem period
          hPeriod configuration data analysis chartData einsteinScale
            hTransverse projection))

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedRobinAction_core
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedRobinAction period hPeriod
        configuration data analysis chartData einsteinScale projection
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      (globalCandidateACanonicalSixLocalBlocks period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)).robin
        (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
          configuration data analysis chartData
          (Submodule.Quotient.mk core)) := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedRobinAction,
    globalCandidateAMinimalPhysicalReducedRobinProjection_core]
  exact (congrFun projection.robinAction_eq
    (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
      configuration data analysis chartData
      (Submodule.Quotient.mk core))).symm

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRobinAction4D
end JanusFormal
