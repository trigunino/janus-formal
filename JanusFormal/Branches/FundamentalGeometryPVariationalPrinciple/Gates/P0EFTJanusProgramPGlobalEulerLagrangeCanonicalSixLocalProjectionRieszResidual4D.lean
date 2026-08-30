import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeCanonicalSixContinuousChartRieszResidual4D

/-!
# Canonical-six Euler residual from local H10 projection data

The completed boundary projection is no longer supplied: it is the composite
of the local H10 projection with the bounded Hilbert-to-chart realization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeCanonicalSixLocalProjectionRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set Topology MeasureTheory
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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeCanonicalSixContinuousChartRieszResidual4D

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

local instance localProjectionBoundaryCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance localProjectionBoundaryCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance localProjectionBoundaryCoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreCompleteSpace period hPeriod metric

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod
  couplings NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (einsteinScale : Real)
variable (hTransverse : HasNoTangentialRadical period hPeriod
  data.plusGravity.metric.metric)
variable (chartRealization :
  CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
    chart.Model)
variable (smoothCoreAgreement :
  ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis,
    chartRealization
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod
          configuration data analysis core) =
      globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis chart sameAction core)
variable (localProjection : chart.Model →L[Real]
  Prod
    (CandidateANormalBoundaryFunctionalCore period hPeriod
      data.plusGravity.metric) Real)
variable (localProjection_base_zero :
  localProjection sameAction.chartBridge.basePoint = 0)
variable (robinAction_eq :
  (globalCandidateACanonicalSixLocalBlocks period hPeriod chart).robin =
    fun state =>
      candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale data.plusGravity.metric (localProjection state))

/-- Complete H10 projection data obtained by composing the local projection
with the continuous chart realization. -/
def globalCandidateACanonicalSixLocalProjectionCoreData :
    GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod configuration
      data analysis chart sameAction einsteinScale where
  localProjection := localProjection
  completedProjection := localProjection.comp chartRealization
  localProjection_base_zero := localProjection_base_zero
  robinAction_eq := robinAction_eq
  smoothCoreProjectionAgreement := by
    intro core
    rw [ContinuousLinearMap.comp_apply, smoothCoreAgreement core]

/-- Full action generated from local projection data alone. -/
def globalCandidateACanonicalSixLocalProjectionAugmentedAction
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    Real :=
  globalCandidateACanonicalSixContinuousChartAugmentedAction period hPeriod
    configuration data analysis chart sameAction einsteinScale
      (globalCandidateACanonicalSixLocalProjectionCoreData period hPeriod
        configuration data analysis chart sameAction einsteinScale
          chartRealization smoothCoreAgreement localProjection
            localProjection_base_zero robinAction_eq)
      hTransverse chartRealization smoothCoreAgreement state

/-- Strong Riesz residual generated from local projection data alone. -/
def globalCandidateACanonicalSixLocalProjectionRieszResidual
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    CommonAugmentedHilbert period hPeriod configuration data analysis :=
  globalCandidateACanonicalSixContinuousChartRieszResidual period hPeriod
    configuration data analysis chart sameAction einsteinScale
      (globalCandidateACanonicalSixLocalProjectionCoreData period hPeriod
        configuration data analysis chart sameAction einsteinScale
          chartRealization smoothCoreAgreement localProjection
            localProjection_base_zero robinAction_eq)
      hTransverse chartRealization smoothCoreAgreement state

/-- Its Euler covector vanishes exactly when the strong residual vanishes. -/
theorem globalCandidateACanonicalSixLocalProjectionEulerCovector_eq_zero_iff_rieszResidual
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    fderiv Real
        (globalCandidateACanonicalSixLocalProjectionAugmentedAction period
          hPeriod configuration data analysis chart sameAction einsteinScale
            hTransverse chartRealization smoothCoreAgreement localProjection
              localProjection_base_zero robinAction_eq) state = 0 ↔
      globalCandidateACanonicalSixLocalProjectionRieszResidual period hPeriod
        configuration data analysis chart sameAction einsteinScale hTransverse
          chartRealization smoothCoreAgreement localProjection
            localProjection_base_zero robinAction_eq state = 0 := by
  unfold globalCandidateACanonicalSixLocalProjectionAugmentedAction
  unfold globalCandidateACanonicalSixLocalProjectionRieszResidual
  exact
    globalCandidateACanonicalSixContinuousChartEulerCovector_eq_zero_iff_rieszResidual
      period hPeriod configuration data analysis chart sameAction einsteinScale
        (globalCandidateACanonicalSixLocalProjectionCoreData period hPeriod
          configuration data analysis chart sameAction einsteinScale
            chartRealization smoothCoreAgreement localProjection
              localProjection_base_zero robinAction_eq)
        hTransverse chartRealization smoothCoreAgreement state

/-- The residual pairing remains the exact local gauge-fixed Hessian. -/
theorem globalCandidateACanonicalSixLocalProjectionRieszResidual_smooth_pairing
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    globalCandidateAFaithfulAugmentedRieszResidualPairing period hPeriod
        configuration data analysis
        (globalCandidateACanonicalSixLocalProjectionRieszResidual period hPeriod
          configuration data analysis chart sameAction einsteinScale
            hTransverse chartRealization smoothCoreAgreement localProjection
              localProjection_base_zero robinAction_eq
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis first))
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second := by
  simpa only [globalCandidateACanonicalSixLocalProjectionRieszResidual] using
    globalCandidateACanonicalSixContinuousChartRieszResidual_smooth_pairing
      period hPeriod configuration data analysis chart sameAction einsteinScale
        (globalCandidateACanonicalSixLocalProjectionCoreData period hPeriod
          configuration data analysis chart sameAction einsteinScale
            chartRealization smoothCoreAgreement localProjection
              localProjection_base_zero robinAction_eq)
        hTransverse chartRealization smoothCoreAgreement first second

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeCanonicalSixLocalProjectionRieszResidual4D
end JanusFormal
