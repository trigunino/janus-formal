import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeCanonicalSixDenseCoreRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D

/-!
# Canonical-six Euler residual from H10 action-level Robin projection data

The Robin Hessian agreement is derived from equality of the local Robin action
with the completed H10 action after a bounded projection, plus agreement of
that projection on the typed smooth core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeCanonicalSixRobinProjectionRieszResidual4D

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
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeCanonicalSixDenseCoreRieszResidual4D

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
variable (projection : GlobalCandidateAH10RobinProjectionCoreData4D period
  hPeriod configuration data analysis chart sameAction einsteinScale)
variable (hTransverse : HasNoTangentialRadical period hPeriod
  data.plusGravity.metric.metric)
variable (chartBound : DenseCoreChartMapBound
  (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration data
    analysis)
  (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
    analysis chart sameAction))

/-- Robin dense-core agreement derived from action-level projection data. -/
def globalCandidateACanonicalSixRobinProjectionAgreement :
    GlobalCandidateAH10RobinDenseCoreAgreement4D period hPeriod configuration
      data analysis chart sameAction einsteinScale :=
  projection.toDenseCoreAgreement period hPeriod hTransverse

/-- Full action with canonical six blocks and action-derived Robin agreement. -/
def globalCandidateACanonicalSixRobinProjectionAugmentedAction
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    Real :=
  globalCandidateACanonicalSixDenseCoreAugmentedAction period hPeriod
    configuration data analysis chart sameAction einsteinScale
      (globalCandidateACanonicalSixRobinProjectionAgreement period hPeriod
        configuration data analysis chart sameAction einsteinScale projection
          hTransverse) chartBound state

/-- Its canonical strong Riesz residual. -/
def globalCandidateACanonicalSixRobinProjectionRieszResidual
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    CommonAugmentedHilbert period hPeriod configuration data analysis :=
  globalCandidateACanonicalSixDenseCoreRieszResidual period hPeriod
    configuration data analysis chart sameAction einsteinScale
      (globalCandidateACanonicalSixRobinProjectionAgreement period hPeriod
        configuration data analysis chart sameAction einsteinScale projection
          hTransverse) chartBound state

/-- Stationarity is equivalent to the strong residual equation, with no
supplied Robin Hessian equality. -/
theorem globalCandidateACanonicalSixRobinProjectionEulerCovector_eq_zero_iff_rieszResidual
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    fderiv Real
        (globalCandidateACanonicalSixRobinProjectionAugmentedAction period
          hPeriod configuration data analysis chart sameAction einsteinScale
            projection hTransverse chartBound) state = 0 ↔
      globalCandidateACanonicalSixRobinProjectionRieszResidual period hPeriod
        configuration data analysis chart sameAction einsteinScale projection
          hTransverse chartBound state = 0 := by
  unfold globalCandidateACanonicalSixRobinProjectionAugmentedAction
  unfold globalCandidateACanonicalSixRobinProjectionRieszResidual
  exact
    globalCandidateACanonicalSixDenseCoreEulerCovector_eq_zero_iff_rieszResidual
      period hPeriod configuration data analysis chart sameAction einsteinScale
        (globalCandidateACanonicalSixRobinProjectionAgreement period hPeriod
          configuration data analysis chart sameAction einsteinScale projection
            hTransverse) chartBound state

/-- The action-derived residual pairing is the full local gauge-fixed Hessian
on the typed dense core. -/
theorem globalCandidateACanonicalSixRobinProjectionRieszResidual_smooth_pairing
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    globalCandidateAFaithfulAugmentedRieszResidualPairing period hPeriod
        configuration data analysis
        (globalCandidateACanonicalSixRobinProjectionRieszResidual period hPeriod
          configuration data analysis chart sameAction einsteinScale projection
            hTransverse chartBound
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis first))
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second := by
  simpa only [globalCandidateACanonicalSixRobinProjectionRieszResidual] using
    globalCandidateACanonicalSixDenseCoreRieszResidual_smooth_pairing period
      hPeriod configuration data analysis chart sameAction einsteinScale
        (globalCandidateACanonicalSixRobinProjectionAgreement period hPeriod
          configuration data analysis chart sameAction einsteinScale projection
            hTransverse) chartBound first second

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeCanonicalSixRobinProjectionRieszResidual4D
end JanusFormal
