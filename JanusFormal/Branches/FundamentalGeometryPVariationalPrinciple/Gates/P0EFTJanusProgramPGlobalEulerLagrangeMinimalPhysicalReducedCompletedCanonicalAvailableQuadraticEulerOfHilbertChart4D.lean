import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfBounds4D

/-!
# Canonical available Euler operator from the common Hilbert chart

The common-Hilbert chart contract now supplies the seven canonical physical
extensions used by the strongest available reduced quadratic action.  The
only remaining inputs are the genuine Robin projection data and its
transversality hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerOfHilbertChart4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open Filter Set Topology MeasureTheory
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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfBounds4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGaugeAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEuler4D

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

private abbrev MinimalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev SameAction :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData

variable
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData)
      einsteinScale)
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData))

private abbrev Core :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev Reduced :=
  GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
    data analysis

/-- The common Hilbert chart constructs the canonical seven-extension packet. -/
def globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart :
    GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData) :=
  globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_hilbertChart
    period hPeriod configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData)
      hilbertChart

/-- Canonical seven named blocks obtained from the common Hilbert chart. -/
def globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks_of_hilbertChart :
    GlobalCandidateASevenPhysicalBlockExtensions4D period hPeriod configuration
      data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData) :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks period hPeriod
    configuration data analysis chartData
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
        period hPeriod configuration data analysis chartData hilbertChart)

/-- Strongest available reduced quadratic action, with no separately supplied
seven-block completion. -/
def globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart :
    Reduced period hPeriod configuration data analysis → Real :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction
    period hPeriod configuration data analysis chartData einsteinScale projection
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
        period hPeriod configuration data analysis chartData hilbertChart)

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart_contDiffOn_two :
    ContDiffOn Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart
        period hPeriod configuration data analysis chartData einsteinScale
          projection hilbertChart)
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_contDiffOn_two
      period hPeriod configuration data analysis chartData einsteinScale
        hTransverse projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
          period hPeriod configuration data analysis chartData hilbertChart)

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart_contDiffAt_zero :
    ContDiffAt Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart
        period hPeriod configuration data analysis chartData einsteinScale
          projection hilbertChart) 0 := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_contDiffAt_zero
      period hPeriod configuration data analysis chartData einsteinScale
        hTransverse projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
          period hPeriod configuration data analysis chartData hilbertChart)

/-- Frechet Euler covector of the Hilbert-chart-instantiated action. -/
noncomputable def globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerCovector_of_hilbertChart
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis →L[Real] Real :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerCovector
    period hPeriod configuration data analysis chartData einsteinScale projection
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
        period hPeriod configuration data analysis chartData hilbertChart) state

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerCovector_eq_fderiv_of_hilbertChart
    (state : Reduced period hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerCovector_of_hilbertChart
        period hPeriod configuration data analysis chartData einsteinScale
          projection hilbertChart state =
      fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart
          period hPeriod configuration data analysis chartData einsteinScale
            projection hilbertChart) state :=
  rfl

/-- Strong Riesz residual of the Hilbert-chart-instantiated action. -/
noncomputable def globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual_of_hilbertChart
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual
    period hPeriod configuration data analysis chartData einsteinScale projection
      (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
        period hPeriod configuration data analysis chartData hilbertChart) state

theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual_pairing_of_hilbertChart
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual_of_hilbertChart
          period hPeriod configuration data analysis chartData einsteinScale
            projection hilbertChart state) test =
      globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerCovector_of_hilbertChart
        period hPeriod configuration data analysis chartData einsteinScale
          projection hilbertChart state test := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual_pairing
      period hPeriod configuration data analysis chartData einsteinScale
        projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
          period hPeriod configuration data analysis chartData hilbertChart)
        state test

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_fderiv_add_of_hilbertChart
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart
          period hPeriod configuration data analysis chartData einsteinScale
            projection hilbertChart) state =
      fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
            period hPeriod configuration data analysis chartData einsteinScale
              projection
              (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks_of_hilbertChart
                period hPeriod configuration data analysis chartData
                  hilbertChart).maxwellPlus
              (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks_of_hilbertChart
                period hPeriod configuration data analysis chartData
                  hilbertChart).maxwellMinus) state +
        globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
          period hPeriod configuration data analysis chartData
            (globalCandidateAMinimalPhysicalReducedCompletedCanonicalBlocks_of_hilbertChart
              period hPeriod configuration data analysis chartData hilbertChart)
            state := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_fderiv_add
      period hPeriod configuration data analysis chartData einsteinScale
        hTransverse projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
          period hPeriod configuration data analysis chartData hilbertChart)
        state hState

/-- Criticality expressed by the strong Hilbert residual. -/
def GlobalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticIsCritical_of_hilbertChart
    (state : Reduced period hPeriod configuration data analysis) : Prop :=
  globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual_of_hilbertChart
    period hPeriod configuration data analysis chartData einsteinScale projection
      hilbertChart state = 0

theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticIsCritical_iff_fderiv_eq_zero_of_hilbertChart
    (state : Reduced period hPeriod configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticIsCritical_of_hilbertChart
        period hPeriod configuration data analysis chartData einsteinScale
          projection hilbertChart state ↔
      fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart
            period hPeriod configuration data analysis chartData einsteinScale
              projection hilbertChart) state = 0 := by
  change
    GlobalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticIsCritical
        period hPeriod configuration data analysis chartData einsteinScale
          projection
          (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
            period hPeriod configuration data analysis chartData hilbertChart)
          state ↔ _
  exact
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticIsCritical_iff_fderiv_eq_zero
      period hPeriod configuration data analysis chartData einsteinScale projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
          period hPeriod configuration data analysis chartData hilbertChart)
        state

/-- Gate 197: the common Hilbert chart yields the available action, its strong
Euler residual, and the exact Riesz pairing without a separate seven-block
extension input. -/
theorem candidate_a_canonical_available_quadratic_euler_of_hilbertChart_gate
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual_of_hilbertChart
          period hPeriod configuration data analysis chartData einsteinScale
            projection hilbertChart state) test =
      fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart
          period hPeriod configuration data analysis chartData einsteinScale
            projection hilbertChart) state test := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticRieszResidual_pairing_of_hilbertChart
      period hPeriod configuration data analysis chartData einsteinScale
        projection hilbertChart state test

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_core_of_hilbertChart
    (core : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_of_hilbertChart
        period hPeriod configuration data analysis chartData einsteinScale
          projection hilbertChart
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      (globalCandidateAMinimalPhysicalReducedCompletedGraphAction period hPeriod
          configuration data analysis
          (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
            period hPeriod configuration data analysis
            (Submodule.Quotient.mk core)) +
        (globalCandidateACanonicalSixLocalBlocks period hPeriod
          (MinimalChart period hPeriod configuration data analysis chartData)).robin
          (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
            configuration data analysis chartData
            (Submodule.Quotient.mk core)) +
        ((1 / 2 : Real) *
            diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core +
          (1 / 2 : Real) *
            diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core)) +
        (1 / 2 : Real) *
          (((diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core +
            diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core) +
            diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core) +
            diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core) := by
  exact
    globalCandidateAMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticAction_core
      period hPeriod configuration data analysis chartData einsteinScale
        projection
        (globalCandidateAMinimalPhysicalReducedCompletedCanonicalExtensions_of_hilbertChart
          period hPeriod configuration data analysis chartData hilbertChart)
        core

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEulerOfHilbertChart4D
end JanusFormal
