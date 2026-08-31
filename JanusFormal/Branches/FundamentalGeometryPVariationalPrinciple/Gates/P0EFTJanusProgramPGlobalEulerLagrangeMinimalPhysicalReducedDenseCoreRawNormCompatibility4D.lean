import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreClosureOfHilbertChart4D

/-!
# Raw-core form of the reduced norm compatibility

The sole norm identity needed by the reduced dense-core closure is equivalent
to the corresponding identity on raw smooth representatives.  This isolates
the remaining analytic estimate before passage to the quotient.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreRawNormCompatibility4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreClosureOfHilbertChart4D

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

local instance reducedRawNormCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance reducedRawNormCommonInnerProductSpace : InnerProductSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance reducedRawNormCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (reducedRawNormCommonInnerProductSpace period hPeriod configuration data
    analysis).toNormedSpace

local instance reducedRawNormCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (reducedRawNormCommonNormedSpace period hPeriod configuration data
    analysis).toModule

local instance reducedRawNormCommonCompleteSpace : CompleteSpace
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The remaining identity stated directly on raw smooth representatives. -/
def GlobalCandidateAMinimalPhysicalReducedRawCoreNormCompatibility : Prop :=
  ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis,
    ‖globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData) core‖ =
      ‖globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
        configuration data analysis core‖

/-- The same identity on the physical quotient smooth core. -/
def GlobalCandidateAMinimalPhysicalReducedCoreNormCompatibility : Prop :=
  ∀ core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
      configuration data analysis,
    ‖globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
        configuration data analysis chartData core‖ =
      ‖globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding period
        hPeriod configuration data analysis core‖

/-- Passing to the algebraic quotient neither loses nor adds a norm
obligation. -/
theorem globalCandidateAMinimalPhysicalReducedCoreNormCompatibility_iff_rawCore :
    GlobalCandidateAMinimalPhysicalReducedCoreNormCompatibility period hPeriod
        configuration data analysis chartData ↔
      GlobalCandidateAMinimalPhysicalReducedRawCoreNormCompatibility period
        hPeriod configuration data analysis chartData := by
  constructor
  · intro hCompatibility core
    simpa only [globalCandidateAMinimalPhysicalReducedCoreToChart_mk,
      globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
      using hCompatibility (Submodule.Quotient.mk core)
  · intro hCompatibility core
    obtain ⟨representative, rfl⟩ := Submodule.Quotient.mk_surjective
      (globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis) core
    simpa only [globalCandidateAMinimalPhysicalReducedCoreToChart_mk,
      globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
      using hCompatibility representative

/-- A reduced chart plus the raw representative identity supplies the entire
dense-core closure certificate. -/
def globalCandidateAMinimalPhysicalReducedDenseCoreClosure_of_hilbertChart_rawCoreNorm
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData)
    (rawNormCompatibility :
      GlobalCandidateAMinimalPhysicalReducedRawCoreNormCompatibility period
        hPeriod configuration data analysis chartData) :
    ProgramPGlobalMinimalPhysicalReducedDenseCoreHilbertClosureData4D period
      hPeriod configuration data analysis chartData :=
  globalCandidateAMinimalPhysicalReducedDenseCoreClosure_of_hilbertChart period
    hPeriod configuration data analysis chartData reducedChart (by
      intro core
      rw [reducedChart.quotient_core_compatibility core]
      exact
        (globalCandidateAMinimalPhysicalReducedCoreNormCompatibility_iff_rawCore
          period hPeriod configuration data analysis chartData).mpr
            rawNormCompatibility core)

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedDenseCoreRawNormCompatibility4D
end JanusFormal
