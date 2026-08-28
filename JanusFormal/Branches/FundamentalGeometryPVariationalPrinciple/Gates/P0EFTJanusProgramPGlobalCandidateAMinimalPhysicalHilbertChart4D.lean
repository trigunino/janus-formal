import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D

/-!
# Minimal physical chart as the common H11 Hilbert chart

The local H13 chart already uses the corrected D10-free minimal physical
tangent as its model.  If that model is continuously linearly equivalent to
the unique diagonal graph `L²` completion and the equivalence agrees with the
existing diagonal smooth core, then the common-Hilbert H11 route is automatic.

This file isolates precisely that norm-identification theorem and constructs
the seven-block extension by transporting the actual local physical Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalHilbertChart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D.commonHilbertChartNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D.commonHilbertChartInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D.commonHilbertChartNormedSpace
  P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D.commonHilbertChartModule

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

private abbrev ExistingCommonHilbert
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

/-- Exact identification of the selected normed minimal tangent with the
existing H11 Hilbert completion.  Agreement on the dense diagonal core fixes
the equivalence uniquely on that core. -/
structure ProgramPGlobalMinimalPhysicalHilbertModel4D
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
      period hPeriod configuration data analysis chart) where
  toCommonHilbert : chart.Model ≃L[Real]
    ExistingCommonHilbert period hPeriod configuration data analysis
  diagonal_core :
    ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      toCommonHilbert
          (sameAction.chartBridge.tangentAnalysis
            (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
              configuration data analysis core)) =
        diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis core

/-- Construct the common-Hilbert chart adapter for the concrete minimal
physical chart. -/
def programPGlobalMinimalPhysicalCommonHilbertChart
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          (measure := measure) configuration data analysis chartData))
    (hilbert : ProgramPGlobalMinimalPhysicalHilbertModel4D period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          (measure := measure) configuration data analysis chartData)
        sameAction) :
    ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period hPeriod
      (measure := measure)
      configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          (measure := measure) configuration data analysis chartData)
        sameAction where
  toChart := hilbert.toCommonHilbert.symm
  smooth_core_compatibility := by
    intro core
    rw [← hilbert.diagonal_core core]
    exact hilbert.toCommonHilbert.symm_apply_apply _

/-- The actual seven physical blocks extend to the common domain as soon as the
minimal physical norm is identified with the existing graph Hilbert norm. -/
def globalCandidateAMinimalPhysicalSevenBlockExtension
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          (measure := measure) configuration data analysis chartData))
    (hilbert : ProgramPGlobalMinimalPhysicalHilbertModel4D period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          (measure := measure) configuration data analysis chartData)
        sameAction) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_hilbertChart period
    hPeriod (measure := measure) configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        (measure := measure) configuration data analysis chartData)
      sameAction
      (programPGlobalMinimalPhysicalCommonHilbertChart period hPeriod
        (measure := measure) configuration data analysis chartData sameAction
          hilbert)

/-- Direct H11 gate on the concrete minimal physical chart. -/
theorem global_candidateA_h11_minimalPhysical_hilbertChart_gate
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          (measure := measure) configuration data analysis chartData))
    (hilbert : ProgramPGlobalMinimalPhysicalHilbertModel4D period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          (measure := measure) configuration data analysis chartData)
        sameAction) :
    GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D period hPeriod
      configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          (measure := measure) configuration data analysis chartData)
        sameAction
        (globalCandidateAMinimalPhysicalSevenBlockExtension period hPeriod
          (measure := measure) configuration data analysis chartData sameAction
            hilbert) :=
  global_candidateA_h11_common_augmented_domain_gate period hPeriod
    (measure := measure) configuration data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        (measure := measure) configuration data analysis chartData)
      sameAction
      (globalCandidateAMinimalPhysicalSevenBlockExtension period hPeriod
        (measure := measure) configuration data analysis chartData sameAction
          hilbert)

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalHilbertChart4D
end JanusFormal
