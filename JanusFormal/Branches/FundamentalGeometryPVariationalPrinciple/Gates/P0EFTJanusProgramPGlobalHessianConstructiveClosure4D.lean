import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D

/-!
# Constructive terminal interface for HESSIAN-GLOBAL-01

The first H14 gate accepted three large aggregate contracts.  The intervening
reduction files replace them by the natural constructive inputs:

* action-level quadratic identities for the matter and LL chart blocks;
* seven separately auditable bounded physical block extensions;
* one explicit bounded parametrix modulo finite-dimensional defects.

This file packages those inputs and constructs the original H10--H14 closure
certificate.  It adds no new physical assumption at the terminal layer.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianConstructiveClosure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
open P0EFTJanusProgramPGlobalHessianClosure4D

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

local instance (priority := 30000) constructiveHessianNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod
      (P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D.globalCandidateAMetricBySector
        period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) constructiveHessianInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod
      (P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D.globalCandidateAMetricBySector
        period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The H13 same-action witness canonically extracted from action-level chart
identities. -/
def constructiveH13SameAction
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
    (quadratic :
      ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D
        period hPeriod configuration data analysis chart) :=
  programPGlobalMinimalPhysicalLocalMatterLLSameActionBridge_of_quadraticChart
    period hPeriod configuration data analysis chart quadratic

/-- The H11 seven-block extension canonically obtained by summing the seven
separate bounded extensions. -/
def constructiveH11PhysicalExtension
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
    (quadratic :
      ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D
        period hPeriod configuration data analysis chart)
    (blocks : GlobalCandidateASevenPhysicalBlockExtensions4D period hPeriod
      configuration data analysis chart
        (constructiveH13SameAction period hPeriod configuration data analysis
          chart quadratic)) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_blocks period hPeriod
    configuration data analysis chart
      (constructiveH13SameAction period hPeriod configuration data analysis
        chart quadratic) blocks

/-- Complete constructive input packet for H14.  Each later field depends on
the canonical witness constructed from the preceding fields, preventing
inconsistent duplicate choices. -/
structure GlobalCandidateAHessianConstructiveClosureInputs4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) where
  quadraticChart :
    ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D period
      hPeriod configuration data analysis chart
  physicalBlocks :
    GlobalCandidateASevenPhysicalBlockExtensions4D period hPeriod configuration
      data analysis chart
        (constructiveH13SameAction period hPeriod configuration data analysis
          chart quadraticChart)
  parametrix :
    GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D period hPeriod
      configuration data analysis chart
        (constructiveH13SameAction period hPeriod configuration data analysis
          chart quadraticChart)
        (constructiveH11PhysicalExtension period hPeriod configuration data
          analysis chart quadraticChart physicalBlocks)

/-- The H12 estimates canonically extracted from the input parametrix. -/
def GlobalCandidateAHessianConstructiveClosureInputs4D.estimates
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
    (inputs : GlobalCandidateAHessianConstructiveClosureInputs4D period hPeriod
      configuration data analysis chart) :=
  globalCandidateAFaithfulAugmentedFredholmEstimates_of_parametrix period hPeriod
    configuration data analysis chart
      (constructiveH13SameAction period hPeriod configuration data analysis
        chart inputs.quadraticChart)
      (constructiveH11PhysicalExtension period hPeriod configuration data
        analysis chart inputs.quadraticChart inputs.physicalBlocks)
      inputs.parametrix

/-- Terminal H14 certificate from the three constructive ingredients. -/
theorem global_candidateA_hessian_constructive_closure_gate
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
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (inputs : GlobalCandidateAHessianConstructiveClosureInputs4D period hPeriod
      configuration data analysis chart) :
    GlobalCandidateAHessianClosureCertificate4D period hPeriod configuration
      data analysis chart einsteinScale
        (constructiveH13SameAction period hPeriod configuration data analysis
          chart inputs.quadraticChart)
        (constructiveH11PhysicalExtension period hPeriod configuration data
          analysis chart inputs.quadraticChart inputs.physicalBlocks)
        inputs.estimates := by
  exact global_candidateA_hessian_closure_gate period hPeriod configuration data
    analysis chart einsteinScale hBoundaryTransverse
      (constructiveH13SameAction period hPeriod configuration data analysis
        chart inputs.quadraticChart)
      (constructiveH11PhysicalExtension period hPeriod configuration data
        analysis chart inputs.quadraticChart inputs.physicalBlocks)
      inputs.estimates

/-- The constructive terminal packet immediately exposes the exact typed-core
same-action pairing. -/
theorem global_candidateA_hessian_constructive_sameAction_on_typed_core
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
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (inputs : GlobalCandidateAHessianConstructiveClosureInputs4D period hPeriod
      configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    inner Real
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart
          (constructiveH13SameAction period hPeriod configuration data analysis
            chart inputs.quadraticChart)
          (constructiveH11PhysicalExtension period hPeriod configuration data
            analysis chart inputs.quadraticChart inputs.physicalBlocks)
          (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalExtendedBulkL2SmoothEmbedding
            period hPeriod
              (P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D.globalCandidateAMetricBySector
                period hPeriod data)
              couplings.matterMassSquared data analysis first))
        (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalExtendedBulkL2SmoothEmbedding
          period hPeriod
            (P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D.globalCandidateAMetricBySector
              period hPeriod data)
            couplings.matterMassSquared data analysis second) =
      P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D.diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore
        period hPeriod configuration data analysis chart
          (constructiveH13SameAction period hPeriod configuration data analysis
            chart inputs.quadraticChart).chartBridge first second :=
  GlobalCandidateAHessianClosureCertificate4D.sameAction_on_typed_core
    period hPeriod
      (global_candidateA_hessian_constructive_closure_gate period hPeriod
        configuration data analysis chart einsteinScale hBoundaryTransverse
          inputs)
      first second

/-- The same packet exposes index zero for the faithful total augmented
operator. -/
theorem global_candidateA_hessian_constructive_index_zero
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
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (inputs : GlobalCandidateAHessianConstructiveClosureInputs4D period hPeriod
      configuration data analysis chart) :
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart
        (constructiveH13SameAction period hPeriod configuration data analysis
          chart inputs.quadraticChart)
        (constructiveH11PhysicalExtension period hPeriod configuration data
          analysis chart inputs.quadraticChart inputs.physicalBlocks)).toLinearMap.index = 0 :=
  GlobalCandidateAHessianClosureCertificate4D.index_zero period hPeriod
    (global_candidateA_hessian_constructive_closure_gate period hPeriod
      configuration data analysis chart einsteinScale hBoundaryTransverse inputs)

end
end P0EFTJanusProgramPGlobalHessianConstructiveClosure4D
end JanusFormal
