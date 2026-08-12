import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorCanonicalOperatorGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorActionSymmetryGenerators4D

/-!
# Preferred five-sector canonical-operator frontier for HESSIAN-GLOBAL-01

This file assembles the two logically independent halves of the preferred
Candidate-A Hessian route:

1. exact action symmetries generate finite sector-labelled vectors satisfying
   the actual equation `H v = 0`;
2. projected-operator estimates on the true kernel complement produce the H12
   gap, Fredholm splitting and reduced Green operator.

Both halves use the same completion-derived five-sector geometry.  The packet
therefore contains no second projection family, no D10 direction and no
Gårding hypothesis hidden inside the symmetry generators.

The only issue intentionally not collapsed here is named-kernel completeness:
proving that the displayed action generators form a basis of the genuine kernel
is a separate finite-dimensional/microlocal statement.  A subsequent closure
file can add precisely that datum without changing any analytic construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 10400000
set_option synthInstance.maxHeartbeats 5200000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCanonicalOperatorGap4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorActionSymmetryGenerators4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorActualHessianCommutation4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

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

private abbrev CanonicalChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAActualKernelChart period hPeriod configuration data analysis
    einsteinScale hTransverse family

private abbrev CanonicalSameAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAActualKernelSameAction period hPeriod configuration data
    analysis einsteinScale hTransverse family

private abbrev CanonicalPhysical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))) :=
  globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
    configuration data analysis einsteinScale hTransverse family chartBound

private abbrev CanonicalOperator
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))) :=
  globalCandidateAActualKernelOperator period hPeriod configuration data analysis
    (CanonicalChart period hPeriod einsteinScale hTransverse family)
    (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
    (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)

/-- One non-circular preferred frontier: canonical operator estimates and exact
action generators share the literal same sector geometry. -/
structure GlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family)))
    (Metric Abelian Matter Longitudinal Boundary : Type*)
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  analytic : GlobalCandidateAFiveSectorCanonicalOperatorGapData4D period hPeriod
    configuration data analysis einsteinScale hTransverse family chartBound
      Metric Abelian Matter Longitudinal Boundary
  generators : GlobalCandidateAFiveSectorActionSymmetryGenerators4D period
    hPeriod configuration data analysis
      (CanonicalChart period hPeriod einsteinScale hTransverse family)
      (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
      (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)
      Metric Abelian Matter Longitudinal Boundary analytic.geometry ZeroMode

/-- Outputs that are already constructive before identifying the named family
with the complete actual kernel. -/
structure GlobalHessianPreferredFiveSectorCanonicalOperatorFrontierOutput4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family)))
    (Metric Abelian Matter Longitudinal Boundary : Type*)
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (ZeroMode : Type*) [Fintype ZeroMode]
    (frontier : GlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode) : Prop where
  action_invariant : ∀ mode,
    ActionTranslationEventuallyInvariantAt
      (globalCandidateACommonAugmentedAction period hPeriod configuration data
        analysis
        (CanonicalChart period hPeriod einsteinScale hTransverse family)
        (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
        (CanonicalPhysical period hPeriod einsteinScale hTransverse family
          chartBound))
      0 (frontier.generators.translations.vector mode)
  generator_annihilated : ∀ mode,
    CanonicalOperator period hPeriod einsteinScale hTransverse family chartBound
      (frontier.generators.translations.vector mode) = 0
  generator_in_sector : ∀ mode,
    frontier.generators.translations.vector mode ∈
      (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        frontier.analytic.geometry.orthogonalResolution
        (frontier.generators.classification.sectorOf mode)).range
  other_sector_annihilates : ∀ mode sector,
    sector ≠ frontier.generators.classification.sectorOf mode →
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          frontier.analytic.geometry.orthogonalResolution sector
          (frontier.generators.translations.vector mode) = 0
  cross_sector_orthogonal : ∀ first second,
    frontier.generators.classification.sectorOf first ≠
        frontier.generators.classification.sectorOf second →
      inner Real (frontier.generators.translations.vector first)
        (frontier.generators.translations.vector second) = 0
  projector_commutes : ∀ sector vector,
    CanonicalOperator period hPeriod einsteinScale hTransverse family chartBound
        (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          frontier.analytic.geometry.orthogonalResolution sector vector) =
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        frontier.analytic.geometry.orthogonalResolution sector
        (CanonicalOperator period hPeriod einsteinScale hTransverse family
          chartBound vector)
  reduced_pythagoras : ∀ vector : SelfAdjointKernelComplement
      (CanonicalOperator period hPeriod einsteinScale hTransverse family
        chartBound),
    ‖vector‖ ^ 2 =
      ∑ sector : CandidateAZeroModeSector,
        ‖frontier.analytic.geometry.reducedResolution.projection sector vector‖ ^ 2
  h12_certificate : GlobalCandidateAActualKernelComplementCertificate4D period
    hPeriod configuration data analysis
      (CanonicalChart period hPeriod einsteinScale hTransverse family)
      (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
      (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)
      frontier.analytic.toActualKernelGap

namespace GlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D

/-- Assemble all non-circular symmetry and H12 outputs. -/
def close
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode]
    (frontier : GlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode) :
    GlobalHessianPreferredFiveSectorCanonicalOperatorFrontierOutput4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode frontier where
  action_invariant := frontier.generators.action_translation_invariant period
    hPeriod
  generator_annihilated := frontier.generators.vector_annihilated period hPeriod
  generator_in_sector := frontier.generators.vector_mem_sectorRange period
    hPeriod
  other_sector_annihilates :=
    frontier.generators.projection_eq_zero_of_sector_ne period hPeriod
  cross_sector_orthogonal :=
    frontier.generators.vectors_inner_eq_zero_of_sector_ne period hPeriod
  projector_commutes := frontier.analytic.geometry.commute period hPeriod
  reduced_pythagoras :=
    frontier.analytic.geometry.reducedResolution.norm_sq_decomposition
  h12_certificate := frontier.analytic.toCanonicalGap.certificate

/-- Public preferred-frontier checkpoint. -/
theorem global_hessian_preferred_five_sector_canonical_operator_frontier_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode]
    (frontier : GlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode) :
    GlobalHessianPreferredFiveSectorCanonicalOperatorFrontierOutput4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode frontier :=
  frontier.close

end GlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
end JanusFormal
