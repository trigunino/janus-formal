import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D

/-!
# Preferred five-sector H14 certificate

The named-kernel closure of the preferred Candidate-A route already gives the
complete actual kernel, its five-sector multiplicities, the reduced Green
operator, closed range, Fredholmness and index zero.  The actual-kernel gap also
has two canonical quantitative consequences:

* a real resolvent on the open interval `(-gap, gap)`, with norm bound
  `(gap - |lambda|)⁻¹`;
* stability under every self-adjoint reduced perturbation of size
  `delta < gap`, with perturbed Green bound `(gap - delta)⁻¹`.

This file packages those outputs as the H14 endpoint of the one-decomposition
route.  The zero-mode space remains the genuine kernel and the named vectors
remain exact symmetries of the same augmented action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14Certificate4D

set_option autoImplicit false
set_option maxHeartbeats 11200000
set_option synthInstance.maxHeartbeats 5600000

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
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D
open P0EFTJanusProgramPGlobalCandidateACanonicalReducedPhysicalBound4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCanonicalGap4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelClosure4D.GlobalHessianPreferredFiveSectorNamedKernelClosure4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelComplementStability4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

variable {measure : Measure (EffectiveQuotient period hPeriod)}

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
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAActualKernelChart period hPeriod (measure := measure)
    configuration data analysis
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
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAActualKernelSameAction period hPeriod (measure := measure)
    configuration data
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
      (measure := measure)
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
    (measure := measure) configuration data analysis einsteinScale hTransverse
      family chartBound

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
      (measure := measure)
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
  globalCandidateAActualKernelOperator period hPeriod (measure := measure)
    configuration data analysis
    (CanonicalChart period hPeriod einsteinScale hTransverse family)
    (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
    (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)

/-- H14 output attached to one named-kernel closure. -/
structure GlobalHessianPreferredFiveSectorH14Certificate4D
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
      (measure := measure)
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
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode]
    (closure : GlobalHessianPreferredFiveSectorNamedKernelClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode) where
  named_kernel :
    GlobalHessianPreferredFiveSectorNamedKernelClosureOutput4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode closure
  resolvent : GlobalCandidateAActualKernelResolventCertificate4D period hPeriod
    configuration data analysis
      (CanonicalChart period hPeriod einsteinScale hTransverse family)
      (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
      (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)
      closure.frontier.analytic.toActualKernelGap
  stability : ∀ perturbation : GlobalCandidateAActualKernelPerturbation4D period
      hPeriod configuration data analysis
        (CanonicalChart period hPeriod einsteinScale hTransverse family)
        (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
        (CanonicalPhysical period hPeriod einsteinScale hTransverse family
          chartBound)
        closure.frontier.analytic.toActualKernelGap,
    IsSelfAdjoint
        (selfAdjointKernelComplementPerturbedOperator
          (CanonicalOperator period hPeriod einsteinScale hTransverse family
            chartBound)
          (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
            configuration data analysis
            (CanonicalChart period hPeriod einsteinScale hTransverse family)
            (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
            (CanonicalPhysical period hPeriod einsteinScale hTransverse family
              chartBound))
          perturbation.perturbation) ∧
      Function.Injective
        (selfAdjointKernelComplementPerturbedOperator
          (CanonicalOperator period hPeriod einsteinScale hTransverse family
            chartBound)
          (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
            configuration data analysis
            (CanonicalChart period hPeriod einsteinScale hTransverse family)
            (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
            (CanonicalPhysical period hPeriod einsteinScale hTransverse family
              chartBound))
          perturbation.perturbation) ∧
      Function.Surjective
        (selfAdjointKernelComplementPerturbedOperator
          (CanonicalOperator period hPeriod einsteinScale hTransverse family
            chartBound)
          (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
            configuration data analysis
            (CanonicalChart period hPeriod einsteinScale hTransverse family)
            (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
            (CanonicalPhysical period hPeriod einsteinScale hTransverse family
              chartBound))
          perturbation.perturbation) ∧
      ‖globalCandidateAActualKernelPerturbedGreen period hPeriod configuration
          data analysis
          (CanonicalChart period hPeriod einsteinScale hTransverse family)
          (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
          (CanonicalPhysical period hPeriod einsteinScale hTransverse family
            chartBound)
          closure.frontier.analytic.toActualKernelGap perturbation‖ ≤
        (closure.frontier.analytic.toActualKernelGap.gapData.gap -
          perturbation.analytic.bound)⁻¹

namespace GlobalHessianPreferredFiveSectorNamedKernelClosure4D

/-- Construct the H14 resolvent and stability package. -/
def toH14Certificate
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
      (measure := measure)
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
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (closure : GlobalHessianPreferredFiveSectorNamedKernelClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode) :
    GlobalHessianPreferredFiveSectorH14Certificate4D period hPeriod configuration
      data analysis einsteinScale hTransverse family chartBound Metric Abelian
        Matter Longitudinal Boundary ZeroMode closure where
  named_kernel := closure.close
  resolvent := globalCandidateAActualKernelResolventCertificate period hPeriod
    configuration data analysis
    (CanonicalChart period hPeriod einsteinScale hTransverse family)
    (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
    (CanonicalPhysical period hPeriod einsteinScale hTransverse family chartBound)
    closure.frontier.analytic.toActualKernelGap
  stability := by
    intro perturbation
    exact global_candidateA_actual_kernel_stability_gate period hPeriod
      configuration data analysis
      (CanonicalChart period hPeriod einsteinScale hTransverse family)
      (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
      (CanonicalPhysical period hPeriod einsteinScale hTransverse family
        chartBound)
      closure.frontier.analytic.toActualKernelGap perturbation

/-- Public preferred H14 checkpoint. -/
def global_hessian_preferred_five_sector_h14_certificate_gate
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
      (measure := measure)
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
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (closure : GlobalHessianPreferredFiveSectorNamedKernelClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode) :
    GlobalHessianPreferredFiveSectorH14Certificate4D period hPeriod configuration
      data analysis einsteinScale hTransverse family chartBound Metric Abelian
        Matter Longitudinal Boundary ZeroMode closure :=
  toH14Certificate period hPeriod closure

end GlobalHessianPreferredFiveSectorNamedKernelClosure4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14Certificate4D
end JanusFormal
