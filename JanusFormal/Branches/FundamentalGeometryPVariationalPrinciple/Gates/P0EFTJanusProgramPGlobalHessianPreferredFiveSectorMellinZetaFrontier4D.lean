import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSpectralFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-!
# Preferred five-sector Mellin/zeta frontier

The preferred spectral frontier supplies an explicit scalar relative heat trace
on the genuine Candidate-A kernel complement.  This file attaches exactly the
two remaining scalar analytic packets:

* finite-part renormalization of its logarithmic heat integral;
* a Gamma-normalized Mellin representation on a right half-plane together with
  differentiable continuation to zero.

The resulting complex relative zeta determinant is nonzero and its norm is the
positive finite-part determinant.  Thus the zeta function is tied to the actual
relative heat trace; an unrelated holomorphic germ cannot be substituted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMellinZetaFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 6000000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSpectralFrontier4D
open P0EFTJanusProgramPGlobalCandidateAActualKernelRelativeTrace4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
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
      (measure := measure)
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
    configuration data analysis einsteinScale hTransverse family chartBound

/-- Preferred spectral frontier plus honest finite-part/Mellin data for its
actual relative heat trace. -/
structure GlobalHessianPreferredFiveSectorMellinZetaFrontier4D
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
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  spectral : GlobalHessianPreferredFiveSectorSpectralFrontier4D period hPeriod
    configuration data analysis einsteinScale hTransverse family chartBound
      Metric Abelian Matter Longitudinal Boundary ZeroMode
  finitePart : RelativeHeatFinitePartData
    (fun time =>
      globalCandidateAActualKernelRelativeHeatTrace period hPeriod configuration
        data analysis
        (CanonicalChart period hPeriod einsteinScale hTransverse family)
        (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
        (CanonicalPhysical period hPeriod einsteinScale hTransverse family
          chartBound)
        spectral.relativeTrace time)
  continuation : RelativeHeatMellinZetaContinuationData finitePart

namespace GlobalHessianPreferredFiveSectorMellinZetaFrontier4D

/-- Complex zeta determinant generated by the actual relative heat trace. -/
def determinant
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
    (frontier : GlobalHessianPreferredFiveSectorMellinZetaFrontier4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode) : Complex :=
  relativeHeatMellinZetaDeterminant frontier.continuation

/-- Outputs through the scalar zeta determinant. -/
structure GlobalHessianPreferredFiveSectorMellinZetaFrontierOutput4D
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
    (frontier : GlobalHessianPreferredFiveSectorMellinZetaFrontier4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode) where
  spectral : GlobalHessianPreferredFiveSectorSpectralFrontierOutput4D period
    hPeriod configuration data analysis einsteinScale hTransverse family
      chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode
        frontier.spectral
  finitePart_pos : 0 < relativeHeatFinitePartDeterminant frontier.finitePart
  finitePart_log :
    Real.log (relativeHeatFinitePartDeterminant frontier.finitePart) =
      relativeHeatFinitePartLogDeterminant frontier.finitePart
  zeta_eq_mellin : ∀ spectralParameter : Complex,
    frontier.continuation.convergenceAbscissa < spectralParameter.re →
      frontier.continuation.zeta spectralParameter =
        relativeHeatMellinZetaCandidate
          (fun time =>
            globalCandidateAActualKernelRelativeHeatTrace period hPeriod
              configuration data analysis
              (CanonicalChart period hPeriod einsteinScale hTransverse family)
              (CanonicalSameAction period hPeriod einsteinScale hTransverse family)
              (CanonicalPhysical period hPeriod einsteinScale hTransverse family
                chartBound)
              frontier.spectral.relativeTrace time)
          spectralParameter
  determinant_ne_zero : frontier.determinant ≠ 0
  determinant_norm : ‖frontier.determinant‖ =
    relativeHeatFinitePartDeterminant frontier.finitePart

/-- Assemble the finite-part and Mellin/zeta outputs. -/
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
    (frontier : GlobalHessianPreferredFiveSectorMellinZetaFrontier4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode) :
    GlobalHessianPreferredFiveSectorMellinZetaFrontierOutput4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode frontier where
  spectral := frontier.spectral.close
  finitePart_pos := relativeHeatFinitePartDeterminant_pos frontier.finitePart
  finitePart_log := log_relativeHeatFinitePartDeterminant frontier.finitePart
  zeta_eq_mellin := frontier.continuation.zeta_eq_mellin
  determinant_ne_zero :=
    (relativeHeatMellinZetaDeterminant_gate frontier.continuation).1
  determinant_norm :=
    (relativeHeatMellinZetaDeterminant_gate frontier.continuation).2

/-- Public preferred Mellin/zeta checkpoint. -/
def global_hessian_preferred_five_sector_mellin_zeta_frontier_gate
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
    (frontier : GlobalHessianPreferredFiveSectorMellinZetaFrontier4D period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode) :
    GlobalHessianPreferredFiveSectorMellinZetaFrontierOutput4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode frontier :=
  frontier.close

end GlobalHessianPreferredFiveSectorMellinZetaFrontier4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorMellinZetaFrontier4D
end JanusFormal
