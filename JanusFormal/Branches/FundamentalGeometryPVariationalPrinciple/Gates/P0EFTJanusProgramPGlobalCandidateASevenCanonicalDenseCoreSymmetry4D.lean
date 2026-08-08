import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenCanonicalDenseCoreBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessianSymmetry4D

/-!
# Symmetry of the canonical seven-block Candidate-A core Hessian

The six non-Robin blocks are symmetric because they are genuine second Frechet
derivatives of `C²` chart actions.  The Robin block is symmetric by the H10
same-action GHY theorem.  Their dense-core pullbacks and their finite sum are
therefore symmetric.  The single H13 core agreement transfers this result to
the physical seven-block form used by H11.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenCanonicalDenseCoreSymmetry4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 5000000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D
open P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessians4D
open P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessianSymmetry4D
open P0EFTJanusProgramPGlobalCandidateASevenCanonicalDenseCoreBound4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- Symmetry of the six non-Robin core pullbacks. -/
theorem globalCandidateACanonicalSixCoreHessian_symmetric
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
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateACanonicalSixCoreHessian period hPeriod configuration data
        analysis chart sameAction first second =
      globalCandidateACanonicalSixCoreHessian period hPeriod configuration data
        analysis chart sameAction second first := by
  exact denseCoreFiniteChartHessianPullback_symmetric
    (globalCandidateACanonicalCoreToChart period hPeriod configuration data
      analysis chart sameAction)
    (fun block : GlobalCandidateANonRobinPhysicalBlock =>
      globalCandidateALocalNonRobinBlockHessian period hPeriod chart
        sameAction.chartBridge.basePoint sameAction.chartBridge.basePoint_mem block)
    (fun block => globalCandidateALocalNonRobinBlockHessian_symmetric period
      hPeriod chart sameAction.chartBridge.basePoint
        sameAction.chartBridge.basePoint_mem block)
    first second

/-- Symmetry of the genuine H10 Robin core pullback. -/
theorem globalCandidateACanonicalRobinCoreHessian_symmetric
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
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateACanonicalRobinCoreHessian period hPeriod configuration data
        analysis chart sameAction einsteinScale family first second =
      globalCandidateACanonicalRobinCoreHessian period hPeriod configuration data
        analysis chart sameAction einsteinScale family second first := by
  exact denseCoreChartHessianPullback_symmetric
    (globalCandidateACanonicalCoreToBoundary period hPeriod configuration data
      analysis chart sameAction einsteinScale family)
    (candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
      einsteinScale data.plusGravity.metric)
    (candidateANormalBoundaryTwoSheetGHYActionHessian_symmetric period hPeriod
      einsteinScale data.plusGravity.metric hTransverse)
    first second

/-- Symmetry of the complete canonical seven-block core Hessian. -/
theorem globalCandidateACanonicalSevenCoreHessian_symmetric
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
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateACanonicalSevenCoreHessian period hPeriod configuration data
        analysis chart sameAction einsteinScale family first second =
      globalCandidateACanonicalSevenCoreHessian period hPeriod configuration data
        analysis chart sameAction einsteinScale family second first := by
  unfold globalCandidateACanonicalSevenCoreHessian
  simp only [LinearMap.add_apply]
  rw [globalCandidateACanonicalRobinCoreHessian_symmetric period hPeriod
      configuration data analysis chart sameAction einsteinScale hTransverse
        family first second,
    globalCandidateACanonicalSixCoreHessian_symmetric period hPeriod
      configuration data analysis chart sameAction first second]

/-- The H13 seven-block physical form is symmetric by exact core agreement. -/
theorem globalCandidateASevenPhysicalCoreLinearForm_symmetric_of_canonical
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
      period hPeriod configuration data analysis chart)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (agreement : GlobalCandidateASevenCanonicalDenseCoreAgreement4D period
      hPeriod configuration data analysis chart sameAction einsteinScale family)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration data
        analysis chart sameAction first second =
      globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration data
        analysis chart sameAction second first := by
  rw [agreement.core_sum_eq]
  exact globalCandidateACanonicalSevenCoreHessian_symmetric period hPeriod
    configuration data analysis chart sameAction einsteinScale hTransverse family
      first second

end
end P0EFTJanusProgramPGlobalCandidateASevenCanonicalDenseCoreSymmetry4D
end JanusFormal
