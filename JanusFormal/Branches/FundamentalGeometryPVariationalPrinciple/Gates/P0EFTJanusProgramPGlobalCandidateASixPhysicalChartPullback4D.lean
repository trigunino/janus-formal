import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCoreEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

/-!
# H11 from one bounded realization of the local physical chart

The six non-Robin action blocks are already `C²` on the genuine local
Candidate-A chart.  Their second Fréchet derivatives are therefore continuous
bilinear forms on that chart.  If the common graph Hilbert space admits one
bounded linear realization in the same chart, agreeing with the typed smooth
core, the physical Hessian extends automatically by pullback.  A bounded Robin
projection agreeing with the H10 family on that core supplies the H10 summand.

This route removes both a hand-selected aggregate form and a separately stated
product estimate.  Its analytic inputs are exactly the bounded chart
realization and the H10-compatible common-domain Robin projection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option synthInstance.maxHeartbeats 2400000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateExtension4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

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

private abbrev PhysicalCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev CommonHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

/-- Bounded realization of the completed graph domain in the genuine local
physical chart, together with the bounded Robin projection on the common
Hilbert space and its exact agreement with the H10 family on the smooth core. -/
structure GlobalCandidateACommonHilbertToLocalChart4D
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) where
  realization : CommonHilbert period hPeriod configuration data analysis →L[Real]
    chart.Model
  robinProjection :
    CommonHilbert period hPeriod configuration data analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real
  smoothCoreAgreement : ∀ core : PhysicalCore period hPeriod analysis,
    realization
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis core) =
      sameAction.chartBridge.tangentAnalysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core)
  robinSmoothCoreAgreement : ∀ core : PhysicalCore period hPeriod analysis,
    robinProjection
        (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
          data analysis core) =
      family.boundaryProjection
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis core)

/-- The local Robin Hessian on the reduced physical model. -/
def globalCandidateALocalH10RobinHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (first second : ReducedFamilyModel period hPeriod configuration) : Real :=
  candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
    einsteinScale data.plusGravity.metric
      (family.boundaryProjection first) (family.boundaryProjection second)

/-- Sum of the six local non-Robin Hessians, characterized as total physical
Hessian minus the canonical H10 Robin Hessian. -/
def globalCandidateALocalSixPhysicalHessian
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (first second : ReducedFamilyModel period hPeriod configuration) : Real :=
  globalCandidateALocalPhysicalHessian period hPeriod chart
      sameAction.chartBridge.basePoint
      (sameAction.chartBridge.tangentAnalysis first)
      (sameAction.chartBridge.tangentAnalysis second) -
    globalCandidateALocalH10RobinHessian period hPeriod configuration data
      analysis einsteinScale family first second

/-- Pull back the six local Hessians through the one bounded chart
realization. -/
def globalCandidateASixPhysicalCommonDomainForm_of_chartPullback
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis chart sameAction einsteinScale family) :=
  (globalCandidateALocalPhysicalHessian period hPeriod chart
    sameAction.chartBridge.basePoint).bilinearComp realization.realization
      realization.realization -
    globalCandidateAH10RobinCommonDomainForm period hPeriod configuration data
      analysis einsteinScale realization.robinProjection

/-- The bounded chart realization and common Robin projection construct the
complete aggregate H11 packet. -/
def globalCandidateASixPhysicalAggregateExtension_of_chartPullback
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
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis chart sameAction einsteinScale family) :
    GlobalCandidateASixPhysicalAggregateContinuousExtension4D period hPeriod
      configuration data analysis chart sameAction einsteinScale where
  robinProjection := realization.robinProjection
  robinCoreForm := globalCandidateAH10RobinCoreLinearForm period hPeriod
    configuration data analysis einsteinScale
      realization.robinProjection
  robin_core_agreement := by
    intro first second
    rfl
  nonRobinForm := globalCandidateASixPhysicalCommonDomainForm_of_chartPullback
    period hPeriod configuration data analysis chart sameAction einsteinScale
      family realization
  nonRobinCoreForm := globalCandidateASixPhysicalAggregateCoreLinearForm period
    hPeriod configuration data analysis chart sameAction einsteinScale
      realization.robinProjection
  nonRobin_core_agreement := by
    intro first second
    unfold globalCandidateASixPhysicalAggregateCoreLinearForm
      globalCandidateASixPhysicalCommonDomainForm_of_chartPullback
      globalCandidateAH10RobinCoreLinearForm
    simp only [LinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.bilinearComp_apply,
      realization.smoothCoreAgreement first,
      realization.smoothCoreAgreement second]
    rfl
  nonRobin_symmetric := by
    intro first second
    unfold globalCandidateASixPhysicalCommonDomainForm_of_chartPullback
    simp only [ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.sub_apply]
    let blocks := globalCandidateAActionBlocks period hPeriod
      (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain)
        measure
    have hC2 : FullCoupledC2At blocks sameAction.chartBridge.basePoint :=
      fullCoupledC2WithinAt_toAt
        (chart.blocksC2Within sameAction.chartBridge.basePoint
          sameAction.chartBridge.basePoint_mem)
        chart.isOpen_domain sameAction.chartBridge.basePoint_mem
    have hPhysical := action_gradient_helmholtz_at
      (fullCoupledPhysicalAction blocks) sameAction.chartBridge.basePoint
      (fullCoupledPhysicalAction_contDiffAt blocks
        sameAction.chartBridge.basePoint hC2)
      (realization.realization first) (realization.realization second)
    rw [show globalCandidateALocalPhysicalHessian period hPeriod chart
          sameAction.chartBridge.basePoint (realization.realization first)
          (realization.realization second) =
        globalCandidateALocalPhysicalHessian period hPeriod chart
          sameAction.chartBridge.basePoint (realization.realization second)
          (realization.realization first) by
        simpa only [globalCandidateALocalPhysicalHessian] using hPhysical,
      globalCandidateAH10RobinCommonDomainForm_symmetric period hPeriod
        configuration data analysis einsteinScale hTransverse
          realization.robinProjection]
  reconstruct := by
    intro first second
    unfold globalCandidateASixPhysicalAggregateCoreLinearForm
    simp only [LinearMap.sub_apply]
    ring

/-- H11 becomes a theorem of the bounded common-to-chart realization. -/
def global_candidateA_h11_gate_of_chartPullback
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
      (measure := measure)
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis chart sameAction einsteinScale family) :=
  global_candidateA_h11_common_domain_gate_of_sixAggregate period hPeriod
    configuration data analysis chart sameAction einsteinScale hTransverse
      (globalCandidateASixPhysicalAggregateExtension_of_chartPullback period
        hPeriod configuration data analysis chart sameAction einsteinScale
          hTransverse family realization)

end
end P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D
end JanusFormal
