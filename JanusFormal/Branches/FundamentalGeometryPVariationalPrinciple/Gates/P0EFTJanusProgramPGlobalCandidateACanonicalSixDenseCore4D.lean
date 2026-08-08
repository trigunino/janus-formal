import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCanonicalSixPhysicalDenseCoreBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D

/-!
# Canonical six Candidate-A chart Hessians on the dense physical core

This module specializes the generic six-block calculus to the real local
Candidate-A chart.  The six forms are fixed by `globalCandidateAActionBlocks`;
they are not supplied by the caller.

The only remaining boundary comparison is the exact equality between the H10
Robin core form and the pullback of the chart Robin Hessian. Once that equality
and the graph-norm bound of the smooth-core chart map are available, the single
H11 six-block estimate is constructed automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPCanonicalSixPhysicalChartHessian4D
open P0EFTJanusProgramPCanonicalSixPhysicalDenseCoreBound4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D
open P0EFTJanusProgramPDenseCoreChartHessianAgreement4D

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
  GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) canonicalDenseHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) canonicalDenseHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) canonicalDenseHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) canonicalDenseHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance canonicalDenseBoundaryCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance canonicalDenseBoundaryCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

/-- Actual local action blocks selected by the chosen variational chart. -/
def globalCandidateACanonicalSixLocalBlocks
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    FullCoupledActionBlocks chart.Model :=
  globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain) measure

/-- Genuine smooth-core tangent map into the local Candidate-A chart. -/
def globalCandidateACanonicalSixCoreToChart
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
      period hPeriod configuration data analysis chart) :
    PhysicalCore period hPeriod analysis →ₗ[Real] chart.Model :=
  sameAction.chartBridge.tangentAnalysis.comp
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis)

/-- Six canonical local Hessians, with no supplied bilinear form. -/
def globalCandidateACanonicalSixChartHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model)
    (block : CanonicalSixPhysicalBlock) :
    chart.Model →L[Real] chart.Model →L[Real] Real :=
  canonicalSixPhysicalBlockHessian
    (globalCandidateACanonicalSixLocalBlocks period hPeriod chart) block point

/-- Canonical six-block Hessian sum pulled back to the diagonal smooth core. -/
def globalCandidateACanonicalSixCoreSum
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
      period hPeriod configuration data analysis chart) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      PhysicalCore period hPeriod analysis →ₗ[Real] Real :=
  canonicalSixPhysicalDenseCoreSum
    (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
      analysis chart sameAction)
    (globalCandidateACanonicalSixLocalBlocks period hPeriod chart)
    sameAction.chartBridge.basePoint

/-- The local seven-block Hessian splits into the six canonical Hessians and
the actual chart Robin Hessian. -/
theorem globalCandidateALocalPhysicalHessian_eq_canonicalSix_add_robin
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
      period hPeriod configuration data analysis chart) :
    globalCandidateALocalPhysicalHessian period hPeriod chart
        sameAction.chartBridge.basePoint =
      canonicalSixPhysicalHessianSum
          (globalCandidateACanonicalSixLocalBlocks period hPeriod chart)
          sameAction.chartBridge.basePoint +
        fderiv Real
          (actionGradient
            (globalCandidateACanonicalSixLocalBlocks period hPeriod chart).robin)
          sameAction.chartBridge.basePoint := by
  let blocks := globalCandidateACanonicalSixLocalBlocks period hPeriod chart
  have hC2 : FullCoupledC2At blocks sameAction.chartBridge.basePoint :=
    fullCoupledC2WithinAt_toAt
      (chart.blocksC2Within sameAction.chartBridge.basePoint
        sameAction.chartBridge.basePoint_mem)
      chart.isOpen_domain sameAction.chartBridge.basePoint_mem
  simpa [blocks, globalCandidateALocalPhysicalHessian] using
    fullCoupledPhysicalHessian_eq_six_add_robin blocks
      sameAction.chartBridge.basePoint hC2

/-- Exact H10 agreement required on the dense core. This is the only Robin
comparison retained by the canonical six-block H11 route. -/
structure GlobalCandidateAH10RobinDenseCoreAgreement4D
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
    (einsteinScale : Real) where
  boundaryProjection :
    CommonHilbert period hPeriod configuration data analysis →L[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real
  robinCore_eq_chart :
    globalCandidateAH10RobinCoreLinearForm period hPeriod configuration data
        analysis einsteinScale boundaryProjection =
      denseCoreChartBilinearPullback
        (globalCandidateACanonicalSixCoreToChart period hPeriod configuration
          data analysis chart sameAction)
        (fderiv Real
          (actionGradient
            (globalCandidateACanonicalSixLocalBlocks period hPeriod chart).robin)
          sameAction.chartBridge.basePoint)

/-- H10 Robin agreement turns the displayed six-block remainder into the
canonical finite chart sum. -/
def globalCandidateACanonicalSixDenseCoreAgreement
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
    (robin : GlobalCandidateAH10RobinDenseCoreAgreement4D period hPeriod
      configuration data analysis chart sameAction einsteinScale) :
    CanonicalSixPhysicalDenseCoreAgreement
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis chart sameAction)
      (globalCandidateACanonicalSixLocalBlocks period hPeriod chart)
      sameAction.chartBridge.basePoint
      (globalCandidateASixPhysicalAggregateCoreLinearForm period hPeriod
        configuration data analysis chart sameAction einsteinScale
          robin.boundaryProjection) where
  target_eq := by
    ext first second
    unfold globalCandidateASixPhysicalAggregateCoreLinearForm
      globalCandidateACanonicalSixCoreSum
      canonicalSixPhysicalDenseCoreSum
    simp only [LinearMap.sub_apply,
      denseCoreFiniteChartHessianSum_apply]
    rw [globalCandidateASevenPhysicalCoreLinearForm_apply]
    unfold diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
    rw [globalCandidateALocalPhysicalHessian_eq_canonicalSix_add_robin
      period hPeriod configuration data analysis chart sameAction]
    have hRobin := congrArg
      (fun form => form first second) robin.robinCore_eq_chart
    simp only [denseCoreChartBilinearPullback_apply] at hRobin
    rw [hRobin]
    ring

/-- Canonical chart-map bound and H10 agreement construct the sole H11
six-block product estimate. -/
def globalCandidateASixPhysicalAggregateBound_of_canonicalDenseCore
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
    (robin : GlobalCandidateAH10RobinDenseCoreAgreement4D period hPeriod
      configuration data analysis chart sameAction einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis chart sameAction)) :
    GlobalCandidateASixPhysicalAggregateCoreBound4D period hPeriod
      configuration data analysis chart sameAction einsteinScale := by
  let agreement := globalCandidateACanonicalSixDenseCoreAgreement period hPeriod
    configuration data analysis chart sameAction einsteinScale robin
  let productBound := agreement.toProductBound
    (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
      data analysis)
    (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
      analysis chart sameAction)
    chartBound
    (globalCandidateACanonicalSixLocalBlocks period hPeriod chart)
    sameAction.chartBridge.basePoint
    (globalCandidateASixPhysicalAggregateCoreLinearForm period hPeriod
      configuration data analysis chart sameAction einsteinScale
        robin.boundaryProjection)
  exact
    { boundaryProjection := robin.boundaryProjection
      constant := productBound.constant
      constant_nonneg := productBound.constant_nonneg
      estimate := productBound.estimate }

/-- Direct H11 gate with no arbitrary six-block forms. -/
theorem global_candidateA_h11_gate_of_canonical_six_dense_core
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
    (robin : GlobalCandidateAH10RobinDenseCoreAgreement4D period hPeriod
      configuration data analysis chart sameAction einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis chart sameAction)) :=
  global_candidateA_h11_gate_of_sixAggregateBound period hPeriod configuration
    data analysis chart sameAction einsteinScale
      (globalCandidateASixPhysicalAggregateBound_of_canonicalDenseCore period
        hPeriod configuration data analysis chart sameAction einsteinScale
          robin chartBound)

end
end P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
end JanusFormal
