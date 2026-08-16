import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessians4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D

/-!
# The seven Candidate-A physical blocks from one dense-core chart estimate

This file removes the analytically unnatural map from the completed graph
Hilbert space back to smooth fields.  The only regularity input is the expected
estimate on the existing typed smooth core:

`||T x||_chart <= C ||i x||_graph`.

The six non-Robin Hessians are the genuine second Frechet derivatives fixed in
the canonical chart module.  Their common bound follows from continuity and a
finite sum.  The seventh block is the genuine H10 Robin Hessian; its bound is
obtained from the norm of the boundary projection composed with the same core
map.

One equality on the dense core identifies this canonical seven-block sum with
the physical form retained by H13.  H11 then extends it by density on the one
existing D10-free completion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenCanonicalDenseCoreBound4D

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 6000000

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPDenseCoreFiniteChartHessianBound4D
open P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessians4D

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

local instance (priority := 30000) denseCoreHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) denseCoreHilbertInnerProductSpace
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

local instance (priority := 30000) denseCoreHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) denseCoreHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) denseCoreHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace (CommonHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance denseCoreBoundaryNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup period hPeriod metric

local instance denseCoreBoundaryNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

/-- Existing dense embedding into the one common analytic completion. -/
def globalCandidateACanonicalCoreToHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      CommonHilbert period hPeriod configuration data analysis :=
  globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration data
    analysis

/-- Existing typed smooth-core map into the genuine local physical chart. -/
def globalCandidateACanonicalCoreToChart
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

/-- The sole regularity estimate needed to transport all local chart Hessians
to H11. -/
abbrev GlobalCandidateACanonicalDenseCoreChartBound4D
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
      period hPeriod configuration data analysis chart) :=
  DenseCoreChartMapBound
    (globalCandidateACanonicalCoreToHilbert period hPeriod configuration data
      analysis)
    (globalCandidateACanonicalCoreToChart period hPeriod configuration data
      analysis chart sameAction)

/-- Core map into the completed metric-normal chart used by the H10 Robin
Hessian. -/
def globalCandidateACanonicalCoreToBoundary
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod
          data.plusGravity.metric) Real :=
  family.boundaryProjection.toLinearMap.comp
    (globalCandidateACanonicalCoreToChart period hPeriod configuration data
      analysis chart sameAction)

/-- The core-to-boundary estimate is inherited from the chart estimate and the
operator norm of the H10 boundary projection. -/
def globalCandidateACanonicalDenseCoreBoundaryBound
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : GlobalCandidateACanonicalDenseCoreChartBound4D period hPeriod
      configuration data analysis chart sameAction) :
    DenseCoreChartMapBound
      (globalCandidateACanonicalCoreToHilbert period hPeriod configuration data
        analysis)
      (globalCandidateACanonicalCoreToBoundary period hPeriod configuration data
        analysis chart sameAction einsteinScale family) where
  constant := ‖family.boundaryProjection‖ * chartBound.constant
  constant_nonneg :=
    mul_nonneg (norm_nonneg _) chartBound.constant_nonneg
  estimate := by
    intro vector
    calc
      ‖globalCandidateACanonicalCoreToBoundary period hPeriod configuration data
          analysis chart sameAction einsteinScale family vector‖
          ≤ ‖family.boundaryProjection‖ *
              ‖globalCandidateACanonicalCoreToChart period hPeriod configuration
                data analysis chart sameAction vector‖ :=
        family.boundaryProjection.le_opNorm _
      _ ≤ ‖family.boundaryProjection‖ *
            (chartBound.constant *
              ‖globalCandidateACanonicalCoreToHilbert period hPeriod
                configuration data analysis vector‖) :=
        mul_le_mul_of_nonneg_left (chartBound.estimate vector) (norm_nonneg _)
      _ = (‖family.boundaryProjection‖ * chartBound.constant) *
            ‖globalCandidateACanonicalCoreToHilbert period hPeriod configuration
              data analysis vector‖ := by ring

/-- Six canonical non-Robin Hessians on the typed core. -/
def globalCandidateACanonicalSixCoreHessian
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
      period hPeriod configuration data analysis chart) :=
  denseCoreFiniteChartHessianPullback
    (globalCandidateACanonicalCoreToChart period hPeriod configuration data
      analysis chart sameAction)
    (fun block : GlobalCandidateANonRobinPhysicalBlock =>
      globalCandidateALocalNonRobinBlockHessian period hPeriod chart
        sameAction.chartBridge.basePoint sameAction.chartBridge.basePoint_mem block)

/-- Genuine H10 Robin Hessian on the typed core. -/
def globalCandidateACanonicalRobinCoreHessian
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  denseCoreChartHessianPullback
    (globalCandidateACanonicalCoreToBoundary period hPeriod configuration data
      analysis chart sameAction einsteinScale family)
    (candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
      einsteinScale data.plusGravity.metric)

/-- Canonical seven-block physical Hessian on the typed smooth core. -/
def globalCandidateACanonicalSevenCoreHessian
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateACanonicalRobinCoreHessian period hPeriod configuration data
      analysis chart sameAction einsteinScale family +
    globalCandidateACanonicalSixCoreHessian period hPeriod configuration data
      analysis chart sameAction

/-- Single dense-core agreement tying the canonical seven action Hessians to
the physical H13 form. -/
structure GlobalCandidateASevenCanonicalDenseCoreAgreement4D
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) : Prop where
  core_sum_eq :
    globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration data
        analysis chart sameAction =
      globalCandidateACanonicalSevenCoreHessian period hPeriod configuration data
        analysis chart sameAction einsteinScale family

/-- Canonical H11 constant for the six non-Robin blocks. -/
def globalCandidateACanonicalSixCoreConstant
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
    (chartBound : GlobalCandidateACanonicalDenseCoreChartBound4D period hPeriod
      configuration data analysis chart sameAction) : Real :=
  denseCoreFiniteChartHessianConstant chartBound.constant
    (fun block : GlobalCandidateANonRobinPhysicalBlock =>
      globalCandidateALocalNonRobinBlockHessian period hPeriod chart
        sameAction.chartBridge.basePoint sameAction.chartBridge.basePoint_mem block)

/-- Canonical H11 constant for the H10 Robin block. -/
def globalCandidateACanonicalRobinCoreConstant
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : GlobalCandidateACanonicalDenseCoreChartBound4D period hPeriod
      configuration data analysis chart sameAction) : Real :=
  let boundaryBound := globalCandidateACanonicalDenseCoreBoundaryBound period
    hPeriod configuration data analysis chart sameAction einsteinScale family
      chartBound
  ‖candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
      einsteinScale data.plusGravity.metric‖ * boundaryBound.constant ^ 2

/-- The dense-core chart estimate and one exact agreement construct the complete
seven-block H11 bound. -/
def globalCandidateASevenPhysicalCoreBound_of_canonicalDenseCore
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : GlobalCandidateACanonicalDenseCoreChartBound4D period hPeriod
      configuration data analysis chart sameAction)
    (agreement : GlobalCandidateASevenCanonicalDenseCoreAgreement4D period
      hPeriod configuration data analysis chart sameAction einsteinScale family) :
    GlobalCandidateASevenPhysicalCoreBound4D period hPeriod configuration data
      analysis chart sameAction where
  constant :=
    globalCandidateACanonicalRobinCoreConstant period hPeriod configuration data
        analysis chart sameAction einsteinScale family chartBound +
      globalCandidateACanonicalSixCoreConstant period hPeriod configuration data
        analysis chart sameAction chartBound
  constant_nonneg := by
    apply add_nonneg
    · unfold globalCandidateACanonicalRobinCoreConstant
      exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
    · exact denseCoreFiniteChartHessianConstant_nonneg chartBound.constant
        chartBound.constant_nonneg _
  estimate := by
    intro first second
    rw [agreement.core_sum_eq]
    change
      ‖globalCandidateACanonicalRobinCoreHessian period hPeriod configuration data
          analysis chart sameAction einsteinScale family first second +
        globalCandidateACanonicalSixCoreHessian period hPeriod configuration data
          analysis chart sameAction first second‖ ≤ _
    calc
      _ ≤ ‖globalCandidateACanonicalRobinCoreHessian period hPeriod configuration
              data analysis chart sameAction einsteinScale family first second‖ +
            ‖globalCandidateACanonicalSixCoreHessian period hPeriod configuration
              data analysis chart sameAction first second‖ :=
        norm_add_le _ _
      _ ≤ globalCandidateACanonicalRobinCoreConstant period hPeriod configuration
              data analysis chart sameAction einsteinScale family chartBound *
            ‖globalCandidateACanonicalCoreToHilbert period hPeriod configuration
              data analysis first‖ *
            ‖globalCandidateACanonicalCoreToHilbert period hPeriod configuration
              data analysis second‖ +
          globalCandidateACanonicalSixCoreConstant period hPeriod configuration
              data analysis chart sameAction chartBound *
            ‖globalCandidateACanonicalCoreToHilbert period hPeriod configuration
              data analysis first‖ *
            ‖globalCandidateACanonicalCoreToHilbert period hPeriod configuration
              data analysis second‖ := by
        apply add_le_add
        · exact denseCoreChartHessianPullback_bound
            (globalCandidateACanonicalCoreToHilbert period hPeriod configuration
              data analysis)
            (globalCandidateACanonicalCoreToBoundary period hPeriod configuration
              data analysis chart sameAction einsteinScale family)
            (globalCandidateACanonicalDenseCoreBoundaryBound period hPeriod
              configuration data analysis chart sameAction einsteinScale family
                chartBound)
            (candidateANormalBoundaryTwoSheetGHYActionHessian period hPeriod
              einsteinScale data.plusGravity.metric) first second
        · exact denseCoreFiniteChartHessianPullback_bound
            (globalCandidateACanonicalCoreToHilbert period hPeriod configuration
              data analysis)
            (globalCandidateACanonicalCoreToChart period hPeriod configuration
              data analysis chart sameAction)
            chartBound
            (fun block : GlobalCandidateANonRobinPhysicalBlock =>
              globalCandidateALocalNonRobinBlockHessian period hPeriod chart
                sameAction.chartBridge.basePoint
                  sameAction.chartBridge.basePoint_mem block)
            first second
      _ = (globalCandidateACanonicalRobinCoreConstant period hPeriod
              configuration data analysis chart sameAction einsteinScale family
                chartBound +
            globalCandidateACanonicalSixCoreConstant period hPeriod configuration
              data analysis chart sameAction chartBound) *
            ‖globalCandidateACanonicalCoreToHilbert period hPeriod configuration
              data analysis first‖ *
            ‖globalCandidateACanonicalCoreToHilbert period hPeriod configuration
              data analysis second‖ := by ring

/-- H11 terminal gate using only a dense-core chart estimate and one exact
seven-block agreement. -/
theorem global_candidateA_h11_canonical_denseCore_gate
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : GlobalCandidateACanonicalDenseCoreChartBound4D period hPeriod
      configuration data analysis chart sameAction)
    (agreement : GlobalCandidateASevenCanonicalDenseCoreAgreement4D period
      hPeriod configuration data analysis chart sameAction einsteinScale family) :=
  global_candidateA_h11_common_augmented_domain_gate_of_bound period hPeriod
    configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCoreBound_of_canonicalDenseCore period hPeriod
        configuration data analysis chart sameAction einsteinScale family
          chartBound agreement)

end
end P0EFTJanusProgramPGlobalCandidateASevenCanonicalDenseCoreBound4D
end JanusFormal
