import Mathlib.Analysis.Normed.Operator.Extend
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCanonicalSixPhysicalChartHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDenseCoreChartBilinearBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D

/-!
# Seven canonical H11 extensions from seven product bounds

This gate is conditional only on blockwise product estimates.  Symmetry and
reconstruction are derived from the genuine `C²` block actions.  Each canonical
block form is extended twice by density; no nonlinear completed action is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfBounds4D

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 1300000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
open P0EFTJanusProgramPCanonicalSixPhysicalChartHessian4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D

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

private abbrev PhysicalHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

local instance (priority := 30000) physicalHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

private def embedding
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      PhysicalHilbert period hPeriod configuration data analysis := by
  unfold PhysicalHilbert CommonAugmentedHilbert
  exact diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

private theorem embedding_denseRange
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    DenseRange (embedding period hPeriod configuration data analysis) := by
  unfold embedding PhysicalHilbert CommonAugmentedHilbert
  exact diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

/-- The genuine smooth-core tangent map into the local physical chart. -/
def globalCandidateASevenPhysicalCanonicalCoreToChart
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
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis →ₗ[Real]
      chart.Model :=
  sameAction.chartBridge.tangentAnalysis.comp
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis)

/-- The single graph-norm estimate which controls all seven canonical block
Hessians. -/
abbrev GlobalCandidateASevenPhysicalCanonicalCoreToChartBound4D
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
    (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
      data analysis)
    (globalCandidateASevenPhysicalCanonicalCoreToChart period hPeriod
      configuration data analysis chart sameAction)

/-- A common Hilbert chart supplies the sole core-to-chart estimate by its
operator norm. -/
def globalCandidateASevenPhysicalCanonicalCoreToChartBound_of_hilbertChart
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
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCanonicalCoreToChartBound4D period hPeriod
      configuration data analysis chart sameAction := by
  letI : NormedAddCommGroup
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis) :=
    physicalHilbertNormedAddCommGroup period hPeriod configuration data analysis
  letI : NormedSpace Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis) :=
    physicalHilbertNormedSpace period hPeriod configuration data analysis
  letI : Module Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis) :=
    physicalHilbertModule period hPeriod configuration data analysis
  let chartRealization :
      PhysicalHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model :=
    hilbertChart.toChart.toContinuousLinearMap
  exact
    { constant := ‖chartRealization‖
      constant_nonneg := norm_nonneg _
      estimate := by
        intro core
        change
          ‖sameAction.chartBridge.tangentAnalysis
              (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period
                hPeriod configuration data analysis core)‖ ≤
            ‖chartRealization‖ *
              ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
                configuration data analysis core‖
        rw [← hilbertChart.smooth_core_compatibility core]
        change
          ‖chartRealization
              (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
                (globalCandidateAMetricBySector period hPeriod data)
                couplings.matterMassSquared data analysis core)‖ ≤
            ‖chartRealization‖ *
              ‖diagonalExtendedBulkL2SmoothEmbedding period hPeriod
                (globalCandidateAMetricBySector period hPeriod data)
                couplings.matterMassSquared data analysis core‖
        exact chartRealization.le_opNorm _ }

private theorem physicalBlockAction_contDiffAt_two
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model)
    (hPoint : point ∈ chart.family.domain)
    (block : GlobalCandidateAPhysicalBlock) :
    ContDiffAt Real 2
      (globalCandidateAPhysicalBlockAction
        (globalCandidateASevenPhysicalLocalBlocks period hPeriod chart) block)
      point := by
  let blocks := globalCandidateASevenPhysicalLocalBlocks period hPeriod chart
  have hAll : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt (chart.blocksC2Within point hPoint)
      chart.isOpen_domain hPoint
  cases block with
  | candidateA =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using hAll.candidateA
  | robin =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using hAll.robin
  | einsteinHilbertPlus =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using
        hAll.einsteinHilbertPlus
  | einsteinHilbertMinus =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using
        hAll.einsteinHilbertMinus
  | maxwellPlus =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using hAll.maxwellPlus
  | maxwellMinus =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using hAll.maxwellMinus
  | finiteBV =>
      simpa [globalCandidateAPhysicalBlockAction, blocks] using hAll.finiteBV

private theorem localPhysicalHessian_eq_blockSum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model)
    (hPoint : point ∈ chart.family.domain) :
    globalCandidateALocalPhysicalHessian period hPeriod chart point =
      ∑ block : GlobalCandidateAPhysicalBlock,
        globalCandidateAPhysicalBlockLocalHessian period hPeriod chart point
          block := by
  let blocks := globalCandidateASevenPhysicalLocalBlocks period hPeriod chart
  have hC2 : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt (chart.blocksC2Within point hPoint)
      chart.isOpen_domain hPoint
  change fderiv Real (actionGradient (fullCoupledPhysicalAction blocks)) point =
    ∑ block : GlobalCandidateAPhysicalBlock,
      fderiv Real
        (actionGradient (globalCandidateAPhysicalBlockAction blocks block)) point
  rw [fullCoupledPhysicalHessian_eq_six_add_robin blocks point hC2]
  rw [show (Finset.univ : Finset GlobalCandidateAPhysicalBlock) =
      {.candidateA, .robin, .einsteinHilbertPlus, .einsteinHilbertMinus,
        .maxwellPlus, .maxwellMinus, .finiteBV} by decide]
  simp [canonicalSixPhysicalHessianSum, canonicalSixPhysicalBlockHessian,
    canonicalSixPhysicalBlockAction, globalCandidateAPhysicalBlockAction]
  abel

private theorem canonicalBlockCoreForm_symmetric
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
    (block : GlobalCandidateAPhysicalBlock)
    (first second : PhysicalCore period hPeriod analysis) :
    globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod configuration
        data analysis chart sameAction block first second =
      globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod configuration
        data analysis chart sameAction block second first := by
  have hSmooth : minSmoothness Real 2 ≤ (2 : ℕ∞ω) := by
    simp [minSmoothness_of_isRCLikeNormedField]
  have hSymmetric :=
    (physicalBlockAction_contDiffAt_two period hPeriod chart
      sameAction.chartBridge.basePoint sameAction.chartBridge.basePoint_mem
      block).isSymmSndFDerivAt hSmooth
  unfold globalCandidateAPhysicalBlockCanonicalCoreForm
    globalCandidateAPhysicalBlockLocalHessian
  exact hSymmetric _ _

private theorem canonicalBlockCoreForm_reconstruct
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
    (first second : PhysicalCore period hPeriod analysis) :
    globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration
        data analysis chart sameAction first second =
      ∑ block : GlobalCandidateAPhysicalBlock,
        globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
          configuration data analysis chart sameAction block first second := by
  rw [globalCandidateASevenPhysicalCoreLinearForm_apply]
  unfold diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
    globalCandidateAPhysicalBlockCanonicalCoreForm
  rw [localPhysicalHessian_eq_blockSum period hPeriod chart
    sameAction.chartBridge.basePoint sameAction.chartBridge.basePoint_mem]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro block _
  rfl

/-- Seven independent product bounds for the canonical block Hessians. -/
structure GlobalCandidateASevenPhysicalCanonicalCoreBounds4D
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
  constant : GlobalCandidateAPhysicalBlock → Real
  constant_nonneg : ∀ block, 0 ≤ constant block
  estimate : ∀ (block : GlobalCandidateAPhysicalBlock)
      (first second : PhysicalCore period hPeriod analysis),
    ‖globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod configuration
        data analysis chart sameAction block first second‖ ≤
      constant block * ‖embedding period hPeriod configuration data analysis first‖ *
        ‖embedding period hPeriod configuration data analysis second‖

private def canonicalCoreToChartBoundForEmbedding
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
    (bound : GlobalCandidateASevenPhysicalCanonicalCoreToChartBound4D period
      hPeriod configuration data analysis chart sameAction) :
    DenseCoreChartMapBound
      (embedding period hPeriod configuration data analysis)
      (globalCandidateASevenPhysicalCanonicalCoreToChart period hPeriod
        configuration data analysis chart sameAction) where
  constant := bound.constant
  constant_nonneg := bound.constant_nonneg
  estimate := by
    intro core
    change
      ‖globalCandidateASevenPhysicalCanonicalCoreToChart period hPeriod
          configuration data analysis chart sameAction core‖ ≤
        bound.constant *
          ‖globalCandidateASevenPhysicalCoreEmbedding period hPeriod
            configuration data analysis core‖
    exact bound.estimate core

/-- One core-to-chart estimate produces the seven required product bounds. -/
def globalCandidateASevenPhysicalCanonicalCoreBounds_of_chartBound
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
    (bound : GlobalCandidateASevenPhysicalCanonicalCoreToChartBound4D period
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCanonicalCoreBounds4D period hPeriod
      configuration data analysis chart sameAction where
  constant := fun block =>
    ‖globalCandidateAPhysicalBlockLocalHessian period hPeriod chart
      sameAction.chartBridge.basePoint block‖ * bound.constant ^ 2
  constant_nonneg := by
    intro block
    exact mul_nonneg
      (norm_nonneg (globalCandidateAPhysicalBlockLocalHessian period hPeriod
        chart sameAction.chartBridge.basePoint block))
      (sq_nonneg bound.constant)
  estimate := by
    intro block first second
    change
      ‖denseCoreChartBilinearPullback
          (globalCandidateASevenPhysicalCanonicalCoreToChart period hPeriod
            configuration data analysis chart sameAction)
          (globalCandidateAPhysicalBlockLocalHessian period hPeriod chart
            sameAction.chartBridge.basePoint block) first second‖ ≤ _
    exact denseCoreChartBilinearPullback_bound
      (embedding period hPeriod configuration data analysis)
      (globalCandidateASevenPhysicalCanonicalCoreToChart period hPeriod
        configuration data analysis chart sameAction)
      (canonicalCoreToChartBoundForEmbedding period hPeriod configuration data
        analysis chart sameAction bound)
      (globalCandidateAPhysicalBlockLocalHessian period hPeriod chart
        sameAction.chartBridge.basePoint block) first second

private def canonicalBlockCoreForm
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
    (block : GlobalCandidateAPhysicalBlock) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      PhysicalCore period hPeriod analysis →ₗ[Real] Real :=
  globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod configuration
    data analysis chart sameAction block

private def secondExtension
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
    (block : GlobalCandidateAPhysicalBlock)
    (first : PhysicalCore period hPeriod analysis) :
    PhysicalHilbert period hPeriod configuration data analysis →L[Real] Real :=
  (canonicalBlockCoreForm period hPeriod configuration data analysis chart
    sameAction block first).extendOfNorm
      (embedding period hPeriod configuration data analysis)

private theorem secondExtension_eq
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
    (bounds : GlobalCandidateASevenPhysicalCanonicalCoreBounds4D period hPeriod
      configuration data analysis chart sameAction)
    (block : GlobalCandidateAPhysicalBlock)
    (first second : PhysicalCore period hPeriod analysis) :
    secondExtension period hPeriod configuration data analysis chart sameAction
        block first (embedding period hPeriod configuration data analysis second) =
      globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod configuration
        data analysis chart sameAction block first second := by
  apply LinearMap.extendOfNorm_eq
  · exact embedding_denseRange period hPeriod configuration data analysis
  · refine ⟨bounds.constant block *
        ‖embedding period hPeriod configuration data analysis first‖, ?_⟩
    intro test
    simpa [canonicalBlockCoreForm, mul_assoc] using
      bounds.estimate block first test

private def coreToDual
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
    (bounds : GlobalCandidateASevenPhysicalCanonicalCoreBounds4D period hPeriod
      configuration data analysis chart sameAction)
    (block : GlobalCandidateAPhysicalBlock) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      (PhysicalHilbert period hPeriod configuration data analysis →L[Real] Real) where
  toFun := secondExtension period hPeriod configuration data analysis chart
    sameAction block
  map_add' first second := by
    have hFunctions :
        (fun test => secondExtension period hPeriod configuration data analysis
          chart sameAction block (first + second) test) =
          fun test => ((secondExtension period hPeriod configuration data analysis
            chart sameAction block first) +
            secondExtension period hPeriod configuration data analysis chart
              sameAction block second) test := by
      apply (embedding_denseRange period hPeriod configuration data analysis).equalizer
      · exact (secondExtension period hPeriod configuration data analysis chart
          sameAction block (first + second)).continuous
      · exact ((secondExtension period hPeriod configuration data analysis chart
          sameAction block first) +
          secondExtension period hPeriod configuration data analysis chart
            sameAction block second).continuous
      · funext test
        simp only [Function.comp_apply]
        rw [secondExtension_eq period hPeriod configuration data analysis chart
            sameAction bounds block (first + second) test,
          add_apply,
          secondExtension_eq period hPeriod configuration data analysis chart
            sameAction bounds block first test,
          secondExtension_eq period hPeriod configuration data analysis chart
            sameAction bounds block second test, map_add, LinearMap.add_apply]
    exact ContinuousLinearMap.ext (congrFun hFunctions)
  map_smul' scalar first := by
    have hFunctions :
        (fun test => secondExtension period hPeriod configuration data analysis
          chart sameAction block (scalar • first) test) =
          fun test => (scalar • secondExtension period hPeriod configuration data
            analysis chart sameAction block first) test := by
      apply (embedding_denseRange period hPeriod configuration data analysis).equalizer
      · exact (secondExtension period hPeriod configuration data analysis chart
          sameAction block (scalar • first)).continuous
      · exact (scalar • secondExtension period hPeriod configuration data analysis
          chart sameAction block first).continuous
      · funext test
        simp only [Function.comp_apply]
        rw [secondExtension_eq period hPeriod configuration data analysis chart
            sameAction bounds block (scalar • first) test,
          smul_apply,
          secondExtension_eq period hPeriod configuration data analysis chart
            sameAction bounds block first test, map_smul]
        rfl
    exact ContinuousLinearMap.ext (congrFun hFunctions)

private theorem coreToDual_bound
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
    (bounds : GlobalCandidateASevenPhysicalCanonicalCoreBounds4D period hPeriod
      configuration data analysis chart sameAction)
    (block : GlobalCandidateAPhysicalBlock)
    (first : PhysicalCore period hPeriod analysis) :
    ‖coreToDual period hPeriod configuration data analysis chart sameAction bounds
        block first‖ ≤
      bounds.constant block *
        ‖embedding period hPeriod configuration data analysis first‖ := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact embedding_denseRange period hPeriod configuration data analysis
  · exact mul_nonneg (bounds.constant_nonneg block) (norm_nonneg _)
  · intro test
    simpa [canonicalBlockCoreForm, mul_assoc] using
      bounds.estimate block first test

private def blockExtension
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
    (bounds : GlobalCandidateASevenPhysicalCanonicalCoreBounds4D period hPeriod
      configuration data analysis chart sameAction)
    (block : GlobalCandidateAPhysicalBlock) :
    PhysicalHilbert period hPeriod configuration data analysis →L[Real]
      PhysicalHilbert period hPeriod configuration data analysis →L[Real] Real :=
  (coreToDual period hPeriod configuration data analysis chart sameAction
    bounds block).extendOfNorm
      (embedding period hPeriod configuration data analysis)

private theorem blockExtension_agrees
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
    (bounds : GlobalCandidateASevenPhysicalCanonicalCoreBounds4D period hPeriod
      configuration data analysis chart sameAction)
    (block : GlobalCandidateAPhysicalBlock)
    (first second : PhysicalCore period hPeriod analysis) :
    blockExtension period hPeriod configuration data analysis chart sameAction
        bounds block (embedding period hPeriod configuration data analysis first)
        (embedding period hPeriod configuration data analysis second) =
      globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod configuration
        data analysis chart sameAction block first second := by
  unfold blockExtension
  rw [LinearMap.extendOfNorm_eq
      (embedding_denseRange period hPeriod configuration data analysis)
      ⟨bounds.constant block, fun first => coreToDual_bound period hPeriod
        configuration data analysis chart sameAction bounds block first⟩]
  exact secondExtension_eq period hPeriod configuration data analysis chart
    sameAction bounds block first second

private theorem blockExtension_symmetric
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
    (bounds : GlobalCandidateASevenPhysicalCanonicalCoreBounds4D period hPeriod
      configuration data analysis chart sameAction)
    (block : GlobalCandidateAPhysicalBlock)
    (first second : PhysicalHilbert period hPeriod configuration data analysis) :
    blockExtension period hPeriod configuration data analysis chart sameAction
        bounds block first second =
      blockExtension period hPeriod configuration data analysis chart sameAction
        bounds block second first := by
  let form := blockExtension period hPeriod configuration data analysis chart
    sameAction bounds block
  have hCore : ∀ x y : PhysicalCore period hPeriod analysis,
      form (embedding period hPeriod configuration data analysis x)
          (embedding period hPeriod configuration data analysis y) =
        globalCandidateAPhysicalBlockCanonicalCoreForm period hPeriod
          configuration data analysis chart sameAction block x y := by
    intro x y
    exact blockExtension_agrees period hPeriod configuration data analysis chart
      sameAction bounds block x y
  have hDense := embedding_denseRange period hPeriod configuration data analysis
  have hOuter : form.flip second = form second := by
    have hFunctions : (fun first => form.flip second first) =
        fun first => form second first := by
      apply hDense.equalizer
      · exact (form.flip second).continuous
      · exact (form second).continuous
      · funext core
        simp only [Function.comp_apply]
        have hInnerFunctions :
            (fun test => form
              (embedding period hPeriod configuration data analysis core) test) =
              fun test => form.flip
                (embedding period hPeriod configuration data analysis core) test := by
          apply hDense.equalizer
          · exact (form
              (embedding period hPeriod configuration data analysis core)).continuous
          · exact (form.flip
              (embedding period hPeriod configuration data analysis core)).continuous
          · funext test
            simp only [Function.comp_apply]
            rw [hCore core test, ContinuousLinearMap.flip_apply,
              hCore test core]
            exact canonicalBlockCoreForm_symmetric period hPeriod configuration
              data analysis chart sameAction block core test
        exact congrFun hInnerFunctions second
    exact ContinuousLinearMap.ext (congrFun hFunctions)
  exact congrArg (fun functional => functional first) hOuter

/-- Construct all seven completed canonical block Hessians from their product
bounds. -/
def globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_bounds
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
    (bounds : GlobalCandidateASevenPhysicalCanonicalCoreBounds4D period hPeriod
      configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D period hPeriod
      configuration data analysis chart sameAction where
  extension := blockExtension period hPeriod configuration data analysis chart
    sameAction bounds
  extension_agrees := blockExtension_agrees period hPeriod configuration data
    analysis chart sameAction bounds
  symmetric := blockExtension_symmetric period hPeriod configuration data analysis
    chart sameAction bounds
  reconstruct := canonicalBlockCoreForm_reconstruct period hPeriod configuration
    data analysis chart sameAction

/-- A single graph-norm bound on the true core-to-chart map constructs all
seven canonical completed block Hessians. -/
def globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_chartBound
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
    (bound : GlobalCandidateASevenPhysicalCanonicalCoreToChartBound4D period
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D period hPeriod
      configuration data analysis chart sameAction :=
  globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_bounds period
    hPeriod configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCanonicalCoreBounds_of_chartBound period
        hPeriod configuration data analysis chart sameAction bound)

/-- The existing common-Hilbert chart contract constructs the seven canonical
extensions without an additional H11 input. -/
def globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_hilbertChart
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
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D period hPeriod
      configuration data analysis chart sameAction :=
  globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_chartBound
    period hPeriod configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCanonicalCoreToChartBound_of_hilbertChart
        period hPeriod configuration data analysis chart sameAction hilbertChart)

/-- Gate 196: seven canonical completed H11 blocks follow from seven explicit
dense-core product bounds. -/
def candidate_a_seven_physical_canonical_extensions_of_bounds_gate
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
    (bounds : GlobalCandidateASevenPhysicalCanonicalCoreBounds4D period hPeriod
      configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D period hPeriod
      configuration data analysis chart sameAction :=
  globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_bounds period
    hPeriod configuration data analysis chart sameAction bounds

/-- Gate 196, strongest form: one core-to-chart estimate supplies all seven
canonical H11 extensions. -/
def candidate_a_seven_physical_canonical_extensions_of_chartBound_gate
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
    (bound : GlobalCandidateASevenPhysicalCanonicalCoreToChartBound4D period
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D period hPeriod
      configuration data analysis chart sameAction :=
  globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_chartBound
    period hPeriod configuration data analysis chart sameAction bound

/-- Gate 196, Hilbert-chart form: the existing norm identification directly
supplies the separated canonical H11 packet. -/
def candidate_a_seven_physical_canonical_extensions_of_hilbertChart_gate
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
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D period hPeriod
      configuration data analysis chart sameAction :=
  globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_hilbertChart
    period hPeriod configuration data analysis chart sameAction hilbertChart

end

end P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfBounds4D
end JanusFormal
