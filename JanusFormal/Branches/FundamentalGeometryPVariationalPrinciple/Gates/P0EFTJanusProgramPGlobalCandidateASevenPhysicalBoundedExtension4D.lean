import Mathlib.Analysis.Normed.Operator.Extend
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D

/-!
# Canonical H11 extension from one dense-core bilinear bound

The seven physical blocks define a canonical algebraic bilinear form on the
existing diagonal smooth core.  A product bound with respect to the norm of
the already constructed dense embedding is enough to extend this form, first
in the second argument and then in the first, to the unique common Hilbert
completion.

This file performs both extensions with `LinearMap.extendOfNorm`.  Therefore
`GlobalCandidateASevenPhysicalCommonDomainExtension4D` is no longer a supplied
bounded form: it is constructed from one explicit analytic estimate on the
true seven-block Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
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
    NormedAddCommGroup
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) physicalHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (PhysicalHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The existing dense algebraic embedding. -/
private def physicalCoreEmbedding
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

private theorem physicalCoreEmbedding_denseRange
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    DenseRange (physicalCoreEmbedding period hPeriod configuration data analysis) := by
  unfold physicalCoreEmbedding PhysicalHilbert CommonAugmentedHilbert
  exact diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

/-- Core tangent map into the chosen local variational chart. -/
private def physicalCoreToChart
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

/-- Canonical algebraic seven-block Hessian on the diagonal smooth core. -/
def globalCandidateASevenPhysicalCoreLinearForm
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
      PhysicalCore period hPeriod analysis →ₗ[Real] Real where
  toFun first :=
    { toFun := fun second =>
        globalCandidateALocalPhysicalHessian period hPeriod chart
          sameAction.chartBridge.basePoint
          (physicalCoreToChart period hPeriod configuration data analysis chart
            sameAction first)
          (physicalCoreToChart period hPeriod configuration data analysis chart
            sameAction second)
      map_add' := by
        intro second third
        rw [map_add, map_add]
      map_smul' := by
        intro scalar second
        rw [map_smul, map_smul]
        rfl }
  map_add' first second := by
    apply LinearMap.ext
    intro test
    simp only [map_add, LinearMap.add_apply]
    rfl
  map_smul' scalar first := by
    apply LinearMap.ext
    intro test
    simp only [map_smul, LinearMap.smul_apply]
    rfl

@[simp]
theorem globalCandidateASevenPhysicalCoreLinearForm_apply
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
      diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second :=
  rfl

/-- The sole H11 analytic estimate when extending all seven physical blocks at
once. -/
structure GlobalCandidateASevenPhysicalCoreBound4D
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
  constant : Real
  constant_nonneg : 0 ≤ constant
  estimate : ∀ first second : PhysicalCore period hPeriod analysis,
    ‖globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration
        data analysis chart sameAction first second‖ ≤
      constant *
        ‖physicalCoreEmbedding period hPeriod configuration data analysis first‖ *
        ‖physicalCoreEmbedding period hPeriod configuration data analysis second‖

private def sevenPhysicalSecondExtension
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
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction)
    (first : PhysicalCore period hPeriod analysis) :
    PhysicalHilbert period hPeriod configuration data analysis →L[Real] Real :=
  (globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration data
    analysis chart sameAction first).extendOfNorm
      (physicalCoreEmbedding period hPeriod configuration data analysis)

private theorem sevenPhysicalSecondExtension_eq
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
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction)
    (first second : PhysicalCore period hPeriod analysis) :
    sevenPhysicalSecondExtension period hPeriod configuration data analysis chart
        sameAction bound first
        (physicalCoreEmbedding period hPeriod configuration data analysis
          second) =
      globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration
        data analysis chart sameAction first second := by
  apply LinearMap.extendOfNorm_eq
  · exact physicalCoreEmbedding_denseRange period hPeriod configuration data
      analysis
  · refine ⟨bound.constant *
        ‖physicalCoreEmbedding period hPeriod configuration data analysis first‖,
      ?_⟩
    intro test
    simpa [mul_assoc] using bound.estimate first test

private def sevenPhysicalCoreToDualLinearMap
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
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      (PhysicalHilbert period hPeriod configuration data analysis →L[Real]
        Real) where
  toFun := sevenPhysicalSecondExtension period hPeriod configuration data analysis
    chart sameAction bound
  map_add' first second := by
    have hFunctions :
        (fun test => sevenPhysicalSecondExtension period hPeriod configuration data
          analysis chart sameAction bound (first + second) test) =
          fun test =>
            ((sevenPhysicalSecondExtension period hPeriod configuration data
              analysis chart sameAction bound first) +
              (sevenPhysicalSecondExtension period hPeriod configuration data
                analysis chart sameAction bound second)) test := by
      apply (physicalCoreEmbedding_denseRange period hPeriod configuration data
        analysis).equalizer
      · exact
          (sevenPhysicalSecondExtension period hPeriod configuration data analysis
            chart sameAction bound (first + second)).continuous
      · exact
          ((sevenPhysicalSecondExtension period hPeriod configuration data analysis
            chart sameAction bound first) +
            (sevenPhysicalSecondExtension period hPeriod configuration data analysis
              chart sameAction bound second)).continuous
      · funext test
        simp only [Function.comp_apply]
        rw [sevenPhysicalSecondExtension_eq period hPeriod configuration data
            analysis chart sameAction bound (first + second) test,
          ContinuousLinearMap.add_apply,
          sevenPhysicalSecondExtension_eq period hPeriod configuration data
            analysis chart sameAction bound first test,
          sevenPhysicalSecondExtension_eq period hPeriod configuration data
            analysis chart sameAction bound second test,
          map_add, LinearMap.add_apply]
    exact ContinuousLinearMap.ext (congrFun hFunctions)
  map_smul' scalar first := by
    have hFunctions :
        (fun test => sevenPhysicalSecondExtension period hPeriod configuration data
          analysis chart sameAction bound (scalar • first) test) =
          fun test =>
            (scalar • sevenPhysicalSecondExtension period hPeriod configuration
              data analysis chart sameAction bound first) test := by
      apply (physicalCoreEmbedding_denseRange period hPeriod configuration data
        analysis).equalizer
      · exact
          (sevenPhysicalSecondExtension period hPeriod configuration data analysis
            chart sameAction bound (scalar • first)).continuous
      · exact
          (scalar • sevenPhysicalSecondExtension period hPeriod configuration data
            analysis chart sameAction bound first).continuous
      · funext test
        simp only [Function.comp_apply]
        rw [sevenPhysicalSecondExtension_eq period hPeriod configuration data
            analysis chart sameAction bound (scalar • first) test,
          ContinuousLinearMap.smul_apply,
          sevenPhysicalSecondExtension_eq period hPeriod configuration data
            analysis chart sameAction bound first test,
          map_smul]
        rfl
    exact ContinuousLinearMap.ext (congrFun hFunctions)

private theorem sevenPhysicalCoreToDual_bound
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
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction)
    (first : PhysicalCore period hPeriod analysis) :
    ‖sevenPhysicalCoreToDualLinearMap period hPeriod configuration data analysis
        chart sameAction bound first‖ ≤
      bound.constant *
        ‖physicalCoreEmbedding period hPeriod configuration data analysis first‖ := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact physicalCoreEmbedding_denseRange period hPeriod configuration data
      analysis
  · exact mul_nonneg bound.constant_nonneg (norm_nonneg _)
  · intro test
    simpa [mul_assoc] using bound.estimate first test

/-- Canonical bounded extension of the seven physical blocks. -/
def globalCandidateASevenPhysicalCommonDomainExtension_of_bound
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
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCommonDomainExtension4D period hPeriod
      configuration data analysis chart sameAction where
  form :=
    (sevenPhysicalCoreToDualLinearMap period hPeriod configuration data analysis
      chart sameAction bound).extendOfNorm
        (physicalCoreEmbedding period hPeriod configuration data analysis)
  symmetric := by
    intro first second
    let form :=
      (sevenPhysicalCoreToDualLinearMap period hPeriod configuration data analysis
        chart sameAction bound).extendOfNorm
          (physicalCoreEmbedding period hPeriod configuration data analysis)
    have hCore : ∀ x y : PhysicalCore period hPeriod analysis,
        form (physicalCoreEmbedding period hPeriod configuration data analysis x)
            (physicalCoreEmbedding period hPeriod configuration data analysis y) =
          globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration
            data analysis chart sameAction x y := by
      intro x y
      change ((sevenPhysicalCoreToDualLinearMap period hPeriod configuration data
          analysis chart sameAction bound).extendOfNorm
            (physicalCoreEmbedding period hPeriod configuration data analysis))
          (physicalCoreEmbedding period hPeriod configuration data analysis x)
          (physicalCoreEmbedding period hPeriod configuration data analysis y) = _
      rw [LinearMap.extendOfNorm_eq
          (physicalCoreEmbedding_denseRange period hPeriod configuration data
            analysis)
          ⟨bound.constant, fun z =>
            sevenPhysicalCoreToDual_bound period hPeriod configuration data
              analysis chart sameAction bound z⟩]
      change sevenPhysicalSecondExtension period hPeriod configuration data
          analysis chart sameAction bound x
          (physicalCoreEmbedding period hPeriod configuration data analysis y) = _
      rw [sevenPhysicalSecondExtension_eq period hPeriod configuration data
        analysis chart sameAction bound x y]
    have hDense := physicalCoreEmbedding_denseRange period hPeriod configuration
      data analysis
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
                (physicalCoreEmbedding period hPeriod configuration data analysis
                  core) test) =
                fun test => form.flip
                  (physicalCoreEmbedding period hPeriod configuration data analysis
                    core) test := by
            apply hDense.equalizer
            · exact (form (physicalCoreEmbedding period hPeriod configuration data
                analysis core)).continuous
            · exact (form.flip (physicalCoreEmbedding period hPeriod configuration
                data analysis core)).continuous
            · funext test
              simp only [Function.comp_apply]
              rw [hCore core test, ContinuousLinearMap.flip_apply,
                hCore test core]
              let blocks := globalCandidateAActionBlocks period hPeriod
                (chart.family.toActionFamily period hPeriod 0
                  chart.zero_mem_domain) measure
              have hC2 : FullCoupledC2At blocks
                  sameAction.chartBridge.basePoint :=
                fullCoupledC2WithinAt_toAt
                  (chart.blocksC2Within sameAction.chartBridge.basePoint
                    sameAction.chartBridge.basePoint_mem)
                  chart.isOpen_domain sameAction.chartBridge.basePoint_mem
              unfold globalCandidateASevenPhysicalCoreLinearForm
              unfold globalCandidateALocalPhysicalHessian
              exact action_gradient_helmholtz_at
                (fullCoupledPhysicalAction blocks)
                sameAction.chartBridge.basePoint
                (fullCoupledPhysicalAction_contDiffAt blocks
                  sameAction.chartBridge.basePoint hC2)
                (physicalCoreToChart period hPeriod configuration data analysis
                  chart sameAction core)
                (physicalCoreToChart period hPeriod configuration data analysis
                  chart sameAction test)
          exact congrFun hInnerFunctions second
      exact ContinuousLinearMap.ext (congrFun hFunctions)
    exact congrArg (fun functional => functional first) hOuter
  smooth_agreement := by
    intro first second
    change ((sevenPhysicalCoreToDualLinearMap period hPeriod configuration data
        analysis chart sameAction bound).extendOfNorm
          (physicalCoreEmbedding period hPeriod configuration data analysis))
        (physicalCoreEmbedding period hPeriod configuration data analysis first)
        (physicalCoreEmbedding period hPeriod configuration data analysis second) = _
    rw [LinearMap.extendOfNorm_eq
        (physicalCoreEmbedding_denseRange period hPeriod configuration data
          analysis)
        ⟨bound.constant, fun z =>
          sevenPhysicalCoreToDual_bound period hPeriod configuration data
            analysis chart sameAction bound z⟩]
    change sevenPhysicalSecondExtension period hPeriod configuration data analysis
        chart sameAction bound first
        (physicalCoreEmbedding period hPeriod configuration data analysis second) = _
    rw [sevenPhysicalSecondExtension_eq period hPeriod configuration data analysis
      chart sameAction bound first second]
    rfl

/-- H11 closes from the single dense-core product estimate. -/
theorem global_candidateA_h11_common_augmented_domain_gate_of_bound
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
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction) :
    GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D period hPeriod
      configuration data analysis chart sameAction
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period
          hPeriod configuration data analysis chart sameAction bound) :=
  global_candidateA_h11_common_augmented_domain_gate period hPeriod
    configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
        configuration data analysis chart sameAction bound)

end
end P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
end JanusFormal
