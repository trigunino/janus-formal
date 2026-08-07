import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D

/-!
# H13 matter--LL same-action closure

The corrected D10-free local Candidate-A Hessian is already split into seven
physical action blocks and the two matter--LL blocks.  The completed diagonal
graph already carries genuine quadratic actions for primitive SpinC matter and
for the full three-slot LL sector.  Their bounded graph forms are therefore
actual second Frechet derivatives, not independently supplied bilinear forms.

This gate isolates the only analytic attachment still needed from a chosen
local variational chart: its matter and LL Hessians must be the second Frechet
derivatives of those same two graph actions on the common smooth core.  From
that typed attachment the matter--LL mismatch vanishes identically, and the
true gauge-fixed covariant Hessian is exactly the completed graph Hessian plus
all seven retained physical blocks.

No physical block is cancelled, no D10 direction is restored, and no new
action, metric, normal, field, coupling or axiom is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- Select the same graph norm used by the completed LL quadratic action.
The source construction deliberately keeps this instance local. -/
local instance (priority := 30000) h13FullLLGraphNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (globalFullLLGraphInnerProductSpace period hPeriod data analysis).toNormedSpace

/-! ## Exact matter/LL split inside the local action chart -/

/-- Hessian of the primitive matter summand alone on the ambient local model. -/
noncomputable def globalCandidateAH13LocalMatterHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) :
    chart.Model →L[Real] chart.Model →L[Real] Real :=
  fderiv Real
    (actionGradient
      (globalCandidateAActionBlocks period hPeriod
        (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain)
        measure).matter) point

/-- Hessian of the complete LL summand alone on the same ambient model. -/
noncomputable def globalCandidateAH13LocalLLHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) :
    chart.Model →L[Real] chart.Model →L[Real] Real :=
  fderiv Real
    (actionGradient
      (globalCandidateAActionBlocks period hPeriod
        (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain)
        measure).ll) point

/-- The previously defined matter--LL Hessian is exactly the sum of the two
separate Hessians.  This is an identity of Frechet derivatives of the actual
local action blocks. -/
theorem globalCandidateAH13LocalMatterLLHessian_split
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) :
    globalCandidateALocalMatterLLHessian period hPeriod chart point =
      globalCandidateAH13LocalMatterHessian period hPeriod chart point +
        globalCandidateAH13LocalLLHessian period hPeriod chart point := by
  let blocks := globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain) measure
  have hC2 : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt
      (chart.blocksC2Within point hPoint) chart.isOpen_domain hPoint
  have hMatter : ContDiffAt Real 2 blocks.matter point := hC2.matter
  have hLL : ContDiffAt Real 2 blocks.ll point := hC2.ll
  have hGradient :
      actionGradient (fun state => blocks.matter state + blocks.ll state) =ᶠ[
        𝓝 point]
      fun state => actionGradient blocks.matter state +
        actionGradient blocks.ll state := by
    change
      fderiv Real (fun state => blocks.matter state + blocks.ll state) =ᶠ[
          𝓝 point]
        fun state => fderiv Real blocks.matter state +
          fderiv Real blocks.ll state
    filter_upwards [hMatter.eventually (by norm_num),
      hLL.eventually (by norm_num)] with state hMatterState hLLState
    exact fderiv_add
      (hMatterState.differentiableAt (by norm_num))
      (hLLState.differentiableAt (by norm_num))
  have hMatterGradientC1 : ContDiffAt Real 1
      (actionGradient blocks.matter) point := by
    change ContDiffAt Real 1 (fderiv Real blocks.matter) point
    exact hMatter.fderiv_right (by norm_num)
  have hLLGradientC1 : ContDiffAt Real 1
      (actionGradient blocks.ll) point := by
    change ContDiffAt Real 1 (fderiv Real blocks.ll) point
    exact hLL.fderiv_right (by norm_num)
  have hMatterGradient : DifferentiableAt Real
      (actionGradient blocks.matter) point :=
    hMatterGradientC1.differentiableAt (by norm_num)
  have hLLGradient : DifferentiableAt Real
      (actionGradient blocks.ll) point :=
    hLLGradientC1.differentiableAt (by norm_num)
  unfold globalCandidateALocalMatterLLHessian
    globalCandidateAH13LocalMatterHessian
    globalCandidateAH13LocalLLHessian
  change
    fderiv Real
        (actionGradient
          (fun state => blocks.matter state + blocks.ll state)) point =
      fderiv Real (actionGradient blocks.matter) point +
        fderiv Real (actionGradient blocks.ll) point
  rw [hGradient.fderiv_eq]
  exact fderiv_add hMatterGradient hLLGradient

/-- Pullback of the local primitive-matter Hessian to the corrected diagonal
smooth core. -/
noncomputable def diagonalExtendedBulkH13LocalMatterHessianOnCore
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateAH13LocalMatterHessian period hPeriod chart bridge.basePoint
    (bridge.tangentAnalysis
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis first))
    (bridge.tangentAnalysis
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis second))

/-- Pullback of the local full-LL Hessian to the same corrected core. -/
noncomputable def diagonalExtendedBulkH13LocalLLHessianOnCore
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateAH13LocalLLHessian period hPeriod chart bridge.basePoint
    (bridge.tangentAnalysis
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis first))
    (bridge.tangentAnalysis
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis second))

/-- The local matter--LL pullback retains its exact two-block split. -/
theorem diagonalExtendedBulkH13LocalMatterLLHessian_split
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalMatterLLHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkH13LocalMatterHessianOnCore period hPeriod
          configuration data analysis chart bridge first second +
        diagonalExtendedBulkH13LocalLLHessianOnCore period hPeriod
          configuration data analysis chart bridge first second := by
  unfold diagonalExtendedBulkMinimalPhysicalLocalMatterLLHessianOnCore
    diagonalExtendedBulkH13LocalMatterHessianOnCore
    diagonalExtendedBulkH13LocalLLHessianOnCore
  rw [globalCandidateAH13LocalMatterLLHessian_split period hPeriod chart
    bridge.basePoint bridge.basePoint_mem]
  rfl

/-! ## The two completed graph blocks are genuine same-action Hessians -/

/-- Primitive SpinC graph form on the matter coordinate of the common smooth
core. -/
def diagonalExtendedBulkH13MatterGraphHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  programPPrimitiveSpinCMatterGraphForm period hPeriod
    couplings.matterMassSquared
    (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
      couplings.matterMassSquared first.2.2.1)
    (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
      couplings.matterMassSquared second.2.2.1)

/-- Full three-slot LL graph form on the LL coordinate of the same core. -/
def diagonalExtendedBulkH13LLGraphHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateAFullLLGraphForm period hPeriod data analysis
    (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
      first.2.2.2)
    (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
      second.2.2.2)

/-- The existing combined graph block is exactly the sum of those two forms. -/
theorem diagonalExtendedBulkH13MatterLLGraphHessian_split
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMatterLLHessianOnCore period hPeriod configuration
        data analysis first second =
      diagonalExtendedBulkH13MatterGraphHessianOnCore period hPeriod
          configuration data analysis first second +
        diagonalExtendedBulkH13LLGraphHessianOnCore period hPeriod
          configuration data analysis first second :=
  rfl

/-- The matter graph block is the mixed second Frechet derivative of its own
primitive SpinC quadratic action, at every graph base point. -/
theorem diagonalExtendedBulkH13MatterGraphHessian_eq_secondFrechet
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (base : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      couplings.matterMassSquared)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkH13MatterGraphHessianOnCore period hPeriod
        configuration data analysis first second =
      fderiv Real
          (fun state => fderiv Real
            (programPPrimitiveSpinCMatterGraphAction period hPeriod
              couplings.matterMassSquared) state)
          base
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
            couplings.matterMassSquared first.2.2.1)
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
            couplings.matterMassSquared second.2.2.1) := by
  unfold diagonalExtendedBulkH13MatterGraphHessianOnCore
  rw [programPPrimitiveSpinCMatterGraphAction_second_fderiv]

/-- The LL graph block is likewise the mixed second Frechet derivative of the
complete three-slot LL graph action, at every graph base point. -/
theorem diagonalExtendedBulkH13LLGraphHessian_eq_secondFrechet
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (base : GlobalFullLLGraphHilbert period hPeriod data analysis)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkH13LLGraphHessianOnCore period hPeriod
        configuration data analysis first second =
      fderiv Real
          (fun state => fderiv Real
            (globalCandidateAFullLLGraphAction period hPeriod data analysis)
              state)
          base
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            first.2.2.2)
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            second.2.2.2) := by
  unfold diagonalExtendedBulkH13LLGraphHessianOnCore
  rw [globalCandidateAFullLLGraphAction_second_fderiv]

/-! ## Typed chart attachment and exact H13 closure -/

/-- Analytic attachment of one chosen regular local chart to the two already
constructed graph actions.  It records no new action: each right-hand side is
the second Frechet derivative of the displayed primitive matter or full LL
quadratic action. -/
structure ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
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
  chartBridge : ProgramPGlobalMinimalPhysicalLocalVariationalChartCoreBridge4D
    period hPeriod configuration.physical chart
  matter_sameAction :
    ∀ (base : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
        couplings.matterMassSquared)
      (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
        period hPeriod analysis),
      diagonalExtendedBulkH13LocalMatterHessianOnCore period hPeriod
          configuration data analysis chart chartBridge first second =
        fderiv Real
            (fun state => fderiv Real
              (programPPrimitiveSpinCMatterGraphAction period hPeriod
                couplings.matterMassSquared) state)
            base
            (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
              couplings.matterMassSquared first.2.2.1)
            (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
              couplings.matterMassSquared second.2.2.1)
  ll_sameAction :
    ∀ (base : GlobalFullLLGraphHilbert period hPeriod data analysis)
      (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
        period hPeriod analysis),
      diagonalExtendedBulkH13LocalLLHessianOnCore period hPeriod
          configuration data analysis chart chartBridge first second =
        fderiv Real
            (fun state => fderiv Real
              (globalCandidateAFullLLGraphAction period hPeriod data analysis)
                state)
            base
            (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
              first.2.2.2)
            (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
              second.2.2.2)

/-- The chart matter Hessian is the completed primitive matter graph form. -/
theorem diagonalExtendedBulkH13LocalMatterHessian_eq_graph
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
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkH13LocalMatterHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second =
      diagonalExtendedBulkH13MatterGraphHessianOnCore period hPeriod
        configuration data analysis first second := by
  let base : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      couplings.matterMassSquared := 0
  calc
    _ = fderiv Real
          (fun state => fderiv Real
            (programPPrimitiveSpinCMatterGraphAction period hPeriod
              couplings.matterMassSquared) state)
          base
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
            couplings.matterMassSquared first.2.2.1)
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
            couplings.matterMassSquared second.2.2.1) :=
      sameAction.matter_sameAction base first second
    _ = _ :=
      (diagonalExtendedBulkH13MatterGraphHessian_eq_secondFrechet period hPeriod
        configuration data analysis base first second).symm

/-- The chart LL Hessian is the completed full LL graph form. -/
theorem diagonalExtendedBulkH13LocalLLHessian_eq_graph
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
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkH13LocalLLHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second =
      diagonalExtendedBulkH13LLGraphHessianOnCore period hPeriod
        configuration data analysis first second := by
  let base : GlobalFullLLGraphHilbert period hPeriod data analysis := 0
  calc
    _ = fderiv Real
          (fun state => fderiv Real
            (globalCandidateAFullLLGraphAction period hPeriod data analysis)
              state)
          base
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            first.2.2.2)
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            second.2.2.2) :=
      sameAction.ll_sameAction base first second
    _ = _ :=
      (diagonalExtendedBulkH13LLGraphHessian_eq_secondFrechet period hPeriod
        configuration data analysis base first second).symm

/-- Exact equality of the local matter--LL Hessian and the two completed graph
blocks on the common smooth core. -/
theorem diagonalExtendedBulkH13LocalMatterLLHessian_eq_graph
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
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalMatterLLHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second =
      diagonalExtendedBulkMatterLLHessianOnCore period hPeriod configuration
        data analysis first second := by
  calc
    _ = diagonalExtendedBulkH13LocalMatterHessianOnCore period hPeriod
          configuration data analysis chart sameAction.chartBridge first second +
        diagonalExtendedBulkH13LocalLLHessianOnCore period hPeriod
          configuration data analysis chart sameAction.chartBridge first second :=
      diagonalExtendedBulkH13LocalMatterLLHessian_split period hPeriod
        configuration data analysis chart sameAction.chartBridge first second
    _ = diagonalExtendedBulkH13MatterGraphHessianOnCore period hPeriod
          configuration data analysis first second +
        diagonalExtendedBulkH13LLGraphHessianOnCore period hPeriod
          configuration data analysis first second := by
      rw [diagonalExtendedBulkH13LocalMatterHessian_eq_graph period hPeriod
          configuration data analysis chart sameAction first second,
        diagonalExtendedBulkH13LocalLLHessian_eq_graph period hPeriod
          configuration data analysis chart sameAction first second]
    _ = _ :=
      (diagonalExtendedBulkH13MatterLLGraphHessian_split period hPeriod
        configuration data analysis first second).symm

/-- The sole matter--LL residual of the corrected Hessian is identically zero. -/
theorem diagonalExtendedBulkH13MatterLLMismatch_eq_zero
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
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalMatterLLMismatchOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second = 0 := by
  unfold diagonalExtendedBulkMinimalPhysicalLocalMatterLLMismatchOnCore
  rw [diagonalExtendedBulkH13LocalMatterLLHessian_eq_graph period hPeriod
    configuration data analysis chart sameAction first second]
  exact sub_self _

/-- H13 identification with the existing augmented graph. -/
theorem diagonalExtendedBulkH13GaugeFixed_eq_augmented
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
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second =
      diagonalExtendedBulkMinimalPhysicalLocalAugmentedGraphHessianOnCore
        period hPeriod configuration data analysis chart sameAction.chartBridge
          first second := by
  exact
    (diagonalExtendedBulkMinimalPhysicalLocalGaugeFixed_eq_augmented_iff
      period hPeriod configuration data analysis chart sameAction.chartBridge
        first second).2
      (diagonalExtendedBulkH13MatterLLMismatch_eq_zero period hPeriod
        configuration data analysis chart sameAction first second)

/-- Expanded terminal form: the graph contribution is augmented by all seven
physical action blocks.  None of those blocks is discarded to force the
equality. -/
theorem diagonalExtendedBulkH13GaugeFixed_eq_graph_add_sevenPhysical
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
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second =
      diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration data
          analysis first second +
        diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
          configuration data analysis chart sameAction.chartBridge first second := by
  calc
    _ = diagonalExtendedBulkMinimalPhysicalLocalAugmentedGraphHessianOnCore
          period hPeriod configuration data analysis chart
            sameAction.chartBridge first second :=
      diagonalExtendedBulkH13GaugeFixed_eq_augmented period hPeriod
        configuration data analysis chart sameAction first second
    _ = _ := rfl

/-- Auditable terminal H13 certificate for one selected regular local chart. -/
structure GlobalCandidateAH13MatterLLSameActionCertificate
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
      period hPeriod configuration data analysis chart) : Prop where
  matter_graph_isSecondFrechet :
    ∀ base first second,
      diagonalExtendedBulkH13MatterGraphHessianOnCore period hPeriod
          configuration data analysis first second =
        fderiv Real
            (fun state => fderiv Real
              (programPPrimitiveSpinCMatterGraphAction period hPeriod
                couplings.matterMassSquared) state)
            base
            (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
              couplings.matterMassSquared first.2.2.1)
            (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
              couplings.matterMassSquared second.2.2.1)
  ll_graph_isSecondFrechet :
    ∀ base first second,
      diagonalExtendedBulkH13LLGraphHessianOnCore period hPeriod configuration
          data analysis first second =
        fderiv Real
            (fun state => fderiv Real
              (globalCandidateAFullLLGraphAction period hPeriod data analysis)
                state)
            base
            (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
              first.2.2.2)
            (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
              second.2.2.2)
  mismatch_zero :
    ∀ first second,
      diagonalExtendedBulkMinimalPhysicalLocalMatterLLMismatchOnCore period hPeriod
          configuration data analysis chart sameAction.chartBridge first second = 0
  gaugeFixed_eq_graph_add_sevenPhysical :
    ∀ first second,
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period hPeriod
          configuration data analysis chart sameAction.chartBridge first second =
        diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration data
            analysis first second +
          diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
            configuration data analysis chart sameAction.chartBridge first second

/-- Canonical H13 gate: the typed same-action chart attachment constructs the
full certificate and removes the last matter--LL comparison residual. -/
theorem global_candidateA_h13_matter_ll_same_action_gate
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
    GlobalCandidateAH13MatterLLSameActionCertificate period hPeriod
      configuration data analysis chart sameAction := by
  refine
    { matter_graph_isSecondFrechet := ?_
      ll_graph_isSecondFrechet := ?_
      mismatch_zero := ?_
      gaugeFixed_eq_graph_add_sevenPhysical := ?_ }
  · intro base first second
    exact diagonalExtendedBulkH13MatterGraphHessian_eq_secondFrechet
      period hPeriod configuration data analysis base first second
  · intro base first second
    exact diagonalExtendedBulkH13LLGraphHessian_eq_secondFrechet
      period hPeriod configuration data analysis base first second
  · intro first second
    exact diagonalExtendedBulkH13MatterLLMismatch_eq_zero period hPeriod
      configuration data analysis chart sameAction first second
  · intro first second
    exact diagonalExtendedBulkH13GaugeFixed_eq_graph_add_sevenPhysical
      period hPeriod configuration data analysis chart sameAction first second

end
end P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
end JanusFormal
