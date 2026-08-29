import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D

/-!
# Quadratic chart constructor for the H13 matter--LL bridge

The H13 interface previously asked directly for equality of two local Hessians
with second Frechet derivatives at every graph base point.  The graph actions
are genuine quadratic actions whose Hessians are constant, so the natural
input is stronger and simpler: identify the actual local matter and LL action
blocks with constant-plus-quadratic pullbacks along bounded linear chart
projections.

This file proves the Frechet calculus once and constructs the existing H13
same-action bridge automatically.  The remaining chart work is therefore at
the action level; no Hessian, action, field, or completion is supplied twice.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Filter MeasureTheory Set Topology
open scoped Manifold ContDiff InnerProductSpace
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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

universe u v

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

/-! ## Generic quadratic pullback calculus -/

private theorem symmetricQuadratic_hasFDerivAt
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (form : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second, form first second = form second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * form state state)
      (form point) point := by
  have hDiagonal :=
    (form.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (form point direction + form direction point) = form point direction
  rw [hSymmetric direction point]
  ring

private theorem symmetricQuadratic_fderiv
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (form : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second, form first second = form second first)
    (point : E) :
    fderiv Real (fun state => (1 / 2 : Real) * form state state) point =
      form point :=
  (symmetricQuadratic_hasFDerivAt form hSymmetric point).fderiv

private theorem symmetricQuadratic_second_fderiv
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (form : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second, form first second = form second first)
    (base : E) :
    fderiv Real
        (fun state => fderiv Real
          (fun point => (1 / 2 : Real) * form point point) state)
        base = form := by
  rw [show
      (fun state => fderiv Real
        (fun point => (1 / 2 : Real) * form point point) state) =
      fun state => form state from by
    funext state
    exact symmetricQuadratic_fderiv form hSymmetric state]
  exact ContinuousLinearMap.fderiv form

private theorem symmetricQuadraticPullback_second_fderiv
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (form : F →L[Real] F →L[Real] Real)
    (hSymmetric : ∀ first second, form first second = form second first)
    (projection : E →L[Real] F)
    (constant : Real) (base : E) :
    fderiv Real
        (actionGradient
          (fun state => constant +
            (1 / 2 : Real) * form (projection state) (projection state)))
        base =
      form.bilinearComp projection projection := by
  let pulled : E →L[Real] E →L[Real] Real :=
    form.bilinearComp projection projection
  have hPulledSymmetric :
      ∀ first second, pulled first second = pulled second first := by
    intro first second
    exact hSymmetric (projection first) (projection second)
  have hAction :
      (fun state => constant +
        (1 / 2 : Real) * form (projection state) (projection state)) =
      fun state => constant + (1 / 2 : Real) * pulled state state := by
    funext state
    rfl
  rw [hAction]
  have hFirst :
      (fun state => fderiv Real
        (fun point => constant + (1 / 2 : Real) * pulled point point) state) =
      fun state => pulled state := by
    funext state
    have hQuadratic :=
      symmetricQuadratic_hasFDerivAt pulled hPulledSymmetric state
    exact (hQuadratic.const_add constant).fderiv
  unfold actionGradient
  rw [hFirst]
  exact ContinuousLinearMap.fderiv pulled

/-! ## Action-level chart attachment -/

private def quadraticBridgeLocalBlocks
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :=
  globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain) measure

/-- Strong action-level chart data.  The local chart's actual matter and LL
blocks are globally equal to constant spectators plus pullbacks of the already
constructed quadratic graph actions. -/
structure ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D
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
  matterProjection : chart.Model →L[Real]
    ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      couplings.matterMassSquared
  llProjection : chart.Model →L[Real]
    GlobalFullLLGraphHilbert period hPeriod data analysis
  matterConstant : Real
  llConstant : Real
  matterAction_eq :
    (quadraticBridgeLocalBlocks period hPeriod chart).matter =
      fun state => matterConstant +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared (matterProjection state)
  llAction_eq :
    (quadraticBridgeLocalBlocks period hPeriod chart).ll =
      fun state => llConstant +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (llProjection state)
  matterProjection_core :
    ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      matterProjection
          (chartBridge.tangentAnalysis
            (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
              configuration data analysis core)) =
        programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
          couplings.matterMassSquared core.2.2.1
  llProjection_core :
    ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      llProjection
          (chartBridge.tangentAnalysis
            (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
              configuration data analysis core)) =
        globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
          core.2.2.2

/-- The action-level matter identity computes the local matter Hessian as the
pullback of the primitive graph form. -/
theorem quadraticChart_localMatterHessian_eq_pullback
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D
      period hPeriod configuration data analysis chart) :
    globalCandidateAH13LocalMatterHessian period hPeriod chart
        bridge.chartBridge.basePoint =
      (programPPrimitiveSpinCMatterGraphForm period hPeriod
        couplings.matterMassSquared).bilinearComp bridge.matterProjection
          bridge.matterProjection := by
  unfold globalCandidateAH13LocalMatterHessian
  change fderiv Real
      (actionGradient (quadraticBridgeLocalBlocks period hPeriod chart).matter)
      bridge.chartBridge.basePoint = _
  rw [bridge.matterAction_eq]
  exact symmetricQuadraticPullback_second_fderiv
    (programPPrimitiveSpinCMatterGraphForm period hPeriod
      couplings.matterMassSquared)
    (programPPrimitiveSpinCMatterGraphForm_comm period hPeriod
      couplings.matterMassSquared)
    bridge.matterProjection bridge.matterConstant bridge.chartBridge.basePoint

/-- The action-level LL identity computes the local LL Hessian as the pullback
of the complete three-slot LL graph form. -/
theorem quadraticChart_localLLHessian_eq_pullback
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D
      period hPeriod configuration data analysis chart) :
    globalCandidateAH13LocalLLHessian period hPeriod chart
        bridge.chartBridge.basePoint =
      globalCandidateAFullLLGraphFormPullback period hPeriod data analysis
        bridge.llProjection := by
  unfold globalCandidateAH13LocalLLHessian
  change fderiv Real
      (actionGradient (quadraticBridgeLocalBlocks period hPeriod chart).ll)
      bridge.chartBridge.basePoint = _
  rw [bridge.llAction_eq]
  simpa only [globalCandidateAFullLLGraphAction,
    globalCandidateAFullLLGraphFormPullback] using
    (@symmetricQuadraticPullback_second_fderiv
      chart.Model (GlobalFullLLGraphHilbert period hPeriod data analysis)
      inferInstance inferInstance
      (GlobalFullLLGraphHilbert period hPeriod data analysis).normedAddCommGroup
      (globalFullLLC2GraphNormedSpace period hPeriod data analysis)
      (globalCandidateAFullLLGraphForm period hPeriod data analysis)
      (globalCandidateAFullLLGraphForm_comm period hPeriod data analysis)
      bridge.llProjection bridge.llConstant bridge.chartBridge.basePoint)

/-- The quadratic chart identifies the local matter block with the completed
matter graph form on the diagonal smooth core. -/
theorem quadraticChart_localMatterHessian_eq_graph
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    diagonalExtendedBulkH13LocalMatterHessianOnCore period hPeriod
        configuration data analysis chart bridge.chartBridge first second =
      diagonalExtendedBulkH13MatterGraphHessianOnCore period hPeriod
        configuration data analysis first second := by
  unfold diagonalExtendedBulkH13LocalMatterHessianOnCore
    diagonalExtendedBulkH13MatterGraphHessianOnCore
  rw [quadraticChart_localMatterHessian_eq_pullback period hPeriod
    configuration data analysis chart bridge]
  change
    programPPrimitiveSpinCMatterGraphForm period hPeriod
      couplings.matterMassSquared
      (bridge.matterProjection
        (bridge.chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis first)))
      (bridge.matterProjection
        (bridge.chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis second))) = _
  rw [bridge.matterProjection_core first,
    bridge.matterProjection_core second]

/-- The quadratic chart likewise identifies the local LL block with the
complete LL graph form. -/
theorem quadraticChart_localLLHessian_eq_graph
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    diagonalExtendedBulkH13LocalLLHessianOnCore period hPeriod configuration
        data analysis chart bridge.chartBridge first second =
      diagonalExtendedBulkH13LLGraphHessianOnCore period hPeriod configuration
        data analysis first second := by
  unfold diagonalExtendedBulkH13LocalLLHessianOnCore
    diagonalExtendedBulkH13LLGraphHessianOnCore
  rw [quadraticChart_localLLHessian_eq_pullback period hPeriod configuration
    data analysis chart bridge]
  change
    globalCandidateAFullLLGraphForm period hPeriod data analysis
      (bridge.llProjection
        (bridge.chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis first)))
      (bridge.llProjection
        (bridge.chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis second))) = _
  rw [bridge.llProjection_core first, bridge.llProjection_core second]

/-- Canonical constructor of the original H13 same-action interface from the
two action-level quadratic chart identities. -/
def programPGlobalMinimalPhysicalLocalMatterLLSameActionBridge_of_quadraticChart
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D
      period hPeriod configuration data analysis chart) :
    ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D period hPeriod
      configuration data analysis chart where
  chartBridge := bridge.chartBridge
  matter_sameAction := by
    intro base first second
    calc
      _ = diagonalExtendedBulkH13MatterGraphHessianOnCore period hPeriod
            configuration data analysis first second :=
        quadraticChart_localMatterHessian_eq_graph period hPeriod configuration
          data analysis chart bridge first second
      _ = fderiv Real
            (fun state => fderiv Real
              (programPPrimitiveSpinCMatterGraphAction period hPeriod
                couplings.matterMassSquared) state)
            base
            (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
              couplings.matterMassSquared first.2.2.1)
            (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
              couplings.matterMassSquared second.2.2.1) :=
        diagonalExtendedBulkH13MatterGraphHessian_eq_secondFrechet period hPeriod
          configuration data analysis base first second
  ll_sameAction := by
    intro base first second
    calc
      _ = diagonalExtendedBulkH13LLGraphHessianOnCore period hPeriod
            configuration data analysis first second :=
        quadraticChart_localLLHessian_eq_graph period hPeriod configuration data
          analysis chart bridge first second
      _ = fderiv Real
            (fun state => fderiv Real
              (globalCandidateAFullLLGraphAction period hPeriod data analysis)
                state)
            base
            (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
              first.2.2.2)
            (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
              second.2.2.2) :=
        diagonalExtendedBulkH13LLGraphHessian_eq_secondFrechet period hPeriod
          configuration data analysis base first second

/-- H13 closes immediately once the actual local matter and LL blocks are
exhibited as the two quadratic pullbacks. -/
theorem global_candidateA_h13_matter_ll_same_action_gate_of_quadraticChart
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
    (bridge : ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D
      period hPeriod configuration data analysis chart) :
    GlobalCandidateAH13MatterLLSameActionCertificate period hPeriod
      configuration data analysis chart
        (programPGlobalMinimalPhysicalLocalMatterLLSameActionBridge_of_quadraticChart
          period hPeriod configuration data analysis chart bridge) :=
  global_candidateA_h13_matter_ll_same_action_gate period hPeriod configuration
    data analysis chart
      (programPGlobalMinimalPhysicalLocalMatterLLSameActionBridge_of_quadraticChart
        period hPeriod configuration data analysis chart bridge)

end
end P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
end JanusFormal
