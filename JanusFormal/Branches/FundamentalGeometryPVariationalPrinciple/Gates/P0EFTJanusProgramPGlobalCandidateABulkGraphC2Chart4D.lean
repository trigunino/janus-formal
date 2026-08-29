import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

/-!
# Candidate-A physical bulk graph chart

This gate takes the direct product of three already constructed analytic
blocks: the metric/de Donder plus Abelian/Lorenz chart, the primitive SpinC
matter graph, and the complete three-slot LL graph.  Their quadratic actions
give one `C∞` action with the exact block-diagonal sum of their sectorwise
same-action Hessians.  This quadratic sum is not yet identified with the
pullback of the complete nonlinear covariant action.

This is a physical bulk subchart.  It does not add typed nonminimal, normal,
or general null-boundary completions and therefore does not close the total
gauge-fixed chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1600000

noncomputable section

open Set
open scoped InnerProductSpace Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D.candidateGaugeGraphNormedSpace
  P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D.candidateGaugeGraphModule
  P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D.candidateGaugeGraphDualNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D.candidateGaugeGraphDualNormedSpace
  P0EFTJanusProgramPGlobalFullLLGraphRiesz4D.globalFullLLC2GraphNormedSpace
  P0EFTJanusProgramPGlobalFullLLGraphRiesz4D.globalFullLLC2GraphModule
  P0EFTJanusProgramPGlobalFullLLGraphRiesz4D.globalFullLLC2GraphDualNormedAddCommGroup
  P0EFTJanusProgramPGlobalFullLLGraphRiesz4D.globalFullLLC2GraphDualNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

/-- Product of the closed physical gauge, primitive matter, and complete LL
graphs. -/
abbrev GlobalCandidateABulkGraphHilbert
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateAGaugeGraphHilbert period hPeriod metric ×
    (ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared ×
      GlobalFullLLGraphHilbert period hPeriod data analysis)

local instance (priority := 10000) candidateBulkGraphNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalCandidateABulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
  @Prod.normedSpace Real
    (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
    (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared ×
      GlobalFullLLGraphHilbert period hPeriod data analysis)
    inferInstance inferInstance inferInstance
    (P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D.candidateGaugeGraphNormedSpace
      period hPeriod metric)
    (@Prod.normedSpace Real
      (ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared)
      (GlobalFullLLGraphHilbert period hPeriod data analysis)
      inferInstance inferInstance inferInstance inferInstance
      (P0EFTJanusProgramPGlobalFullLLGraphRiesz4D.globalFullLLC2GraphNormedSpace
        period hPeriod data analysis))

local instance (priority := 10000) candidateBulkGraphModule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real
      (GlobalCandidateABulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
  (candidateBulkGraphNormedSpace period hPeriod metric
    massSquared data analysis).toModule

local instance candidateBulkGraphDualNormedAddCommGroup
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedAddCommGroup
      (GlobalCandidateABulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real) :=
  @ContinuousLinearMap.toNormedAddCommGroup
    Real Real
    (GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    Real
    inferInstance inferInstance inferInstance inferInstance
    (candidateBulkGraphNormedSpace period hPeriod metric
      massSquared data analysis)
    inferInstance
    (RingHom.id Real) inferInstance

local instance candidateBulkGraphDualNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalCandidateABulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real) :=
  @ContinuousLinearMap.toNormedSpace
    Real Real
    (GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    Real
    inferInstance inferInstance inferInstance inferInstance
    (candidateBulkGraphNormedSpace period hPeriod metric
      massSquared data analysis)
    inferInstance
    (RingHom.id Real) inferInstance
    Real inferInstance inferInstance inferInstance

def globalCandidateABulkGaugeProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateABulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateAGaugeGraphHilbert period hPeriod metric :=
  { toFun := Prod.fst
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_fst }

def globalCandidateABulkMatterProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateABulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared :=
  { toFun := fun state => state.2.1
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_fst.comp continuous_snd }

def globalCandidateABulkLLProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateABulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
  { toFun := fun state => state.2.2
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_snd.comp continuous_snd }

private def globalCandidateABulkGaugeForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateABulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateABulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  globalCandidateAGaugeGraphHessianPullback period hPeriod metric
    (E := GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    (domainGroup := inferInstance)
    (domainNorm := candidateBulkGraphNormedSpace period hPeriod metric
      massSquared data analysis)
    (globalCandidateABulkGaugeProjection period hPeriod metric
      massSquared data analysis)

private def globalCandidateABulkMatterForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateABulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateABulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  (programPPrimitiveSpinCMatterGraphForm
      period hPeriod massSquared).bilinearComp
    (𝕜₁' := Real) (𝕜₂' := Real)
    (E' := GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    (F' := GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    (globalCandidateABulkMatterProjection period hPeriod metric
      massSquared data analysis)
    (globalCandidateABulkMatterProjection period hPeriod metric
      massSquared data analysis)

private def globalCandidateABulkLLForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateABulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateABulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  globalCandidateAFullLLGraphFormPullback period hPeriod data analysis
    (E := GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    (domainGroup := inferInstance)
    (domainNorm := candidateBulkGraphNormedSpace period hPeriod metric
      massSquared data analysis)
    (globalCandidateABulkLLProjection period hPeriod metric
      massSquared data analysis)

/-- Exact block-diagonal Hessian on the physical bulk graph product. -/
def globalCandidateABulkGraphHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateABulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateABulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  globalCandidateABulkGaugeForm period hPeriod metric
      massSquared data analysis +
    globalCandidateABulkMatterForm period hPeriod metric
      massSquared data analysis +
    globalCandidateABulkLLForm period hPeriod metric
      massSquared data analysis

@[simp]
theorem globalCandidateABulkGraphHessian_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis) :
    globalCandidateABulkGraphHessian period hPeriod metric massSquared
        data analysis first second =
      globalCandidateAGaugeGraphHessian
          period hPeriod metric first.1 second.1 +
        programPPrimitiveSpinCMatterGraphForm
          period hPeriod massSquared first.2.1 second.2.1 +
        globalCandidateAFullLLGraphForm
          period hPeriod data analysis first.2.2 second.2.2 :=
  rfl

theorem globalCandidateABulkGraphHessian_comm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis) :
    globalCandidateABulkGraphHessian period hPeriod metric massSquared
        data analysis first second =
      globalCandidateABulkGraphHessian period hPeriod metric massSquared
        data analysis second first := by
  rw [globalCandidateABulkGraphHessian_apply,
    globalCandidateABulkGraphHessian_apply]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · exact globalCandidateAGaugeGraphHessian_comm
        period hPeriod metric first.1 second.1
    · exact programPPrimitiveSpinCMatterGraphForm_comm
        period hPeriod massSquared first.2.1 second.2.1
  · exact globalCandidateAFullLLGraphForm_comm
      period hPeriod data analysis first.2.2 second.2.2

/-- Quadratic physical bulk action. -/
def globalCandidateABulkGraphAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis) : Real :=
  (1 / 2 : Real) *
    globalCandidateABulkGraphHessian period hPeriod metric
      massSquared data analysis state state

/-- The bulk quadratic action is exactly the sum of the three already
constructed graph actions.  This does not identify it with the pullback of
the complete nonlinear covariant action. -/
theorem globalCandidateABulkGraphAction_eq_sectorActions
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis) :
    globalCandidateABulkGraphAction period hPeriod metric
        massSquared data analysis state =
      globalCandidateAGaugeGraphAction period hPeriod metric state.1 +
        programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          state.2.1 +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          state.2.2 := by
  unfold globalCandidateABulkGraphAction
    globalCandidateAGaugeGraphAction
    programPPrimitiveSpinCMatterGraphAction
    globalCandidateAFullLLGraphAction
  rw [globalCandidateABulkGraphHessian_apply]
  ring

private theorem symmetricQuadratic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second,
      bilinear first second = bilinear second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * bilinear state state)
      (bilinear point) point := by
  have hDiagonal :=
    (bilinear.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (bilinear point direction + bilinear direction point) =
    bilinear point direction
  rw [hSymmetric direction point]
  ring

private theorem symmetricQuadratic_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real) :
    ContDiff Real ⊤ (fun state => (1 / 2 : Real) * bilinear state state) :=
  contDiff_const.mul (bilinear.contDiff.clm_apply contDiff_id)

theorem globalCandidateABulkGraphAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis) :
    HasFDerivAt
      (globalCandidateABulkGraphAction period hPeriod metric
        massSquared data analysis)
      (globalCandidateABulkGraphHessian period hPeriod metric
        massSquared data analysis state)
      state := by
  exact @symmetricQuadratic_hasFDerivAt
    (GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    inferInstance
    (candidateBulkGraphNormedSpace period hPeriod metric
      massSquared data analysis)
    (globalCandidateABulkGraphHessian period hPeriod metric
      massSquared data analysis)
    (globalCandidateABulkGraphHessian_comm period hPeriod metric
      massSquared data analysis)
    state

theorem globalCandidateABulkGraphAction_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis) :
    fderiv Real
        (globalCandidateABulkGraphAction period hPeriod metric
          massSquared data analysis)
        state =
      globalCandidateABulkGraphHessian period hPeriod metric
        massSquared data analysis state :=
  (globalCandidateABulkGraphAction_hasFDerivAt
    period hPeriod metric massSquared data analysis state).fderiv

theorem globalCandidateABulkGraphAction_second_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (base : GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis) :
    fderiv Real
        (fun state => fderiv Real
          (globalCandidateABulkGraphAction period hPeriod metric
            massSquared data analysis)
          state)
        base =
      globalCandidateABulkGraphHessian period hPeriod metric
        massSquared data analysis := by
  have hLinear :
      HasFDerivAt
        (globalCandidateABulkGraphHessian period hPeriod metric
          massSquared data analysis)
        (globalCandidateABulkGraphHessian period hPeriod metric
          massSquared data analysis)
        base :=
    (globalCandidateABulkGraphHessian period hPeriod metric
      massSquared data analysis).hasFDerivAt
  have hEventually :
      (fun state => fderiv Real
        (globalCandidateABulkGraphAction period hPeriod metric
          massSquared data analysis) state) =ᶠ[𝓝 base]
      globalCandidateABulkGraphHessian period hPeriod metric
        massSquared data analysis :=
    Filter.Eventually.of_forall fun state =>
      globalCandidateABulkGraphAction_fderiv period hPeriod metric
        massSquared data analysis state
  exact (hLinear.congr_of_eventuallyEq hEventually).fderiv

theorem globalCandidateABulkGraphAction_contDiff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ContDiff Real ⊤
      (globalCandidateABulkGraphAction period hPeriod metric
        massSquared data analysis) := by
  unfold globalCandidateABulkGraphAction
  exact @symmetricQuadratic_contDiff
    (GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    inferInstance
    (candidateBulkGraphNormedSpace period hPeriod metric
      massSquared data analysis)
    (globalCandidateABulkGraphHessian period hPeriod metric
      massSquared data analysis)

theorem globalCandidateABulkGraphAction_contDiff_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ContDiff Real 2
      (globalCandidateABulkGraphAction period hPeriod metric
        massSquared data analysis) :=
  (globalCandidateABulkGraphAction_contDiff period hPeriod metric
    massSquared data analysis).of_le (by simp)

/-! ## Dense smooth core and corrected typed tangent -/

/-- Common smooth core of the gauge, finite spectral matter, and complete
smooth LL blocks. -/
abbrev GlobalCandidateABulkSmoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateAGaugeSmoothCore period hPeriod ×
    (ProgramPPrimitiveSpinCMatterFiniteCoefficients ×
      GlobalFullLLSmooth period hPeriod analysis)

/-- Real-linear insertion of the common smooth core into the physical bulk
graph. -/
def globalCandidateABulkSmoothEmbedding
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateABulkSmoothCore period hPeriod analysis →ₗ[Real]
      GlobalCandidateABulkGraphHilbert period hPeriod metric
        massSquared data analysis where
  toFun core :=
    (globalCandidateAGaugeSmoothEmbedding
        period hPeriod metric core.1,
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
          period hPeriod massSquared core.2.1,
        globalCandidateAFullLLSmoothEmbedding
          period hPeriod data analysis core.2.2))
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalCandidateAGaugeSmoothEmbedding
          period hPeriod metric).map_add first.1 second.1
    · apply Prod.ext
      · exact
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
            period hPeriod massSquared).map_add first.2.1 second.2.1
      · exact
          (globalCandidateAFullLLSmoothEmbedding
            period hPeriod data analysis).map_add first.2.2 second.2.2
  map_smul' scalar core := by
    apply Prod.ext
    · exact
        (globalCandidateAGaugeSmoothEmbedding
          period hPeriod metric).map_smul scalar core.1
    · apply Prod.ext
      · exact
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
            period hPeriod massSquared).map_smul scalar core.2.1
      · exact
          (globalCandidateAFullLLSmoothEmbedding
            period hPeriod data analysis).map_smul scalar core.2.2

theorem globalCandidateABulkSmoothEmbedding_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateABulkSmoothEmbedding period hPeriod metric
        massSquared data analysis) := by
  intro first second hEqual
  apply Prod.ext
  · apply globalCandidateAGaugeSmoothEmbedding_injective
      period hPeriod metric
    exact congrArg Prod.fst hEqual
  · apply Prod.ext
    · apply programPPrimitiveSpinCMatterGraphFiniteLinearMap_injective
        period hPeriod massSquared
      exact congrArg (fun value => value.2.1) hEqual
    · apply globalCandidateAFullLLSmoothEmbedding_injective
        period hPeriod data analysis
      exact congrArg (fun value => value.2.2) hEqual

/-- The common smooth core is genuinely dense for the product graph norm. -/
theorem globalCandidateABulkSmoothEmbedding_denseRange
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    DenseRange
      (globalCandidateABulkSmoothEmbedding period hPeriod metric
        massSquared data analysis) := by
  have hProduct :=
    (globalCandidateAGaugeSmoothEmbedding_denseRange
      period hPeriod metric).prodMap
      ((programPPrimitiveSpinCMatterGraphFiniteLinearMap_denseRange
        period hPeriod massSquared).prodMap
        (globalCandidateAFullLLSmoothEmbedding_denseRange
          period hPeriod data analysis))
  apply Dense.mono _ hProduct
  rintro _ ⟨⟨gauge, matter, ll⟩, rfl⟩
  exact ⟨(gauge, (matter, ll)), rfl⟩

/-- The gauge summand of the bulk core in the corrected typed physical
tangent. -/
def globalCandidateABulkGaugePhysicalTangentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    GlobalCandidateAGaugeSmoothCore period hPeriod →ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod configuration :=
  (globalMinimalPhysicalTangentInclusionLinearMap
      period hPeriod configuration).comp
    (globalCandidateAGaugeSmoothCoreMinimalTangentLinearMap
      period hPeriod data)

/-- The finite spectral matter summand of the bulk core in the corrected
typed physical tangent. -/
def globalCandidateABulkMatterPhysicalTangentLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod configuration :=
  (LinearMap.inr Real
      (GeneralMetricMatterFreeVariation period hPeriod)
      (ProgramPPrimitiveSpinCMatterSmoothField
        period hPeriod)).comp
    (programPPrimitiveSpinCMatterSmoothFiniteSynthesisRealLinearMap
      period hPeriod)

/-- Gauge, matter, and LL smooth directions inserted in their exact slots of
the corrected typed physical tangent. -/
def globalCandidateABulkSmoothCorePhysicalTangentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateABulkSmoothCore period hPeriod analysis →ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod configuration :=
  ((globalCandidateABulkGaugePhysicalTangentLinearMap
      period hPeriod data).comp
    (LinearMap.fst Real
      (GlobalCandidateAGaugeSmoothCore period hPeriod)
      (ProgramPPrimitiveSpinCMatterFiniteCoefficients ×
        GlobalFullLLSmooth period hPeriod analysis))) +
  ((globalCandidateABulkMatterPhysicalTangentLinearMap
      period hPeriod configuration).comp
    ((LinearMap.fst Real
      ProgramPPrimitiveSpinCMatterFiniteCoefficients
      (GlobalFullLLSmooth period hPeriod analysis)).comp
        (LinearMap.snd Real
          (GlobalCandidateAGaugeSmoothCore period hPeriod)
          (ProgramPPrimitiveSpinCMatterFiniteCoefficients ×
            GlobalFullLLSmooth period hPeriod analysis)))) +
  ((fullLLSmoothPhysicalTangentLinearMap
      period hPeriod analysis).comp
    ((LinearMap.snd Real
      ProgramPPrimitiveSpinCMatterFiniteCoefficients
      (GlobalFullLLSmooth period hPeriod analysis)).comp
        (LinearMap.snd Real
          (GlobalCandidateAGaugeSmoothCore period hPeriod)
          (ProgramPPrimitiveSpinCMatterFiniteCoefficients ×
            GlobalFullLLSmooth period hPeriod analysis))))

/-- Faithful physical specialization recording both the exact bulk graph
point and its corrected typed tangent direction. -/
def globalCandidateABulkGraphTypedCoreLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateABulkSmoothCore period hPeriod analysis →ₗ[Real]
      (GlobalCandidateABulkGraphHilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis ×
        GlobalPhysicalFieldTangent period hPeriod configuration) where
  toFun core :=
    (globalCandidateABulkSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis core,
      globalCandidateABulkSmoothCorePhysicalTangentLinearMap
        period hPeriod data analysis core)
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalCandidateABulkSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis).map_add first second
    · exact
        (globalCandidateABulkSmoothCorePhysicalTangentLinearMap
          period hPeriod data analysis).map_add first second
  map_smul' scalar core := by
    apply Prod.ext
    · exact
        (globalCandidateABulkSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis).map_smul scalar core
    · exact
        (globalCandidateABulkSmoothCorePhysicalTangentLinearMap
          period hPeriod data analysis).map_smul scalar core

theorem globalCandidateABulkGraphTypedCoreLinearMap_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateABulkGraphTypedCoreLinearMap
        period hPeriod data analysis) := by
  intro first second hEqual
  apply globalCandidateABulkSmoothEmbedding_injective
    period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
  exact congrArg Prod.fst hEqual

end
end P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
end JanusFormal
