import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

/-!
# Candidate-A physical bulk graph chart

This gate takes the direct product of three already constructed analytic
blocks: the metric/de Donder plus Abelian/Lorenz chart, the primitive SpinC
matter graph, and the complete three-slot LL graph.  Their quadratic actions
give one `C∞` action with the exact block-diagonal same-action Hessian.

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

open scoped InnerProductSpace Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D
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

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance baseGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)).toNormedSpace

local instance pairingGraphAmbientNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric)).toNormedSpace

local instance pairingGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)).toNormedSpace

local instance (priority := 10000) pairingGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  (pairingGraphNormedSpace period hPeriod metric).toModule

local instance lorenzGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert
        period hPeriod metric)).toNormedSpace

local instance (priority := 10000) lorenzGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianLorenzGraphHilbert
        period hPeriod metric) :=
  (lorenzGraphNormedSpace period hPeriod metric).toModule

local instance pairedMetricGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  Prod.normedSpace

local instance (priority := 10000) pairedMetricGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (Prod.normedSpace :
    NormedSpace Real
      (GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)).toModule

local instance candidateGaugeGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric) :=
  Prod.normedSpace

local instance (priority := 10000) candidateGaugeGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric) :=
  (Prod.normedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)).toModule

local instance candidateGaugeGraphDualNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric →L[Real]
        Real) :=
  @ContinuousLinearMap.toNormedAddCommGroup
    Real Real
    (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
    Real
    inferInstance inferInstance inferInstance inferInstance
    (candidateGaugeGraphNormedSpace period hPeriod metric)
    inferInstance
    (RingHom.id Real) inferInstance

local instance candidateGaugeGraphDualNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric →L[Real]
        Real) :=
  @ContinuousLinearMap.toNormedSpace
    Real Real
    (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
    Real
    inferInstance inferInstance inferInstance inferInstance
    (candidateGaugeGraphNormedSpace period hPeriod metric)
    inferInstance
    (RingHom.id Real) inferInstance
    Real inferInstance inferInstance inferInstance

local instance fullLLGraphInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  Submodule.innerProductSpace
    (globalCandidateAFullLLGraphSubmodule period hPeriod data analysis)

local instance fullLLGraphNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (fullLLGraphInnerProductSpace period hPeriod data analysis).toNormedSpace

local instance (priority := 10000) fullLLGraphModule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (fullLLGraphNormedSpace period hPeriod data analysis).toModule

local instance fullLLGraphDualNormedAddCommGroup
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedAddCommGroup
      (GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
        Real) :=
  @ContinuousLinearMap.toNormedAddCommGroup
    Real Real
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    Real
    inferInstance inferInstance inferInstance inferInstance
    (fullLLGraphNormedSpace period hPeriod data analysis)
    inferInstance
    (RingHom.id Real) inferInstance

local instance fullLLGraphDualNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis →L[Real]
        Real) :=
  @ContinuousLinearMap.toNormedSpace
    Real Real
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    Real
    inferInstance inferInstance inferInstance inferInstance
    (fullLLGraphNormedSpace period hPeriod data analysis)
    inferInstance
    (RingHom.id Real) inferInstance
    Real inferInstance inferInstance inferInstance

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

local instance candidateBulkGraphNormedSpace
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
  Prod.normedSpace

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
  (globalCandidateAGaugeGraphHessian period hPeriod metric).bilinearComp
    (𝕜₁' := Real) (𝕜₂' := Real)
    (E' := GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    (F' := GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    (globalCandidateABulkGaugeProjection period hPeriod metric
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
  (globalCandidateAFullLLGraphForm
      period hPeriod data analysis).bilinearComp
    (𝕜₁' := Real) (𝕜₂' := Real)
    (E' := GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    (F' := GlobalCandidateABulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    (globalCandidateABulkLLProjection period hPeriod metric
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
    globalCandidateABulkGraphHessian_apply,
    globalCandidateAGaugeGraphHessian_comm,
    programPPrimitiveSpinCMatterGraphForm_comm,
    globalCandidateAFullLLGraphForm_comm]

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
  exact symmetricQuadratic_hasFDerivAt
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
  rw [show
      (fun state => fderiv Real
        (globalCandidateABulkGraphAction period hPeriod metric
          massSquared data analysis)
        state) =
      (fun state =>
        globalCandidateABulkGraphHessian period hPeriod metric
          massSquared data analysis state) from by
    funext state
    exact globalCandidateABulkGraphAction_fderiv period hPeriod metric
      massSquared data analysis state]
  exact ContinuousLinearMap.fderiv
    (globalCandidateABulkGraphHessian period hPeriod metric
      massSquared data analysis)

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
  exact contDiff_const.mul
    ((globalCandidateABulkGraphHessian period hPeriod metric
        massSquared data analysis).contDiff
      |>.clm_apply contDiff_id)

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

end
end P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
end JanusFormal
