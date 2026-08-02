import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

/-!
# Candidate-A bulk with the Abelian off-shell graph

This construction replaces, rather than duplicates, the paired Lorenz factor of
the Candidate-A gauge graph.  The remaining factors are the two de Donder
metric graphs, primitive SpinC matter, and the full LL graph.  Its quadratic
action is the exact sum of these graph-sector actions; no identification with
the pullback Hessian of the complete nonlinear Candidate-A action is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1600000

noncomputable section

open Set
open scoped InnerProductSpace Topology ContDiff
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance extendedBulkCanonicalLorentzVolumeFinite :
    MeasureTheory.IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.canonicalLorentzVolumeFinite
    period hPeriod

local instance (priority := 10001) extendedBulkPairedMetricNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedGeneralMetricDeDonderGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D.pairedMetricGraphNormedSpace
    period hPeriod metric

local instance (priority := 10001) extendedBulkPairedMetricModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedGeneralMetricDeDonderGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D.pairedMetricGraphModule
    period hPeriod metric

local instance (priority := 10001) extendedBulkOffShellNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod metric

local instance (priority := 10001) extendedBulkOffShellModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphModule
    period hPeriod metric

local instance (priority := 10001) extendedBulkLLNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  P0EFTJanusProgramPGlobalFullLLGraphRiesz4D.globalFullLLC2GraphNormedSpace
    period hPeriod data analysis

local instance (priority := 10001) extendedBulkLLModule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  P0EFTJanusProgramPGlobalFullLLGraphRiesz4D.globalFullLLC2GraphModule
    period hPeriod data analysis

/-- The Lorenz factor is absent: its potential and Lorenz feature occur only
inside the off-shell BRST graph. -/
abbrev GlobalCandidateAAbelianExtendedBulkGraphHilbert
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalPairedGeneralMetricDeDonderGraphHilbert period hPeriod metric ×
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric ×
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared ×
        GlobalFullLLGraphHilbert period hPeriod data analysis))

local instance (priority := 10002) extendedBulkNormedSpace
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
      (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
  Prod.normedSpace

local instance (priority := 10003) extendedBulkModule
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
      (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
  (extendedBulkNormedSpace period hPeriod metric massSquared data analysis).toModule

local instance (priority := 10004) extendedBulkIsBoundedSMul
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsBoundedSMul Real
      (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
  @NormedSpace.toIsBoundedSMul Real
    (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    inferInstance inferInstance
    (extendedBulkNormedSpace period hPeriod metric massSquared data analysis)

/-- Intrinsic smooth core for the four independent factors. -/
abbrev GlobalCandidateAAbelianExtendedBulkSmoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalMetricPerturbationPair period hPeriod ×
    (GlobalPairedAbelianBRSTState period hPeriod ×
      (ProgramPPrimitiveSpinCMatterFiniteCoefficients ×
        GlobalFullLLSmooth period hPeriod analysis))

/-- Componentwise smooth-core insertion. -/
def extendedBulkSmoothEmbedding
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkSmoothCore period hPeriod analysis →ₗ[Real]
      GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis where
  toFun core :=
    (globalPairedGeneralMetricDeDonderSmoothEmbedding
        period hPeriod metric core.1,
      (globalPairedAbelianOffShellSmoothEmbedding
          period hPeriod metric core.2.1,
        (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
            period hPeriod massSquared core.2.2.1,
          globalCandidateAFullLLSmoothEmbedding
            period hPeriod data analysis core.2.2.2)))
  map_add' first second := by
    apply Prod.ext
    · exact (globalPairedGeneralMetricDeDonderSmoothEmbedding
        period hPeriod metric).map_add first.1 second.1
    · apply Prod.ext
      · exact (globalPairedAbelianOffShellSmoothEmbedding
          period hPeriod metric).map_add first.2.1 second.2.1
      · apply Prod.ext
        · exact (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
            period hPeriod massSquared).map_add first.2.2.1 second.2.2.1
        · exact (globalCandidateAFullLLSmoothEmbedding
            period hPeriod data analysis).map_add first.2.2.2 second.2.2.2
  map_smul' scalar core := by
    apply Prod.ext
    · exact (globalPairedGeneralMetricDeDonderSmoothEmbedding
        period hPeriod metric).map_smul scalar core.1
    · apply Prod.ext
      · exact (globalPairedAbelianOffShellSmoothEmbedding
          period hPeriod metric).map_smul scalar core.2.1
      · apply Prod.ext
        · exact (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
            period hPeriod massSquared).map_smul scalar core.2.2.1
        · exact (globalCandidateAFullLLSmoothEmbedding
            period hPeriod data analysis).map_smul scalar core.2.2.2

theorem extendedBulkSmoothEmbedding_injective
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
      (extendedBulkSmoothEmbedding period hPeriod metric massSquared data analysis) := by
  intro first second hEqual
  apply Prod.ext
  · apply globalPairedGeneralMetricDeDonderSmoothEmbedding_injective
      period hPeriod metric
    exact congrArg Prod.fst hEqual
  · apply Prod.ext
    · apply globalPairedAbelianOffShellSmoothEmbedding_injective
        period hPeriod metric
      exact congrArg (fun value => value.2.1) hEqual
    · apply Prod.ext
      · apply programPPrimitiveSpinCMatterGraphFiniteLinearMap_injective
          period hPeriod massSquared
        exact congrArg (fun value => value.2.2.1) hEqual
      · apply globalCandidateAFullLLSmoothEmbedding_injective
          period hPeriod data analysis
        exact congrArg (fun value => value.2.2.2) hEqual

theorem extendedBulkSmoothEmbedding_denseRange
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
      (extendedBulkSmoothEmbedding period hPeriod metric massSquared data analysis) := by
  have hProduct :=
    (globalPairedGeneralMetricDeDonderSmoothEmbedding_denseRange
      period hPeriod metric).prodMap
      ((globalPairedAbelianOffShellSmoothEmbedding_denseRange
        period hPeriod metric).prodMap
        ((programPPrimitiveSpinCMatterGraphFiniteLinearMap_denseRange
          period hPeriod massSquared).prodMap
          (globalCandidateAFullLLSmoothEmbedding_denseRange
            period hPeriod data analysis)))
  apply Dense.mono _ hProduct
  rintro _ ⟨⟨metricCore, offShellCore, matterCore, llCore⟩, rfl⟩
  exact ⟨(metricCore, (offShellCore, (matterCore, llCore))), rfl⟩

/-! ## Exact block form (with no separate Lorenz summand) -/

local instance extendedBulkDualNormedAddCommGroup
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
      (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real) :=
  @ContinuousLinearMap.toNormedAddCommGroup
    Real Real
    (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    Real inferInstance inferInstance inferInstance inferInstance
    (extendedBulkNormedSpace period hPeriod metric massSquared data analysis)
    inferInstance (RingHom.id Real) inferInstance

local instance extendedBulkDualNormedSpace
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
      (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real) :=
  @ContinuousLinearMap.toNormedSpace
    Real Real
    (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    Real inferInstance inferInstance inferInstance inferInstance
    (extendedBulkNormedSpace period hPeriod metric massSquared data analysis)
    inferInstance (RingHom.id Real) inferInstance
    Real inferInstance inferInstance inferInstance

def metricProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalPairedGeneralMetricDeDonderGraphHilbert period hPeriod metric :=
  { toFun := Prod.fst
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_fst }

def offShellProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  { toFun := fun state => state.2.1
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_fst.comp continuous_snd }

def matterProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared :=
  { toFun := fun state => state.2.2.1
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_fst.comp (continuous_snd.comp continuous_snd) }

def llProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalFullLLGraphHilbert period hPeriod data analysis :=
  { toFun := fun state => state.2.2.2
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_snd.comp (continuous_snd.comp continuous_snd) }

private def pullbackRealBilinear
    {E D : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup D]
    (sourceNorm : NormedSpace Real E)
    (domainNorm : NormedSpace Real D)
    (form : E →L[Real] E →L[Real] Real)
    (projection : D →L[Real] E) :
    D →L[Real] D →L[Real] Real :=
  @ContinuousLinearMap.bilinearComp
    Real Real Real E E Real
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    sourceNorm sourceNorm inferInstance
    (RingHom.id Real) (RingHom.id Real)
    D D inferInstance inferInstance
    Real Real inferInstance inferInstance
    domainNorm domainNorm
    (RingHom.id Real) (RingHom.id Real) (RingHom.id Real) (RingHom.id Real)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    form projection projection

private def metricPullbackForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  pullbackRealBilinear
    (extendedBulkPairedMetricNormedSpace period hPeriod metric)
    (extendedBulkNormedSpace period hPeriod metric massSquared data analysis)
    (globalPairedGeneralMetricDeDonderGraphHessian period hPeriod metric)
    (metricProjection period hPeriod metric massSquared data analysis)

private def offShellPullbackForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  pullbackRealBilinear
    (extendedBulkOffShellNormedSpace period hPeriod metric)
    (extendedBulkNormedSpace period hPeriod metric massSquared data analysis)
    (globalPairedAbelianOffShellHessian period hPeriod metric)
    (offShellProjection period hPeriod metric massSquared data analysis)

private def matterPullbackForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  pullbackRealBilinear
    (inferInstance : NormedSpace Real
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared))
    (extendedBulkNormedSpace period hPeriod metric massSquared data analysis)
    (programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared)
    (matterProjection period hPeriod metric massSquared data analysis)

private def llPullbackForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  pullbackRealBilinear
    (extendedBulkLLNormedSpace period hPeriod data analysis)
    (extendedBulkNormedSpace period hPeriod metric massSquared data analysis)
    (globalCandidateAFullLLGraphForm period hPeriod data analysis)
    (llProjection period hPeriod metric massSquared data analysis)

/-- Bounded block-diagonal Hessian on the nonduplicated product. -/
def extendedBulkHessianCLM
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  metricPullbackForm period hPeriod metric massSquared data analysis +
    offShellPullbackForm period hPeriod metric massSquared data analysis +
    matterPullbackForm period hPeriod metric massSquared data analysis +
    llPullbackForm period hPeriod metric massSquared data analysis

@[simp]
theorem extendedBulkHessianCLM_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAAbelianExtendedBulkGraphHilbert
      period hPeriod metric massSquared data analysis) :
    extendedBulkHessianCLM period hPeriod metric massSquared data analysis
        first second =
      globalPairedGeneralMetricDeDonderGraphHessian period hPeriod metric
          first.1 second.1 +
        globalPairedAbelianOffShellHessian period hPeriod metric
          first.2.1 second.2.1 +
        programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
          first.2.2.1 second.2.2.1 +
        globalCandidateAFullLLGraphForm period hPeriod data analysis
          first.2.2.2 second.2.2.2 :=
  rfl

/-- Exact direct sum of the metric, off-shell BRST, matter and LL Hessians.
There is deliberately no independent Lorenz quadratic form. -/
def extendedBulkHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAAbelianExtendedBulkGraphHilbert
      period hPeriod metric massSquared data analysis) : Real :=
  extendedBulkHessianCLM period hPeriod metric massSquared data analysis
    first second

@[simp]
theorem extendedBulkHessian_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAAbelianExtendedBulkGraphHilbert
      period hPeriod metric massSquared data analysis) :
    extendedBulkHessian period hPeriod metric massSquared data analysis
        first second =
      globalPairedGeneralMetricDeDonderGraphHessian period hPeriod metric
          first.1 second.1 +
        globalPairedAbelianOffShellHessian period hPeriod metric
          first.2.1 second.2.1 +
        programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
          first.2.2.1 second.2.2.1 +
        globalCandidateAFullLLGraphForm period hPeriod data analysis
          first.2.2.2 second.2.2.2 :=
  rfl

theorem extendedBulkHessianCLM_comm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAAbelianExtendedBulkGraphHilbert
      period hPeriod metric massSquared data analysis) :
    extendedBulkHessianCLM period hPeriod metric massSquared data analysis
        first second =
      extendedBulkHessianCLM period hPeriod metric massSquared data analysis
        second first := by
  let metricFirst :=
    globalPairedGeneralMetricDeDonderGraphHessian period hPeriod metric
      first.1 second.1
  let metricSecond :=
    globalPairedGeneralMetricDeDonderGraphHessian period hPeriod metric
      second.1 first.1
  let offShellFirst :=
    globalPairedAbelianOffShellHessian period hPeriod metric
      first.2.1 second.2.1
  let offShellSecond :=
    globalPairedAbelianOffShellHessian period hPeriod metric
      second.2.1 first.2.1
  let matterFirst :=
    programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
      first.2.2.1 second.2.2.1
  let matterSecond :=
    programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
      second.2.2.1 first.2.2.1
  let llFirst :=
    globalCandidateAFullLLGraphForm period hPeriod data analysis
      first.2.2.2 second.2.2.2
  let llSecond :=
    globalCandidateAFullLLGraphForm period hPeriod data analysis
      second.2.2.2 first.2.2.2
  change metricFirst + offShellFirst + matterFirst + llFirst =
    metricSecond + offShellSecond + matterSecond + llSecond
  have hMetric : metricFirst = metricSecond :=
    globalPairedGeneralMetricDeDonderGraphHessian_comm period hPeriod metric
      first.1 second.1
  have hOffShell : offShellFirst = offShellSecond :=
    globalPairedAbelianOffShellHessian_comm period hPeriod metric
      first.2.1 second.2.1
  have hMatter : matterFirst = matterSecond :=
    programPPrimitiveSpinCMatterGraphForm_comm period hPeriod massSquared
      first.2.2.1 second.2.2.1
  have hLL : llFirst = llSecond :=
    globalCandidateAFullLLGraphForm_comm period hPeriod data analysis
      first.2.2.2 second.2.2.2
  calc
    metricFirst + offShellFirst + matterFirst + llFirst =
        metricSecond + offShellFirst + matterFirst + llFirst :=
      congrArg (fun value => value + offShellFirst + matterFirst + llFirst)
        hMetric
    _ = metricSecond + offShellSecond + matterFirst + llFirst :=
      congrArg (fun value => metricSecond + value + matterFirst + llFirst)
        hOffShell
    _ = metricSecond + offShellSecond + matterSecond + llFirst :=
      congrArg (fun value => metricSecond + offShellSecond + value + llFirst)
        hMatter
    _ = metricSecond + offShellSecond + matterSecond + llSecond :=
      congrArg (fun value => metricSecond + offShellSecond + matterSecond + value)
        hLL

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

/-- Exact quadratic action of the nonduplicated product. -/
def extendedBulkAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod
      metric massSquared data analysis) : Real :=
  (1 / 2 : Real) *
    extendedBulkHessian period hPeriod metric massSquared data analysis
      state state

theorem extendedBulkAction_eq_sectorActions
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod
      metric massSquared data analysis) :
    extendedBulkAction period hPeriod metric massSquared data analysis state =
      (1 / 2 : Real) *
          globalPairedGeneralMetricDeDonderGraphHessian period hPeriod metric
            state.1 state.1 +
        globalPairedAbelianOffShellGraphAction period hPeriod metric
          state.2.1 +
        programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          state.2.2.1 +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          state.2.2.2 := by
  unfold extendedBulkAction globalPairedAbelianOffShellGraphAction
    programPPrimitiveSpinCMatterGraphAction
    globalCandidateAFullLLGraphAction
  rw [extendedBulkHessian_apply]
  ring

theorem extendedBulkAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod
      metric massSquared data analysis) :
    HasFDerivAt
      (extendedBulkAction period hPeriod metric massSquared data analysis)
      (extendedBulkHessianCLM period hPeriod metric massSquared data analysis
        state)
      state := by
  unfold extendedBulkAction extendedBulkHessian
  exact @symmetricQuadratic_hasFDerivAt
    (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    inferInstance
    (extendedBulkNormedSpace period hPeriod metric massSquared data analysis)
    (extendedBulkHessianCLM period hPeriod metric massSquared data analysis)
    (extendedBulkHessianCLM_comm period hPeriod metric massSquared data
      analysis)
    state

theorem extendedBulkAction_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod
      metric massSquared data analysis) :
    fderiv Real
        (extendedBulkAction period hPeriod metric massSquared data analysis)
        state =
      extendedBulkHessianCLM period hPeriod metric massSquared data analysis
        state := by
  letI : NormedSpace Real
      (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
    extendedBulkNormedSpace period hPeriod metric massSquared data analysis
  exact (extendedBulkAction_hasFDerivAt period hPeriod metric massSquared data
    analysis state).fderiv

theorem extendedBulkAction_second_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (base : GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod
      metric massSquared data analysis) :
    fderiv Real
        (fun state => fderiv Real
          (extendedBulkAction period hPeriod metric massSquared data analysis)
          state)
        base =
      extendedBulkHessianCLM period hPeriod metric massSquared data analysis := by
  have hLinear :
      HasFDerivAt
        (extendedBulkHessianCLM period hPeriod metric massSquared data analysis)
        (extendedBulkHessianCLM period hPeriod metric massSquared data analysis)
        base :=
    (extendedBulkHessianCLM period hPeriod metric massSquared data analysis
      ).hasFDerivAt
  have hEventually :
      (fun state => fderiv Real
        (extendedBulkAction period hPeriod metric massSquared data analysis)
        state) =ᶠ[nhds base]
      extendedBulkHessianCLM period hPeriod metric massSquared data analysis :=
    Filter.Eventually.of_forall fun state =>
      extendedBulkAction_fderiv period hPeriod metric massSquared data
        analysis state
  exact (hLinear.congr_of_eventuallyEq hEventually).fderiv

/-- On the smooth core, the only Abelian summand is exactly the canonical
volume specialization of the unchanged off-shell `sΨ` action. -/
theorem extendedBulkAction_smooth_eq_BRSTAndSectorActions
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAAbelianExtendedBulkSmoothCore
      period hPeriod analysis) :
    extendedBulkAction period hPeriod metric massSquared data analysis
        (extendedBulkSmoothEmbedding period hPeriod metric massSquared data
          analysis core) =
      (1 / 2 : Real) *
          globalPairedGeneralMetricDeDonderGraphHessian period hPeriod metric
            (globalPairedGeneralMetricDeDonderSmoothEmbedding period hPeriod
              metric core.1)
            (globalPairedGeneralMetricDeDonderSmoothEmbedding period hPeriod
              metric core.1) +
        globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
          core.2.1
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
            massSquared core.2.2.1) +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            core.2.2.2) := by
  rw [extendedBulkAction_eq_sectorActions]
  change
    _ + globalPairedAbelianOffShellGraphAction period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
          core.2.1) + _ + _ = _
  rw [globalPairedAbelianOffShellGraphAction_smooth_eq_BRST]
  rfl

/-- The assembled quadratic action is smooth because every displayed block
is a bounded bilinear form on its closed graph factor. -/
theorem extendedBulkAction_contDiff
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
      (extendedBulkAction period hPeriod metric massSquared data analysis) := by
  unfold extendedBulkAction extendedBulkHessian
  fun_prop

theorem extendedBulkAction_contDiff_two
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
      (extendedBulkAction period hPeriod metric massSquared data analysis) :=
  (extendedBulkAction_contDiff period hPeriod metric massSquared data analysis
    ).of_le (by simp)

/-! ## Corrected combined typed tangent -/

def extendedMatterMinimalTangentLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration where
  toFun coefficients :=
    ⟨globalCandidateABulkMatterPhysicalTangentLinearMap period hPeriod
      configuration coefficients, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (globalCandidateABulkMatterPhysicalTangentLinearMap period hPeriod
      configuration).map_add first second
  map_smul' scalar coefficients := by
    apply Subtype.ext
    exact (globalCandidateABulkMatterPhysicalTangentLinearMap period hPeriod
      configuration).map_smul scalar coefficients

def extendedLLMinimalTangentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration where
  toFun direction :=
    ⟨fullLLSmoothPhysicalTangentLinearMap period hPeriod analysis direction,
      rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact (fullLLSmoothPhysicalTangentLinearMap period hPeriod analysis
      ).map_add first second
  map_smul' scalar direction := by
    apply Subtype.ext
    exact (fullLLSmoothPhysicalTangentLinearMap period hPeriod analysis
      ).map_smul scalar direction

def extendedMatterGaugeFixedTangentLinearMap
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration :=
  (globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap period hPeriod
    configuration).comp
      (extendedMatterMinimalTangentLinearMap period hPeriod
        configuration.physical)

def extendedLLGaugeFixedTangentLinearMap
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalFullLLSmooth period hPeriod analysis →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration :=
  (globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap period hPeriod
    configuration).comp
      (extendedLLMinimalTangentLinearMap period hPeriod analysis)

/-- Metric, Abelian potential/nonminimal, matter and LL directions occupy
their distinct corrected slots.  The potential occurs only in the Abelian
summand. -/
def extendedBulkGaugeFixedTangentLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAAbelianExtendedBulkSmoothCore period hPeriod analysis →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration where
  toFun core :=
    globalMetricPerturbationGaugeFixedTangentLinearMap period hPeriod
        configuration core.1 +
      globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
        configuration data core.2.1 +
      extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
        core.2.2.1 +
      extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
        analysis core.2.2.2
  map_add' first second := by
    change
      globalMetricPerturbationGaugeFixedTangentLinearMap period hPeriod
            configuration (first.1 + second.1) +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data (first.2.1 + second.2.1) +
        extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
            (first.2.2.1 + second.2.2.1) +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis (first.2.2.2 + second.2.2.2) =
      (globalMetricPerturbationGaugeFixedTangentLinearMap period hPeriod
            configuration first.1 +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data first.2.1 +
        extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
            first.2.2.1 +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis first.2.2.2) +
      (globalMetricPerturbationGaugeFixedTangentLinearMap period hPeriod
            configuration second.1 +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data second.2.1 +
        extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
            second.2.2.1 +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis second.2.2.2)
    simp only [map_add]
    abel
  map_smul' scalar core := by
    change
      globalMetricPerturbationGaugeFixedTangentLinearMap period hPeriod
            configuration (scalar • core.1) +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data (scalar • core.2.1) +
        extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
            (scalar • core.2.2.1) +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis (scalar • core.2.2.2) =
      scalar •
        (globalMetricPerturbationGaugeFixedTangentLinearMap period hPeriod
              configuration core.1 +
            globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
              configuration data core.2.1 +
          extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
              core.2.2.1 +
          extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
              analysis core.2.2.2)
    simp only [map_smul, smul_add]

/-- The graph point and corrected typed tangent are fibered over the same
smooth core, without reintroducing a separate Lorenz potential. -/
def extendedBulkGraphTypedCoreLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAAbelianExtendedBulkSmoothCore period hPeriod analysis →ₗ[Real]
      (GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis ×
        GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration) where
  toFun core :=
    (extendedBulkSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis core,
      extendedBulkGaugeFixedTangentLinearMap period hPeriod configuration
        data analysis core)
  map_add' first second := by
    apply Prod.ext
    · exact (extendedBulkSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis).map_add first second
    · exact (extendedBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis).map_add first second
  map_smul' scalar core := by
    apply Prod.ext
    · exact (extendedBulkSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis).map_smul scalar core
    · exact (extendedBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis).map_smul scalar core

theorem extendedBulkGraphTypedCoreLinearMap_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Function.Injective
      (extendedBulkGraphTypedCoreLinearMap period hPeriod configuration data
        analysis) := by
  intro first second hEqual
  apply extendedBulkSmoothEmbedding_injective period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
  exact congrArg Prod.fst hEqual


end
end P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
end JanusFormal
