import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D

/-!
# Candidate-A bulk with diagonal diffeomorphism and Abelian BRST graphs

This replaces the two independent de Donder action blocks by the completed
two-metric/one-triplet diagonal diffeomorphism graph.  The paired Abelian
off-shell graph, primitive SpinC matter graph and full LL graph are reused
unchanged.  Hence neither a Lorenz factor nor a second diffeomorphism triplet
is duplicated.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set
open scoped InnerProductSpace Topology ContDiff
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance diagonalBulkCanonicalLorentzVolumeFinite :
    MeasureTheory.IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.canonicalLorentzVolumeFinite
    period hPeriod

local instance (priority := 10001)
    diagonalBulkDiffeomorphismNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedAddCommGroupValue
    period hPeriod metric

local instance (priority := 10001)
    diagonalBulkDiffeomorphismContinuousAdd
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousAdd
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphContinuousAdd
    period hPeriod metric

local instance (priority := 10001) diagonalBulkDiffeomorphismNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedSpace
    period hPeriod metric

local instance (priority := 10001) diagonalBulkDiffeomorphismModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphModule
    period hPeriod metric

local instance (priority := 10001) diagonalBulkAbelianNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D.extendedBulkOffShellNormedSpace
    period hPeriod metric

local instance (priority := 10001) diagonalBulkAbelianModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D.extendedBulkOffShellModule
    period hPeriod metric

local instance (priority := 10001) diagonalBulkLLNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D.extendedBulkLLNormedSpace
    period hPeriod data analysis

local instance (priority := 10001) diagonalBulkLLModule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D.extendedBulkLLModule
    period hPeriod data analysis

/-- Total physical bulk chart with both nonduplicated off-shell BRST graphs. -/
abbrev GlobalCandidateADiagonalExtendedBulkGraphHilbert
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric ×
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric ×
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared ×
        GlobalFullLLGraphHilbert period hPeriod data analysis))

local instance (priority := 10002) diagonalBulkNormedAddCommGroup
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
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
  Prod.normedAddCommGroup

local instance (priority := 10003) diagonalBulkSeminormedAddCommGroup
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    SeminormedAddCommGroup
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
  Prod.seminormedAddCommGroup

local instance (priority := 10002) diagonalBulkNormedSpace
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
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
  Prod.normedSpace

local instance (priority := 10003) diagonalBulkModule
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
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
  (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis
    ).toModule

local instance (priority := 10004) diagonalBulkIsBoundedSMul
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
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
  @NormedSpace.toIsBoundedSMul Real
    (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    inferInstance inferInstance
    (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)

/-- Smooth fiber product: two metric perturbations, one diffeomorphism
triplet, the paired Abelian state, matter coefficients and a smooth LL state. -/
abbrev GlobalCandidateADiagonalExtendedBulkSmoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod ×
    (GlobalPairedAbelianBRSTState period hPeriod ×
      (ProgramPPrimitiveSpinCMatterFiniteCoefficients ×
        GlobalFullLLSmooth period hPeriod analysis))

def diagonalExtendedBulkSmoothEmbedding
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
      →ₗ[Real]
      GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis where
  toFun core :=
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric core.1,
      (globalPairedAbelianOffShellSmoothEmbedding
          period hPeriod metric core.2.1,
        (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
            period hPeriod massSquared core.2.2.1,
          globalCandidateAFullLLSmoothEmbedding
            period hPeriod data analysis core.2.2.2)))
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric).map_add first.1 second.1
    · apply Prod.ext
      · exact
          (globalPairedAbelianOffShellSmoothEmbedding
            period hPeriod metric).map_add first.2.1 second.2.1
      · apply Prod.ext
        · exact
            (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
              period hPeriod massSquared).map_add first.2.2.1 second.2.2.1
        · exact
            (globalCandidateAFullLLSmoothEmbedding
              period hPeriod data analysis).map_add first.2.2.2 second.2.2.2
  map_smul' scalar core := by
    apply Prod.ext
    · exact
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric).map_smul scalar core.1
    · apply Prod.ext
      · exact
          (globalPairedAbelianOffShellSmoothEmbedding
            period hPeriod metric).map_smul scalar core.2.1
      · apply Prod.ext
        · exact
            (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
              period hPeriod massSquared).map_smul scalar core.2.2.1
        · exact
            (globalCandidateAFullLLSmoothEmbedding
              period hPeriod data analysis).map_smul scalar core.2.2.2

theorem diagonalExtendedBulkSmoothEmbedding_injective
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
      (diagonalExtendedBulkSmoothEmbedding
        period hPeriod metric massSquared data analysis) := by
  intro first second hEqual
  apply Prod.ext
  · apply
      globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_injective
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

theorem diagonalExtendedBulkSmoothEmbedding_denseRange
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
      (diagonalExtendedBulkSmoothEmbedding
        period hPeriod metric massSquared data analysis) := by
  have hProduct :=
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_denseRange
      period hPeriod metric).prodMap
      ((globalPairedAbelianOffShellSmoothEmbedding_denseRange
        period hPeriod metric).prodMap
        ((programPPrimitiveSpinCMatterGraphFiniteLinearMap_denseRange
          period hPeriod massSquared).prodMap
          (globalCandidateAFullLLSmoothEmbedding_denseRange
            period hPeriod data analysis)))
  apply Dense.mono _ hProduct
  rintro _ ⟨⟨diffeomorphismCore, abelianCore, matterCore, llCore⟩, rfl⟩
  exact
    ⟨(diffeomorphismCore, (abelianCore, (matterCore, llCore))), rfl⟩

/-! ## Bounded total Hessian -/

local instance diagonalBulkDualNormedAddCommGroup
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
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real) :=
  @ContinuousLinearMap.toNormedAddCommGroup
    Real Real
    (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    Real inferInstance inferInstance inferInstance inferInstance
    (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)
    inferInstance (RingHom.id Real) inferInstance

local instance diagonalBulkDualNormedSpace
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
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real) :=
  @ContinuousLinearMap.toNormedSpace
    Real Real
    (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    Real inferInstance inferInstance inferInstance inferInstance
    (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)
    inferInstance (RingHom.id Real) inferInstance
    Real inferInstance inferInstance inferInstance

def diagonalDiffeomorphismProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric :=
  { toFun := Prod.fst
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_fst }

def diagonalAbelianProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric :=
  { toFun := fun state => state.2.1
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_fst.comp continuous_snd }

def diagonalMatterProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared :=
  { toFun := fun state => state.2.2.1
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_fst.comp (continuous_snd.comp continuous_snd) }

def diagonalLLProjection
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
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
    (projection : D →L[Real] E) : D →L[Real] D →L[Real] Real :=
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

private def diagonalDiffeomorphismPullbackForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  pullbackRealBilinear
    (diagonalBulkDiffeomorphismNormedSpace period hPeriod metric)
    (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)
    (globalCandidateADiagonalDiffeomorphismOffShellHessian
      period hPeriod couplings metric)
    (diagonalDiffeomorphismProjection
      period hPeriod metric massSquared data analysis)

private def diagonalAbelianPullbackForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  pullbackRealBilinear
    (diagonalBulkAbelianNormedSpace period hPeriod metric)
    (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)
    (globalPairedAbelianOffShellHessian period hPeriod metric)
    (diagonalAbelianProjection period hPeriod metric massSquared data analysis)

private def diagonalMatterPullbackForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  pullbackRealBilinear
    (inferInstance : NormedSpace Real
      (ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared))
    (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)
    (programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared)
    (diagonalMatterProjection period hPeriod metric massSquared data analysis)

private def diagonalLLPullbackForm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  pullbackRealBilinear
    (diagonalBulkLLNormedSpace period hPeriod data analysis)
    (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)
    (globalCandidateAFullLLGraphForm period hPeriod data analysis)
    (diagonalLLProjection period hPeriod metric massSquared data analysis)

private def realBilinearAdd
    {D : Type*} [NormedAddCommGroup D] [NormedSpace Real D]
    (first second : D →L[Real] D →L[Real] Real) :
    D →L[Real] D →L[Real] Real :=
  first + second

/-- Total bounded Hessian after replacing the two independent de Donder
blocks by the one-triplet diagonal BRST block. -/
def diagonalExtendedBulkHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  @realBilinearAdd
    (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    inferInstance
    (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)
    (@realBilinearAdd
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis)
      inferInstance
      (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)
      (diagonalDiffeomorphismPullbackForm
        period hPeriod metric massSquared data analysis)
      (diagonalAbelianPullbackForm
        period hPeriod metric massSquared data analysis))
    (@realBilinearAdd
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis)
      inferInstance
      (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)
      (diagonalMatterPullbackForm
        period hPeriod metric massSquared data analysis)
      (diagonalLLPullbackForm
        period hPeriod metric massSquared data analysis))

@[simp]
theorem diagonalExtendedBulkHessian_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateADiagonalExtendedBulkGraphHilbert
      period hPeriod metric massSquared data analysis) :
    diagonalExtendedBulkHessian period hPeriod metric massSquared data analysis
        first second =
      globalCandidateADiagonalDiffeomorphismOffShellHessian
          period hPeriod couplings metric first.1 second.1 +
        globalPairedAbelianOffShellHessian period hPeriod metric
          first.2.1 second.2.1 +
        programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
          first.2.2.1 second.2.2.1 +
        globalCandidateAFullLLGraphForm period hPeriod data analysis
          first.2.2.2 second.2.2.2 :=
by
  change
    (globalCandidateADiagonalDiffeomorphismOffShellHessian
        period hPeriod couplings metric first.1 second.1 +
      globalPairedAbelianOffShellHessian period hPeriod metric
        first.2.1 second.2.1) +
      (programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
          first.2.2.1 second.2.2.1 +
        globalCandidateAFullLLGraphForm period hPeriod data analysis
          first.2.2.2 second.2.2.2) = _
  ring

theorem diagonalExtendedBulkHessian_comm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateADiagonalExtendedBulkGraphHilbert
      period hPeriod metric massSquared data analysis) :
    diagonalExtendedBulkHessian period hPeriod metric massSquared data analysis
        first second =
      diagonalExtendedBulkHessian period hPeriod metric massSquared data analysis
        second first := by
  rw [diagonalExtendedBulkHessian_apply,
    diagonalExtendedBulkHessian_apply]
  let diffeomorphismFirst :=
    globalCandidateADiagonalDiffeomorphismOffShellHessian
      period hPeriod couplings metric first.1 second.1
  let diffeomorphismSecond :=
    globalCandidateADiagonalDiffeomorphismOffShellHessian
      period hPeriod couplings metric second.1 first.1
  let abelianFirst :=
    globalPairedAbelianOffShellHessian period hPeriod metric
      first.2.1 second.2.1
  let abelianSecond :=
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
  change diffeomorphismFirst + abelianFirst + matterFirst + llFirst =
    diffeomorphismSecond + abelianSecond + matterSecond + llSecond
  have hDiffeomorphism : diffeomorphismFirst = diffeomorphismSecond :=
    globalCandidateADiagonalDiffeomorphismOffShellHessian_comm
      period hPeriod couplings metric first.1 second.1
  have hAbelian : abelianFirst = abelianSecond :=
    globalPairedAbelianOffShellHessian_comm period hPeriod metric
      first.2.1 second.2.1
  have hMatter : matterFirst = matterSecond :=
    programPPrimitiveSpinCMatterGraphForm_comm period hPeriod massSquared
      first.2.2.1 second.2.2.1
  have hLL : llFirst = llSecond :=
    globalCandidateAFullLLGraphForm_comm period hPeriod data analysis
      first.2.2.2 second.2.2.2
  calc
    diffeomorphismFirst + abelianFirst + matterFirst + llFirst =
        diffeomorphismSecond + abelianFirst + matterFirst + llFirst :=
      congrArg
        (fun value => value + abelianFirst + matterFirst + llFirst)
        hDiffeomorphism
    _ = diffeomorphismSecond + abelianSecond + matterFirst + llFirst :=
      congrArg
        (fun value => diffeomorphismSecond + value + matterFirst + llFirst)
        hAbelian
    _ = diffeomorphismSecond + abelianSecond + matterSecond + llFirst :=
      congrArg
        (fun value => diffeomorphismSecond + abelianSecond + value + llFirst)
        hMatter
    _ = diffeomorphismSecond + abelianSecond + matterSecond + llSecond :=
      congrArg
        (fun value => diffeomorphismSecond + abelianSecond + matterSecond + value)
        hLL

/-! ## Same-action quadratic calculus -/

def diagonalExtendedBulkAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod
      metric massSquared data analysis) : Real :=
  (1 / 2 : Real) *
    diagonalExtendedBulkHessian period hPeriod metric massSquared data analysis
      state state

theorem diagonalExtendedBulkAction_eq_sectorActions
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod
      metric massSquared data analysis) :
    diagonalExtendedBulkAction period hPeriod metric massSquared data analysis
        state =
      globalCandidateADiagonalDiffeomorphismOffShellGraphAction
          period hPeriod couplings metric state.1 +
        globalPairedAbelianOffShellGraphAction period hPeriod metric
          state.2.1 +
        programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          state.2.2.1 +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          state.2.2.2 := by
  unfold diagonalExtendedBulkAction
    globalCandidateADiagonalDiffeomorphismOffShellGraphAction
    globalPairedAbelianOffShellGraphAction
    programPPrimitiveSpinCMatterGraphAction
    globalCandidateAFullLLGraphAction
  rw [diagonalExtendedBulkHessian_apply]
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

theorem diagonalExtendedBulkAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod
      metric massSquared data analysis) :
    HasFDerivAt
      (diagonalExtendedBulkAction
        period hPeriod metric massSquared data analysis)
      (diagonalExtendedBulkHessian
        period hPeriod metric massSquared data analysis state) state :=
by
  exact @symmetricQuadratic_hasFDerivAt
    (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
      massSquared data analysis)
    inferInstance
    (diagonalBulkNormedSpace period hPeriod metric massSquared data analysis)
    (diagonalExtendedBulkHessian
      period hPeriod metric massSquared data analysis)
    (diagonalExtendedBulkHessian_comm
      period hPeriod metric massSquared data analysis) state

theorem diagonalExtendedBulkAction_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod
      metric massSquared data analysis) :
    fderiv Real
        (diagonalExtendedBulkAction
          period hPeriod metric massSquared data analysis) state =
      diagonalExtendedBulkHessian
        period hPeriod metric massSquared data analysis state :=
by
  exact (diagonalExtendedBulkAction_hasFDerivAt
    period hPeriod metric massSquared data analysis state).fderiv

theorem diagonalExtendedBulkAction_fderiv_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (base : GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod
      metric massSquared data analysis) :
    HasFDerivAt
        (fun state => fderiv Real
          (diagonalExtendedBulkAction period hPeriod metric massSquared data
            analysis) state)
      (diagonalExtendedBulkHessian
        period hPeriod metric massSquared data analysis)
      base := by
  have hLinear :
      HasFDerivAt
        (diagonalExtendedBulkHessian
          period hPeriod metric massSquared data analysis)
        (diagonalExtendedBulkHessian
          period hPeriod metric massSquared data analysis)
        base :=
    (diagonalExtendedBulkHessian
      period hPeriod metric massSquared data analysis).hasFDerivAt
  have hEventually :
      (fun state => fderiv Real
        (diagonalExtendedBulkAction
          period hPeriod metric massSquared data analysis) state) =ᶠ[nhds base]
      diagonalExtendedBulkHessian
        period hPeriod metric massSquared data analysis :=
    Filter.Eventually.of_forall fun state =>
      diagonalExtendedBulkAction_fderiv
        period hPeriod metric massSquared data analysis state
  exact hLinear.congr_of_eventuallyEq hEventually

theorem diagonalExtendedBulkAction_contDiff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    @ContDiff Real inferInstance
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis)
      (diagonalBulkNormedAddCommGroup
        period hPeriod metric massSquared data analysis)
      (diagonalBulkNormedSpace
        period hPeriod metric massSquared data analysis)
      Real inferInstance inferInstance ⊤
      (diagonalExtendedBulkAction
        period hPeriod metric massSquared data analysis) := by
  letI : NormedAddCommGroup
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
    diagonalBulkNormedAddCommGroup
      period hPeriod metric massSquared data analysis
  letI : SeminormedAddCommGroup
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
    diagonalBulkSeminormedAddCommGroup
      period hPeriod metric massSquared data analysis
  letI : NormedSpace Real
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
    diagonalBulkNormedSpace period hPeriod metric massSquared data analysis
  unfold diagonalExtendedBulkAction
  fun_prop

theorem diagonalExtendedBulkAction_contDiff_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    @ContDiff Real inferInstance
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis)
      (diagonalBulkNormedAddCommGroup
        period hPeriod metric massSquared data analysis)
      (diagonalBulkNormedSpace
        period hPeriod metric massSquared data analysis)
      Real inferInstance inferInstance 2
      (diagonalExtendedBulkAction
        period hPeriod metric massSquared data analysis) := by
  letI : NormedAddCommGroup
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
    diagonalBulkNormedAddCommGroup
      period hPeriod metric massSquared data analysis
  letI : SeminormedAddCommGroup
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
    diagonalBulkSeminormedAddCommGroup
      period hPeriod metric massSquared data analysis
  letI : NormedSpace Real
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis) :=
    diagonalBulkNormedSpace period hPeriod metric massSquared data analysis
  unfold diagonalExtendedBulkAction
  fun_prop

theorem diagonalExtendedBulkAction_smooth_eq_BRSTAndSectorActions
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkAction period hPeriod metric massSquared data analysis
        (diagonalExtendedBulkSmoothEmbedding
          period hPeriod metric massSquared data analysis core) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
          period hPeriod couplings metric core.1 +
        globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
          core.2.1 (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
            period hPeriod massSquared core.2.2.1) +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding
            period hPeriod data analysis core.2.2.2) := by
  rw [diagonalExtendedBulkAction_eq_sectorActions]
  change
    globalCandidateADiagonalDiffeomorphismOffShellGraphAction
          period hPeriod couplings metric
          (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
            period hPeriod metric core.1) +
      globalPairedAbelianOffShellGraphAction period hPeriod metric
          (globalPairedAbelianOffShellSmoothEmbedding
            period hPeriod metric core.2.1) + _ + _ = _
  rw [globalCandidateADiagonalDiffeomorphismOffShellGraphAction_smooth_eq_BRST,
    globalPairedAbelianOffShellGraphAction_smooth_eq_BRST]
  rfl

/-! ## Faithful typed raccord -/

/-- The two metric perturbations and the shared diffeomorphism triplet occupy
their pre-existing physical and typed nonminimal slots. -/
def diagonalDiffeomorphismGaugeFixedTangentLinearMap
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration where
  toFun state :=
    (globalMetricPerturbationMinimalPhysicalTangentLinearMap
        period hPeriod configuration.physical state.metricPerturbation,
      globalDiffeomorphismNonminimalTypedInclusionLinearMap
        period hPeriod state.nonminimal)
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalMetricPerturbationMinimalPhysicalTangentLinearMap
          period hPeriod configuration.physical).map_add
            first.metricPerturbation second.metricPerturbation
    · exact
        (globalDiffeomorphismNonminimalTypedInclusionLinearMap
          period hPeriod).map_add first.nonminimal second.nonminimal
  map_smul' scalar state := by
    apply Prod.ext
    · exact
        (globalMetricPerturbationMinimalPhysicalTangentLinearMap
          period hPeriod configuration.physical).map_smul
            scalar state.metricPerturbation
    · exact
        (globalDiffeomorphismNonminimalTypedInclusionLinearMap
          period hPeriod).map_smul scalar state.nonminimal

@[simp]
theorem diagonalDiffeomorphismGaugeFixedTangent_metric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (diagonalDiffeomorphismGaugeFixedTangentLinearMap
        period hPeriod configuration state).1.1).fullMetricPerturbation =
      state.metricPerturbation :=
  rfl

@[simp]
theorem diagonalDiffeomorphismGaugeFixedTangent_diffeomorphism
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState
      period hPeriod) :
    (diagonalDiffeomorphismGaugeFixedTangentLinearMap
      period hPeriod configuration state).2.diffeomorphism =
      state.nonminimal :=
  rfl

/-- The diagonal metric/diffeomorphism, paired Abelian, matter and LL
directions are assembled in the corrected typed tangent without duplicating
either nonminimal sector. -/
def diagonalExtendedBulkGaugeFixedTangentLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
      →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration where
  toFun core :=
    diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
        configuration core.1 +
      globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
        configuration data core.2.1 +
      extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
        core.2.2.1 +
      extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
        analysis core.2.2.2
  map_add' first second := by
    change
      diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
            configuration (first.1 + second.1) +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data (first.2.1 + second.2.1) +
        extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
            (first.2.2.1 + second.2.2.1) +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis (first.2.2.2 + second.2.2.2) =
      (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
            configuration first.1 +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data first.2.1 +
        extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
            first.2.2.1 +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis first.2.2.2) +
      (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
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
      diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
            configuration (scalar • core.1) +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data (scalar • core.2.1) +
        extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
            (scalar • core.2.2.1) +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis (scalar • core.2.2.2) =
      scalar •
        (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
              configuration core.1 +
            globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
              configuration data core.2.1 +
          extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration
              core.2.2.1 +
          extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
              analysis core.2.2.2)
    simp only [map_smul, smul_add]

/-- The completed diagonal graph and its corrected typed tangent are fibered
over the same smooth core. -/
def diagonalExtendedBulkGraphTypedCoreLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
      →ₗ[Real]
      (GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis ×
        GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration) where
  toFun core :=
    (diagonalExtendedBulkSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis core,
      diagonalExtendedBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core)
  map_add' first second := by
    apply Prod.ext
    · exact
        (diagonalExtendedBulkSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis).map_add first second
    · exact
        (diagonalExtendedBulkGaugeFixedTangentLinearMap period hPeriod
          configuration data analysis).map_add first second
  map_smul' scalar core := by
    apply Prod.ext
    · exact
        (diagonalExtendedBulkSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis).map_smul scalar core
    · exact
        (diagonalExtendedBulkGaugeFixedTangentLinearMap period hPeriod
          configuration data analysis).map_smul scalar core

theorem diagonalExtendedBulkGraphTypedCoreLinearMap_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Function.Injective
      (diagonalExtendedBulkGraphTypedCoreLinearMap period hPeriod
        configuration data analysis) := by
  intro first second hEqual
  apply diagonalExtendedBulkSmoothEmbedding_injective period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
  exact congrArg Prod.fst hEqual

end

end P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
end JanusFormal
