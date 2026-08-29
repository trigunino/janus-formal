import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D

/-!
# L2 Hilbertization of the Candidate-A Abelian extended bulk graph

The existing extended bulk chart uses finite ordinary products, hence their
equivalent maximum norm.  This file equips the same five graph factors with
nested `WithLp 2` products.  The resulting complete real Hilbert space is
continuously linearly equivalent to the existing chart.

Transporting the unchanged same-action Hessian through that equivalence gives
a bounded self-adjoint Riesz representative.  In particular the paired
ghost/antighost Hessian needs no separate self-adjointness assertion for the
single scalar Faddeev--Popov operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1600000

noncomputable section

open scoped InnerProductSpace ENNReal
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairingC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance l2MetricGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D.pairingGraphModule
    period hPeriod metric

local instance l2MetricGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D.pairingGraphNormedSpace
    period hPeriod metric

local instance l2MetricGraphInnerProductSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  Submodule.innerProductSpace
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod metric)

local instance l2MetricGraphCompleteSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  globalGeneralMetricDeDonderPairingGraphCompleteSpace
    period hPeriod metric

local instance l2OffShellGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphNormedSpace
    period hPeriod metric

local instance l2OffShellGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.globalPairedAbelianOffShellGraphModule
    period hPeriod metric

local instance l2OffShellGraphInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  Submodule.innerProductSpace
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod metric)

local instance l2OffShellGraphCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  globalPairedAbelianOffShellGraphCompleteSpace period hPeriod metric

local instance l2LLGraphInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  P0EFTJanusProgramPGlobalFullLLGraphRiesz4D.globalFullLLGraphInnerProductSpace
    period hPeriod data analysis

local instance l2LLGraphNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (l2LLGraphInnerProductSpace period hPeriod data analysis).toNormedSpace

local instance l2LLGraphModule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (l2LLGraphNormedSpace period hPeriod data analysis).toModule

local instance l2LLGraphCompleteSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CompleteSpace (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  globalCandidateAFullLLGraphCompleteSpace period hPeriod data analysis

local instance l2MatterHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D.programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

/-- L2 ambient product for the exact signed SpinC matter graph. -/
abbrev ProgramPPrimitiveSpinCMatterL2GraphAmbient :=
  WithLp 2
    (ProgramPPrimitiveSpinCMatterHilbert ×
      ProgramPPrimitiveSpinCMatterHilbert)

/-- The existing complex graph viewed over the real action scalars. -/
def programPPrimitiveSpinCMatterRealGraphSubmodule
    (massSquared : Real) :
    Submodule Real
      (ProgramPPrimitiveSpinCMatterHilbert ×
        ProgramPPrimitiveSpinCMatterHilbert) :=
  ((complexDiagonalOperator ProgramPPrimitiveSpinCMatterMode
      (programPPrimitiveSpinCMatterHessianWeight
        period hPeriod massSquared)).graph).restrictScalars Real

/-- The same matter graph inside the equivalent L2 product norm. -/
def programPPrimitiveSpinCMatterL2GraphSubmodule
    (massSquared : Real) :
    Submodule Real ProgramPPrimitiveSpinCMatterL2GraphAmbient :=
  (programPPrimitiveSpinCMatterRealGraphSubmodule
      period hPeriod massSquared).comap
    (WithLp.prodContinuousLinearEquiv 2 Real
      ProgramPPrimitiveSpinCMatterHilbert
      ProgramPPrimitiveSpinCMatterHilbert).toLinearMap

/-- Genuine Hilbert graph domain for the signed matter Hessian. -/
abbrev ProgramPPrimitiveSpinCMatterL2GraphDomain
    (massSquared : Real) :=
  programPPrimitiveSpinCMatterL2GraphSubmodule
    period hPeriod massSquared

local instance l2MatterGraphInnerProductSpace
    (massSquared : Real) :
    InnerProductSpace Real
      (ProgramPPrimitiveSpinCMatterL2GraphDomain
        period hPeriod massSquared) :=
  Submodule.innerProductSpace
    (programPPrimitiveSpinCMatterL2GraphSubmodule
      period hPeriod massSquared)

local instance l2MatterGraphClosed
    (massSquared : Real) :
    IsClosed
      (programPPrimitiveSpinCMatterL2GraphSubmodule
        period hPeriod massSquared :
        Set ProgramPPrimitiveSpinCMatterL2GraphAmbient) := by
  change IsClosed
    ((WithLp.prodContinuousLinearEquiv 2 Real
        ProgramPPrimitiveSpinCMatterHilbert
        ProgramPPrimitiveSpinCMatterHilbert) ⁻¹'
      ((complexDiagonalOperator ProgramPPrimitiveSpinCMatterMode
        (programPPrimitiveSpinCMatterHessianWeight
          period hPeriod massSquared)).graph :
        Set (ProgramPPrimitiveSpinCMatterHilbert ×
          ProgramPPrimitiveSpinCMatterHilbert)))
  exact (complexDiagonalOperator_isClosed ProgramPPrimitiveSpinCMatterMode
      (programPPrimitiveSpinCMatterHessianWeight
        period hPeriod massSquared)).preimage
    (WithLp.prodContinuousLinearEquiv 2 Real
      ProgramPPrimitiveSpinCMatterHilbert
      ProgramPPrimitiveSpinCMatterHilbert).continuous

local instance l2MatterGraphCompleteSpace
    (massSquared : Real) :
    CompleteSpace
      (ProgramPPrimitiveSpinCMatterL2GraphDomain
        period hPeriod massSquared) := by
  infer_instance

/-- Continuous linear equivalence between the L2 matter graph and the existing
maximum-norm graph. -/
def programPPrimitiveSpinCMatterL2GraphEquiv
    (massSquared : Real) :
    ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared ≃L[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared where
  toFun state := ⟨
    WithLp.ofLp state.1,
    state.2⟩
  invFun state := ⟨
    WithLp.toLp 2 state.1,
    by
      change WithLp.ofLp (WithLp.toLp 2 state.1) ∈
        programPPrimitiveSpinCMatterRealGraphSubmodule
          period hPeriod massSquared
      rw [WithLp.ofLp_toLp]
      exact state.2⟩
  left_inv state := by
    apply Subtype.ext
    rfl
  right_inv state := by
    apply Subtype.ext
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private abbrev MatterLLL2Tail
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  WithLp 2
    (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared ×
      GlobalFullLLGraphHilbert period hPeriod data analysis)

private abbrev OffShellMatterLLL2Tail
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  WithLp 2
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric ×
      MatterLLL2Tail period hPeriod massSquared data analysis)

private abbrev MinusOffShellMatterLLL2Tail
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  WithLp 2
    (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod (metric .minus) ×
      OffShellMatterLLL2Tail period hPeriod metric massSquared data analysis)

local instance l2MatterLLInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (MatterLLL2Tail period hPeriod massSquared data analysis) :=
  @WithLp.instProdInnerProductSpace
    Real
    (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared)
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    inferInstance inferInstance
    (l2MatterGraphInnerProductSpace period hPeriod massSquared)
    inferInstance
    (l2LLGraphInnerProductSpace period hPeriod data analysis)

local instance l2OffShellMatterLLInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (OffShellMatterLLL2Tail period hPeriod metric massSquared data
        analysis) :=
  @WithLp.instProdInnerProductSpace
    Real
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric)
    (MatterLLL2Tail period hPeriod massSquared data analysis)
    inferInstance inferInstance
    (l2OffShellGraphInnerProductSpace period hPeriod metric)
    inferInstance
    (l2MatterLLInnerProductSpace period hPeriod massSquared data analysis)

local instance l2MinusTailInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (MinusOffShellMatterLLL2Tail period hPeriod metric massSquared data
        analysis) :=
  @WithLp.instProdInnerProductSpace
    Real
    (GlobalGeneralMetricDeDonderPairingGraphHilbert
      period hPeriod (metric .minus))
    (OffShellMatterLLL2Tail period hPeriod metric massSquared data analysis)
    inferInstance inferInstance
    (l2MetricGraphInnerProductSpace period hPeriod (metric .minus))
    inferInstance
    (l2OffShellMatterLLInnerProductSpace period hPeriod metric massSquared data
      analysis)

/-- The five independent graph factors with genuine nested L2 product norms. -/
abbrev GlobalCandidateAAbelianExtendedBulkL2Hilbert
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  WithLp 2
    (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod (metric .plus) ×
      MinusOffShellMatterLLL2Tail period hPeriod metric massSquared data
        analysis)

local instance (priority := 10020) l2ExtendedBulkInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  @WithLp.instProdInnerProductSpace
    Real
    (GlobalGeneralMetricDeDonderPairingGraphHilbert
      period hPeriod (metric .plus))
    (MinusOffShellMatterLLL2Tail period hPeriod metric massSquared data
      analysis)
    inferInstance inferInstance
    (l2MetricGraphInnerProductSpace period hPeriod (metric .plus))
    inferInstance
    (l2MinusTailInnerProductSpace period hPeriod metric massSquared data
      analysis)

local instance (priority := 10010) l2ExtendedBulkNormedSpace
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
      (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  (l2ExtendedBulkInnerProductSpace period hPeriod metric massSquared data
    analysis).toNormedSpace

local instance (priority := 10011) l2ExtendedBulkModule
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
      (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  (l2ExtendedBulkNormedSpace period hPeriod metric massSquared data
    analysis).toModule

local instance l2ExtendedBulkCompleteSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CompleteSpace
      (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) := by
  infer_instance

local instance (priority := 10002) legacyExtendedBulkNormedSpace
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
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D.extendedBulkNormedSpace
    period hPeriod metric massSquared data analysis

local instance (priority := 10003) legacyExtendedBulkModule
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
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D.extendedBulkModule
    period hPeriod metric massSquared data analysis

/-- Continuous linear equivalence from the genuine L2 product to the existing
finite-product chart.  It changes only the equivalent finite-product norm. -/
def extendedBulkL2Equiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis ≃L[Real]
      GlobalCandidateAAbelianExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis where
  toFun state :=
    ((WithLp.fst state, WithLp.fst (WithLp.snd state)),
      (WithLp.fst (WithLp.snd (WithLp.snd state)),
        (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared
            (WithLp.fst (WithLp.snd (WithLp.snd (WithLp.snd state)))),
          WithLp.snd (WithLp.snd (WithLp.snd (WithLp.snd state))))))
  invFun state :=
    WithLp.toLp 2
      (state.1.1,
        WithLp.toLp 2
          (state.1.2,
            WithLp.toLp 2
              (state.2.1,
                WithLp.toLp 2
                  ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
                    massSquared).symm state.2.2.1, state.2.2.2))))
  left_inv state := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · apply WithLp.ofLp_injective 2
      apply Prod.ext
      · rfl
      · apply WithLp.ofLp_injective 2
        apply Prod.ext
        · rfl
        · apply WithLp.ofLp_injective 2
          apply Prod.ext
          · simp
          · rfl
  right_inv state := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · simp
        · rfl
  map_add' first second := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
            massSquared).map_add _ _
        · rfl
  map_smul' scalar state := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
            massSquared).map_smul _ _
        · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The existing smooth core inserted into the equivalent L2 chart. -/
def extendedBulkL2SmoothEmbedding
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
      GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis :=
  (extendedBulkL2Equiv period hPeriod metric massSquared data analysis
    ).symm.toLinearMap.comp
      (extendedBulkSmoothEmbedding period hPeriod metric massSquared data
        analysis)

theorem extendedBulkL2SmoothEmbedding_injective
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
      (extendedBulkL2SmoothEmbedding period hPeriod metric massSquared data
        analysis) :=
  (extendedBulkL2Equiv period hPeriod metric massSquared data analysis
    ).symm.injective.comp
      (extendedBulkSmoothEmbedding_injective period hPeriod metric massSquared
        data analysis)

theorem extendedBulkL2SmoothEmbedding_denseRange
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
      (extendedBulkL2SmoothEmbedding period hPeriod metric massSquared data
        analysis) := by
  have hBack :=
    ((extendedBulkL2Equiv period hPeriod metric massSquared data analysis
      ).symm.surjective.denseRange).comp
      (extendedBulkSmoothEmbedding_denseRange period hPeriod metric massSquared
        data analysis)
      (extendedBulkL2Equiv period hPeriod metric massSquared data analysis
        ).symm.continuous
  simpa [extendedBulkL2SmoothEmbedding, Function.comp_def] using hBack

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

/-- The unchanged extended-bulk Hessian transported to the L2 Hilbert chart. -/
def extendedBulkL2Hessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  pullbackRealBilinear
    (legacyExtendedBulkNormedSpace period hPeriod metric massSquared data
      analysis)
    (inferInstance : NormedSpace Real
      (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis))
    (extendedBulkHessianCLM period hPeriod metric massSquared data analysis)
    (extendedBulkL2Equiv period hPeriod metric massSquared data analysis)

@[simp]
theorem extendedBulkL2Hessian_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod
      metric massSquared data analysis) :
    extendedBulkL2Hessian period hPeriod metric massSquared data analysis
        first second =
      extendedBulkHessian period hPeriod metric massSquared data analysis
        (extendedBulkL2Equiv period hPeriod metric massSquared data analysis
          first)
        (extendedBulkL2Equiv period hPeriod metric massSquared data analysis
          second) :=
  rfl

theorem extendedBulkL2Hessian_comm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod
      metric massSquared data analysis) :
    extendedBulkL2Hessian period hPeriod metric massSquared data analysis
        first second =
      extendedBulkL2Hessian period hPeriod metric massSquared data analysis
        second first :=
  extendedBulkHessianCLM_comm period hPeriod metric massSquared data analysis
    _ _

private theorem l2SymmetricQuadratic_hasFDerivAt
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

/-- Exact quadratic extended-bulk action in the equivalent L2 chart. -/
def extendedBulkL2Action
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis) : Real :=
  (1 / 2 : Real) *
    extendedBulkL2Hessian period hPeriod metric massSquared data analysis
      state state

theorem extendedBulkL2Action_eq_legacy
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis) :
    extendedBulkL2Action period hPeriod metric massSquared data analysis state =
      extendedBulkAction period hPeriod metric massSquared data analysis
        (extendedBulkL2Equiv period hPeriod metric massSquared data analysis
          state) := by
  unfold extendedBulkL2Action extendedBulkAction
  rw [extendedBulkL2Hessian_apply]

theorem extendedBulkL2Action_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis) :
    HasFDerivAt
      (extendedBulkL2Action period hPeriod metric massSquared data analysis)
      (extendedBulkL2Hessian period hPeriod metric massSquared data analysis
        state)
      state := by
  unfold extendedBulkL2Action
  exact @l2SymmetricQuadratic_hasFDerivAt
    (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis)
    inferInstance
    (l2ExtendedBulkNormedSpace period hPeriod metric massSquared data analysis)
    (extendedBulkL2Hessian period hPeriod metric massSquared data analysis)
    (extendedBulkL2Hessian_comm period hPeriod metric massSquared data analysis)
    state

/-- The first-variation field is linear, with constant derivative equal to the
same Hessian.  Together with `extendedBulkL2Action_hasFDerivAt`, this is the
second Fréchet variation without normalizing the global `fderiv` choice. -/
theorem extendedBulkL2Action_hasSecondFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (base : GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis) :
    HasFDerivAt
      (extendedBulkL2Hessian period hPeriod metric massSquared data analysis)
      (extendedBulkL2Hessian period hPeriod metric massSquared data analysis)
      base :=
  (extendedBulkL2Hessian period hPeriod metric massSquared data analysis
    ).hasFDerivAt

theorem extendedBulkL2Action_contDiff_two
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
      (extendedBulkL2Action period hPeriod metric massSquared data analysis) := by
  unfold extendedBulkL2Action
  fun_prop

theorem extendedBulkL2Action_smoothCore_eq_legacy
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAAbelianExtendedBulkSmoothCore period hPeriod
      analysis) :
    extendedBulkL2Action period hPeriod metric massSquared data analysis
        (extendedBulkL2SmoothEmbedding period hPeriod metric massSquared data
          analysis core) =
      extendedBulkAction period hPeriod metric massSquared data analysis
        (extendedBulkSmoothEmbedding period hPeriod metric massSquared data
          analysis core) := by
  rw [extendedBulkL2Action_eq_legacy]
  simp [extendedBulkL2SmoothEmbedding]

/-- Bounded Riesz representative of the exact same-action extended bulk
Hessian on the genuine L2 product. -/
def extendedBulkL2RieszOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis :=
  @InnerProductSpace.continuousLinearMapOfBilin
    Real
    (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis)
    inferInstance inferInstance
    (l2ExtendedBulkInnerProductSpace period hPeriod metric massSquared data
      analysis)
    (l2ExtendedBulkCompleteSpace period hPeriod metric massSquared data
      analysis)
    (extendedBulkL2Hessian period hPeriod metric massSquared data analysis)

theorem extendedBulkL2RieszOperator_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod
      metric massSquared data analysis) :
    inner Real
        (extendedBulkL2RieszOperator period hPeriod metric massSquared data
          analysis first) second =
      extendedBulkL2Hessian period hPeriod metric massSquared data analysis
        first second := by
  exact @InnerProductSpace.continuousLinearMapOfBilin_apply
    Real
    (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis)
    inferInstance inferInstance
    (l2ExtendedBulkInnerProductSpace period hPeriod metric massSquared data
      analysis)
    (l2ExtendedBulkCompleteSpace period hPeriod metric massSquared data
      analysis)
    (extendedBulkL2Hessian period hPeriod metric massSquared data analysis)
    first second

/-- The bounded same-action Hessian representative is self-adjoint on the
complete L2 product graph. -/
theorem extendedBulkL2RieszOperator_isSelfAdjoint
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    @IsSelfAdjoint
      (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis →L[Real]
        GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis)
      (@ContinuousLinearMap.instStarId
        Real
        (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis)
        inferInstance inferInstance
        (l2ExtendedBulkInnerProductSpace period hPeriod metric massSquared data
          analysis)
        (l2ExtendedBulkCompleteSpace period hPeriod metric massSquared data
          analysis))
      (extendedBulkL2RieszOperator period hPeriod metric massSquared data
        analysis) := by
  apply (@ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
    Real
    (GlobalCandidateAAbelianExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis)
    inferInstance inferInstance
    (l2ExtendedBulkInnerProductSpace period hPeriod metric massSquared data
      analysis)
    (l2ExtendedBulkCompleteSpace period hPeriod metric massSquared data
      analysis)
    (extendedBulkL2RieszOperator period hPeriod metric massSquared data
      analysis)).2
  intro first second
  change inner Real
      (extendedBulkL2RieszOperator period hPeriod metric massSquared data
        analysis first) second =
    inner Real first
      (extendedBulkL2RieszOperator period hPeriod metric massSquared data
        analysis second)
  calc
    _ = extendedBulkL2Hessian period hPeriod metric massSquared data analysis
          first second :=
      extendedBulkL2RieszOperator_pairing period hPeriod metric massSquared
        data analysis first second
    _ = extendedBulkL2Hessian period hPeriod metric massSquared data analysis
          second first :=
      extendedBulkL2Hessian_comm period hPeriod metric massSquared data
        analysis first second
    _ = inner Real
          (extendedBulkL2RieszOperator period hPeriod metric massSquared data
            analysis second) first :=
      (extendedBulkL2RieszOperator_pairing period hPeriod metric massSquared
        data analysis second first).symm
    _ = _ := real_inner_comm _ _

end
end P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
end JanusFormal
