import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D

/-!
# L2 Riesz realization of the diagonal Candidate-A bulk graph

The completed two-metric/one-diffeomorphism-triplet graph replaces the two
independent de Donder factors in the existing Abelian/matter/LL bulk product.
Nested `WithLp 2` products give the resulting four factors one genuine complete
real Hilbert structure.  The already proved diagonal bulk Hessian and action
are transported through the finite-product equivalence; no action block or
analytic axiom is added.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open scoped InnerProductSpace ENNReal ContDiff
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance diagonalL2CanonicalLorentzVolumeFinite :
    MeasureTheory.IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D.canonicalLorentzVolumeFinite
    period hPeriod

local instance (priority := 10001) diagonalL2DiffeomorphismNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedAddCommGroupValue
    period hPeriod metric

local instance (priority := 10001) diagonalL2DiffeomorphismContinuousAdd
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContinuousAdd
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphContinuousAdd
    period hPeriod metric

local instance (priority := 10001) diagonalL2DiffeomorphismNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphNormedSpace
    period hPeriod metric

local instance (priority := 10001) diagonalL2DiffeomorphismModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphModule
    period hPeriod metric

local instance diagonalL2DiffeomorphismInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D.diagonalGraphInnerProductSpace
    period hPeriod metric

local instance diagonalL2DiffeomorphismCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  globalCandidateADiagonalDiffeomorphismOffShellGraphCompleteSpace
    period hPeriod metric

local instance diagonalL2AbelianNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D.l2OffShellGraphNormedSpace
    period hPeriod metric

local instance diagonalL2AbelianModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D.l2OffShellGraphModule
    period hPeriod metric

local instance diagonalL2AbelianInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D.l2OffShellGraphInnerProductSpace
    period hPeriod metric

local instance diagonalL2AbelianCompleteSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D.l2OffShellGraphCompleteSpace
    period hPeriod metric

local instance diagonalL2MatterInnerProductSpace
    (massSquared : Real) :
    InnerProductSpace Real
      (ProgramPPrimitiveSpinCMatterL2GraphDomain
        period hPeriod massSquared) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D.l2MatterGraphInnerProductSpace
    period hPeriod massSquared

local instance diagonalL2MatterCompleteSpace
    (massSquared : Real) :
    CompleteSpace
      (ProgramPPrimitiveSpinCMatterL2GraphDomain
        period hPeriod massSquared) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D.l2MatterGraphCompleteSpace
    period hPeriod massSquared

local instance diagonalL2LLInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D.l2LLGraphInnerProductSpace
    period hPeriod data analysis

local instance diagonalL2LLNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (diagonalL2LLInnerProductSpace period hPeriod data analysis).toNormedSpace

local instance diagonalL2LLModule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  (diagonalL2LLNormedSpace period hPeriod data analysis).toModule

local instance diagonalL2LLCompleteSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CompleteSpace (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D.l2LLGraphCompleteSpace
    period hPeriod data analysis

private abbrev DiagonalMatterLLL2Tail
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

private abbrev DiagonalAbelianMatterLLL2Tail
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
      DiagonalMatterLLL2Tail period hPeriod massSquared data analysis)

/-- The diagonal diffeomorphism, paired Abelian, matter and LL graph factors
with genuine nested L2 product norms. -/
abbrev GlobalCandidateADiagonalExtendedBulkL2Hilbert
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
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric ×
      DiagonalAbelianMatterLLL2Tail period hPeriod metric massSquared data
        analysis)

local instance diagonalL2MatterLLInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (DiagonalMatterLLL2Tail period hPeriod massSquared data analysis) :=
  @WithLp.instProdInnerProductSpace
    Real
    (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared)
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    inferInstance inferInstance
    (diagonalL2MatterInnerProductSpace period hPeriod massSquared)
    inferInstance
    (diagonalL2LLInnerProductSpace period hPeriod data analysis)

local instance diagonalL2AbelianTailInnerProductSpace
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
      (DiagonalAbelianMatterLLL2Tail period hPeriod metric massSquared data
        analysis) :=
  @WithLp.instProdInnerProductSpace
    Real
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric)
    (DiagonalMatterLLL2Tail period hPeriod massSquared data analysis)
    inferInstance inferInstance
    (diagonalL2AbelianInnerProductSpace period hPeriod metric)
    inferInstance
    (diagonalL2MatterLLInnerProductSpace period hPeriod massSquared data
      analysis)

local instance (priority := 10030) diagonalL2ExtendedBulkNormedAddCommGroup
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
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  WithLp.instProdNormedAddCommGroup 2 _ _

local instance (priority := 10020) diagonalL2ExtendedBulkInnerProductSpace
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
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  @WithLp.instProdInnerProductSpace
    Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric)
    (DiagonalAbelianMatterLLL2Tail period hPeriod metric massSquared data
      analysis)
    inferInstance inferInstance
    (diagonalL2DiffeomorphismInnerProductSpace period hPeriod metric)
    inferInstance
    (diagonalL2AbelianTailInnerProductSpace period hPeriod metric massSquared
      data analysis)

local instance (priority := 10010) diagonalL2ExtendedBulkNormedSpace
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
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  (diagonalL2ExtendedBulkInnerProductSpace period hPeriod metric massSquared
    data analysis).toNormedSpace

local instance (priority := 10011) diagonalL2ExtendedBulkModule
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
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  (diagonalL2ExtendedBulkNormedSpace period hPeriod metric massSquared data
    analysis).toModule

local instance diagonalL2ExtendedBulkCompleteSpace
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
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) := by
  infer_instance

local instance (priority := 10002) legacyDiagonalBulkNormedSpace
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
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D.diagonalBulkNormedSpace
    period hPeriod metric massSquared data analysis

local instance (priority := 10003) legacyDiagonalBulkModule
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
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D.diagonalBulkModule
    period hPeriod metric massSquared data analysis

/-- Continuous linear equivalence between the genuine L2 product and the
finite maximum-norm diagonal bulk chart. -/
def diagonalExtendedBulkL2Equiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis ≃L[Real]
      GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis where
  toFun state :=
    (WithLp.fst state,
      (WithLp.fst (WithLp.snd state),
        (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared
            (WithLp.fst (WithLp.snd (WithLp.snd state))),
          WithLp.snd (WithLp.snd (WithLp.snd state)))))
  invFun state :=
    WithLp.toLp 2
      (state.1,
        WithLp.toLp 2
          (state.2.1,
            WithLp.toLp 2
              ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
                massSquared).symm state.2.2.1, state.2.2.2)))
  left_inv state := by
    apply WithLp.ofLp_injective 2
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

/-- The existing diagonal smooth core inserted into the equivalent L2 chart. -/
def diagonalExtendedBulkL2SmoothEmbedding
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
      GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis :=
  (diagonalExtendedBulkL2Equiv period hPeriod metric massSquared data analysis
    ).symm.toLinearMap.comp
      (diagonalExtendedBulkSmoothEmbedding period hPeriod metric massSquared
        data analysis)

theorem diagonalExtendedBulkL2SmoothEmbedding_injective
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
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
        data analysis) :=
  (diagonalExtendedBulkL2Equiv period hPeriod metric massSquared data analysis
    ).symm.injective.comp
      (diagonalExtendedBulkSmoothEmbedding_injective period hPeriod metric
        massSquared data analysis)

theorem diagonalExtendedBulkL2SmoothEmbedding_denseRange
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
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
        data analysis) := by
  have hBack :=
    ((diagonalExtendedBulkL2Equiv period hPeriod metric massSquared data
      analysis).symm.surjective.denseRange).comp
      (diagonalExtendedBulkSmoothEmbedding_denseRange period hPeriod metric
        massSquared data analysis)
      (diagonalExtendedBulkL2Equiv period hPeriod metric massSquared data
        analysis).symm.continuous
  simpa [diagonalExtendedBulkL2SmoothEmbedding, Function.comp_def] using hBack

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

/-- The exact diagonal bulk Hessian transported to the genuine L2 Hilbert
product. -/
def diagonalExtendedBulkL2Hessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis →L[Real] Real :=
  pullbackRealBilinear
    (legacyDiagonalBulkNormedSpace period hPeriod metric massSquared data
      analysis)
    (diagonalL2ExtendedBulkNormedSpace period hPeriod metric massSquared data
      analysis)
    (diagonalExtendedBulkHessian period hPeriod metric massSquared data
      analysis)
    (diagonalExtendedBulkL2Equiv period hPeriod metric massSquared data
      analysis).toContinuousLinearMap

@[simp]
theorem diagonalExtendedBulkL2Hessian_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateADiagonalExtendedBulkL2Hilbert period
      hPeriod metric massSquared data analysis) :
    diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
        analysis first second =
      diagonalExtendedBulkHessian period hPeriod metric massSquared data
        analysis
        (diagonalExtendedBulkL2Equiv period hPeriod metric massSquared data
          analysis first)
        (diagonalExtendedBulkL2Equiv period hPeriod metric massSquared data
          analysis second) :=
  rfl

theorem diagonalExtendedBulkL2Hessian_comm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateADiagonalExtendedBulkL2Hilbert period
      hPeriod metric massSquared data analysis) :
    diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
        analysis first second =
      diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
        analysis second first :=
  diagonalExtendedBulkHessian_comm period hPeriod metric massSquared data
    analysis _ _

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

/-- Exact quadratic diagonal-bulk action on the genuine L2 product. -/
def diagonalExtendedBulkL2Action
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      metric massSquared data analysis) : Real :=
  (1 / 2 : Real) *
    diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
      analysis state state

theorem diagonalExtendedBulkL2Action_eq_legacy
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      metric massSquared data analysis) :
    diagonalExtendedBulkL2Action period hPeriod metric massSquared data
        analysis state =
      diagonalExtendedBulkAction period hPeriod metric massSquared data
        analysis
        (diagonalExtendedBulkL2Equiv period hPeriod metric massSquared data
          analysis state) := by
  unfold diagonalExtendedBulkL2Action diagonalExtendedBulkAction
  rw [diagonalExtendedBulkL2Hessian_apply]

theorem diagonalExtendedBulkL2Action_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      metric massSquared data analysis) :
    HasFDerivAt
      (diagonalExtendedBulkL2Action period hPeriod metric massSquared data
        analysis)
      (diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
        analysis state)
      state := by
  unfold diagonalExtendedBulkL2Action
  exact @l2SymmetricQuadratic_hasFDerivAt
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis)
    inferInstance
    (diagonalL2ExtendedBulkNormedSpace period hPeriod metric massSquared data
      analysis)
    (diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
      analysis)
    (diagonalExtendedBulkL2Hessian_comm period hPeriod metric massSquared data
      analysis)
    state

/-- The first-variation field is linear with constant derivative equal to the
same transported Hessian. -/
theorem diagonalExtendedBulkL2Action_hasSecondFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (base : GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      metric massSquared data analysis) :
    HasFDerivAt
      (diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
        analysis)
      (diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
        analysis)
      base :=
  (diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
    analysis).hasFDerivAt

theorem diagonalExtendedBulkL2Action_contDiff_two
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
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis)
      (diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod metric
        massSquared data analysis)
      (diagonalL2ExtendedBulkNormedSpace period hPeriod metric massSquared data
        analysis)
      Real inferInstance inferInstance 2
      (diagonalExtendedBulkL2Action period hPeriod metric massSquared data
        analysis) := by
  unfold diagonalExtendedBulkL2Action
  fun_prop

theorem diagonalExtendedBulkL2Action_smoothCore_eq_legacy
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    diagonalExtendedBulkL2Action period hPeriod metric massSquared data
        analysis
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric
          massSquared data analysis core) =
      diagonalExtendedBulkAction period hPeriod metric massSquared data
        analysis
        (diagonalExtendedBulkSmoothEmbedding period hPeriod metric massSquared
          data analysis core) := by
  rw [diagonalExtendedBulkL2Action_eq_legacy]
  simp [diagonalExtendedBulkL2SmoothEmbedding]

theorem diagonalExtendedBulkL2Action_smooth_eq_BRSTAndSectorActions
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    diagonalExtendedBulkL2Action period hPeriod metric massSquared data
        analysis
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric
          massSquared data analysis core) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
          period hPeriod couplings metric core.1 +
        globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
          core.2.1 (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
            period hPeriod massSquared core.2.2.1) +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            core.2.2.2) := by
  rw [diagonalExtendedBulkL2Action_smoothCore_eq_legacy]
  exact diagonalExtendedBulkAction_smooth_eq_BRSTAndSectorActions period
    hPeriod metric massSquared data analysis core

/-- Bounded Riesz representative of the exact diagonal same-action Hessian on
the complete L2 product graph. -/
def diagonalExtendedBulkL2RieszOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis :=
  @InnerProductSpace.continuousLinearMapOfBilin
    Real
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis)
    inferInstance inferInstance
    (diagonalL2ExtendedBulkInnerProductSpace period hPeriod metric massSquared
      data analysis)
    (diagonalL2ExtendedBulkCompleteSpace period hPeriod metric massSquared data
      analysis)
    (diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
      analysis)

theorem diagonalExtendedBulkL2RieszOperator_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateADiagonalExtendedBulkL2Hilbert period
      hPeriod metric massSquared data analysis) :
    inner Real
        (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared
          data analysis first) second =
      diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
        analysis first second := by
  exact @InnerProductSpace.continuousLinearMapOfBilin_apply
    Real
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis)
    inferInstance inferInstance
    (diagonalL2ExtendedBulkInnerProductSpace period hPeriod metric massSquared
      data analysis)
    (diagonalL2ExtendedBulkCompleteSpace period hPeriod metric massSquared data
      analysis)
    (diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
      analysis)
    first second

/-- The bounded same-action Hessian representative is self-adjoint on the
complete diagonal L2 bulk graph. -/
theorem diagonalExtendedBulkL2RieszOperator_isSelfAdjoint
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
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis →L[Real]
        GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis)
      (@ContinuousLinearMap.instStarId
        Real
        (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis)
        inferInstance inferInstance
        (diagonalL2ExtendedBulkInnerProductSpace period hPeriod metric
          massSquared data analysis)
        (diagonalL2ExtendedBulkCompleteSpace period hPeriod metric massSquared
          data analysis))
      (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared
        data analysis) := by
  apply (@ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
    Real
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis)
    inferInstance inferInstance
    (diagonalL2ExtendedBulkInnerProductSpace period hPeriod metric massSquared
      data analysis)
    (diagonalL2ExtendedBulkCompleteSpace period hPeriod metric massSquared data
      analysis)
    (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared data
      analysis)).2
  intro first second
  change inner Real
      (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared
        data analysis first) second =
    inner Real first
      (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared
        data analysis second)
  calc
    _ = diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
          analysis first second :=
      diagonalExtendedBulkL2RieszOperator_pairing period hPeriod metric
        massSquared data analysis first second
    _ = diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
          analysis second first :=
      diagonalExtendedBulkL2Hessian_comm period hPeriod metric massSquared data
        analysis first second
    _ = inner Real
          (diagonalExtendedBulkL2RieszOperator period hPeriod metric
            massSquared data analysis second) first :=
      (diagonalExtendedBulkL2RieszOperator_pairing period hPeriod metric
        massSquared data analysis second first).symm
    _ = _ := real_inner_comm _ _

/-! ## Faithful typed raccord on the common dense core -/

def diagonalExtendedBulkL2GraphTypedCoreLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
      →ₗ[Real]
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis ×
        GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration) where
  toFun core :=
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis core,
      diagonalExtendedBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core)
  map_add' first second := by
    apply Prod.ext
    · exact
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis).map_add first second
    · exact
        (diagonalExtendedBulkGaugeFixedTangentLinearMap period hPeriod
          configuration data analysis).map_add first second
  map_smul' scalar core := by
    apply Prod.ext
    · exact
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis).map_smul scalar core
    · exact
        (diagonalExtendedBulkGaugeFixedTangentLinearMap period hPeriod
          configuration data analysis).map_smul scalar core

theorem diagonalExtendedBulkL2GraphTypedCoreLinearMap_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Function.Injective
      (diagonalExtendedBulkL2GraphTypedCoreLinearMap period hPeriod
        configuration data analysis) := by
  intro first second hEqual
  apply diagonalExtendedBulkL2SmoothEmbedding_injective period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
  exact congrArg Prod.fst hEqual

end
end P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
end JanusFormal
