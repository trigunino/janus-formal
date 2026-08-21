import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D

/-!
# Faithful pairing on the regrouped diagonal bulk core

This identifies the componentwise pairing of the regrouped smooth core with
the genuine nested-L2 inner product and derives nondegeneracy from the already
proved faithful Hilbert embedding.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2CorePairing4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped InnerProductSpace ENNReal
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Bilinear4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Reassociation loses no smooth field coordinate. -/
theorem diagonalExtendedBulkSmoothCoreToLegacy_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (diagonalExtendedBulkSmoothCoreToLegacy period hPeriod data analysis) := by
  intro first second hEqual
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (fun value => value.1) hEqual
    · exact congrArg (fun value => value.2.1) hEqual
  · apply Prod.ext
    · exact congrArg (fun value => value.2.2.1) hEqual
    · exact congrArg (fun value => value.2.2.2) hEqual

/-- The regrouped core remains faithful in the genuine L2 completion. -/
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
      (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
        period hPeriod metric massSquared data analysis) :=
  (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalExtendedBulkL2SmoothEmbedding_injective
      period hPeriod metric massSquared data analysis).comp
    (diagonalExtendedBulkSmoothCoreToLegacy_injective period hPeriod data
      analysis)

@[simp]
theorem diagonalExtendedBulkL2SmoothEmbedding_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data
      analysis) :
    P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
        period hPeriod metric massSquared data analysis core =
      WithLp.toLp 2
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
            hPeriod metric core.1.1,
          WithLp.toLp 2
            (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
                core.1.2,
              WithLp.toLp 2
                ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
                    massSquared).symm
                    (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period
                      hPeriod massSquared core.2.1),
                  globalCandidateAFullLLSmoothEmbedding period hPeriod data
                    analysis core.2.2))) := by
  rfl

/-- The explicit four-block formula is the pullback of the actual Hilbert
inner product, not an independent pairing. -/
theorem diagonalExtendedBulkL2SmoothEmbedding_inner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod data analysis) :
    @inner Real
        (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis)
        (diagonalL2ExtendedBulkInnerProductSpace period hPeriod metric
          massSquared data analysis).toInner
        (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
          period hPeriod metric massSquared data analysis first)
        (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
          period hPeriod metric massSquared data analysis second) =
      diagonalExtendedBulkL2CoreInner period hPeriod metric massSquared data
        analysis first second := by
  rw [diagonalExtendedBulkL2SmoothEmbedding_apply period hPeriod metric
      massSquared data analysis first,
    diagonalExtendedBulkL2SmoothEmbedding_apply period hPeriod metric
      massSquared data analysis second]
  rw [@WithLp.prod_inner_apply Real
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
      metric) _ inferInstance
    (diagonalL2DiffeomorphismNormedAddCommGroup period hPeriod metric)
    (diagonalL2DiffeomorphismInnerProductSpace period hPeriod metric)
    inferInstance
    (diagonalL2AbelianTailInnerProductSpace period hPeriod metric massSquared
      data analysis)]
  rw [@WithLp.prod_inner_apply Real
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) _
    inferInstance inferInstance
    (diagonalL2AbelianInnerProductSpace period hPeriod metric)
    inferInstance
    (diagonalL2MatterLLInnerProductSpace period hPeriod massSquared data
      analysis)]
  rw [@WithLp.prod_inner_apply Real
    (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared)
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    inferInstance inferInstance
    (diagonalL2MatterInnerProductSpace period hPeriod massSquared)
    inferInstance
    (diagonalL2LLInnerProductSpace period hPeriod data analysis)]
  unfold diagonalExtendedBulkL2CoreInner
  ring

/-- The integrated common-core pairing is nondegenerate on the actual smooth
fields, including the distinct BRST `c/cbar/B` coordinates. -/
theorem diagonalExtendedBulkL2CoreInner_self_eq_zero_iff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data
      analysis) :
    diagonalExtendedBulkL2CoreInner period hPeriod metric massSquared data
        analysis core core = 0 ↔
      core = 0 := by
  rw [← diagonalExtendedBulkL2SmoothEmbedding_inner period hPeriod metric
    massSquared data analysis core core]
  constructor
  · intro hZero
    have hImage :
        P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
            period hPeriod metric massSquared data analysis core = 0 :=
      (@inner_self_eq_zero Real
        (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis)
        inferInstance
        (diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod metric massSquared data
          analysis)
        (diagonalL2ExtendedBulkInnerProductSpace period hPeriod metric massSquared data
          analysis)).mp hZero
    apply diagonalExtendedBulkL2SmoothEmbedding_injective period hPeriod metric
      massSquared data analysis
    simpa using hImage
  · rintro rfl
    exact
      (@inner_self_eq_zero Real
        (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
          massSquared data analysis)
        inferInstance
        (diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod metric massSquared data
          analysis)
        (diagonalL2ExtendedBulkInnerProductSpace period hPeriod metric massSquared data
          analysis)).2
        (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
          period hPeriod metric massSquared data analysis).map_zero

end
end P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2CorePairing4D
end JanusFormal
