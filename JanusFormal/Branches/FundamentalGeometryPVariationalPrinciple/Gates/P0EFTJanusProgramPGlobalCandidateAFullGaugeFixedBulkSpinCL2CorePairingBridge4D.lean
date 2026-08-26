import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCTangentBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2CorePairing4D

/-!
# Gauge-fixed bulk core and the diagonal L2 pairing

The gauge-fixed bulk-plus-SpinC source is only a reassociation of the four
factors in the regrouped diagonal bulk core.  This file exposes the resulting
linear equivalence and pulls the faithful Candidate-A L2 pairing back across
it.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCL2CorePairingBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCTangentBridge4D
open P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Bilinear4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2CorePairing4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance (priority := 40000) pulledBackCoreMatterInnerProductSpace
    (massSquared : Real) :
    InnerProductSpace Real
      (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared) :=
  coreMatterInnerProductSpace period hPeriod massSquared

local instance (priority := 40000) pulledBackCoreLLInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  coreLLInnerProductSpace period hPeriod data analysis

local instance (priority := 40000) pulledBackCoreLLNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  coreLLNormedSpace period hPeriod data analysis

local instance (priority := 40000) pulledBackCoreLLModule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  coreLLModule period hPeriod data analysis

/-- Canonical reassociation
`(diffeomorphism × (Abelian × LL)) × SpinC`
with `(diffeomorphism × Abelian) × (SpinC × LL)`. -/
def globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod analysis ≃ₗ[Real]
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data
        analysis where
  toFun core := ((core.1.1, core.1.2.1), (core.2, core.1.2.2))
  invFun core := ((core.1.1, (core.1.2, core.2.2)), core.2.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
        period hPeriod data analysis core =
      ((core.1.1, core.1.2.1), (core.2, core.1.2.2)) :=
  rfl

/-- Underlying canonical linear map, for APIs that do not need the inverse. -/
def globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod analysis →ₗ[Real]
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data
        analysis :=
  (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
    period hPeriod data analysis).toLinearMap

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulk_diffeomorphism
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearMap
      period hPeriod data analysis core).1.1 = core.1.1 :=
  rfl

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulk_abelian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearMap
      period hPeriod data analysis core).1.2 = core.1.2.1 :=
  rfl

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulk_spinC
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearMap
      period hPeriod data analysis core).2.1 = core.2 :=
  rfl

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulk_ll
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearMap
      period hPeriod data analysis core).2.2 = core.1.2.2 :=
  rfl

theorem globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulk_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearMap
        period hPeriod data analysis) :=
  (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
    period hPeriod data analysis).injective

theorem globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulk_surjective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Surjective
      (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearMap
        period hPeriod data analysis) :=
  (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
    period hPeriod data analysis).surjective

/-- Candidate-A L2 pairing pulled back to the gauge-fixed bulk-plus-SpinC
source. -/
def globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) : Real :=
  diagonalExtendedBulkL2CoreInner period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
    (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
      period hPeriod data analysis first)
    (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
      period hPeriod data analysis second)

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
        analysis first second =
      diagonalExtendedBulkL2CoreInner period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        ((first.1.1, first.1.2.1), (first.2, first.1.2.2))
      ((second.1.1, second.1.2.1), (second.2, second.1.2.2)) :=
  rfl

/-- Hilbert realization of the pulled-back bulk pairing. -/
theorem globalCandidateAFullGaugeFixedBulkSpinCDiagonalL2SmoothEmbedding_inner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    @inner Real
        (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis)
        (diagonalL2ExtendedBulkInnerProductSpace period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis).toInner
        (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
          period hPeriod (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis
          (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
            period hPeriod data analysis first))
        (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
          period hPeriod (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis
          (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
            period hPeriod data analysis second)) =
      globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
        analysis first second := by
  rw [diagonalExtendedBulkL2SmoothEmbedding_inner]
  rfl

theorem globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_symm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
        analysis first second =
      globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
        analysis second first := by
  rcases first with ⟨⟨firstDiffeomorphism, ⟨firstAbelian, firstLL⟩⟩,
    firstSpinC⟩
  rcases second with ⟨⟨secondDiffeomorphism, ⟨secondAbelian, secondLL⟩⟩,
    secondSpinC⟩
  simp only [globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_apply]
  unfold diagonalExtendedBulkL2CoreInner
  congr 1
  · congr 1
    · congr 1
      · exact real_inner_comm _ _
      · exact real_inner_comm _ _
    · exact real_inner_comm _ _
  · exact real_inner_comm _ _

theorem globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_add_left
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second third : GlobalCandidateAFullGaugeFixedBulkSpinCCore
      period hPeriod analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
        analysis (first + second) third =
      globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
          analysis first third +
        globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
          analysis second third := by
  rw [← globalCandidateAFullGaugeFixedBulkSpinCDiagonalL2SmoothEmbedding_inner,
    ← globalCandidateAFullGaugeFixedBulkSpinCDiagonalL2SmoothEmbedding_inner,
    ← globalCandidateAFullGaugeFixedBulkSpinCDiagonalL2SmoothEmbedding_inner]
  rw [(globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
    period hPeriod data analysis).map_add]
  rw [(P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis).map_add]
  exact
    @inner_add_left Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis)
      inferInstance
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis)
        (diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis))
      (diagonalL2ExtendedBulkInnerProductSpace period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis) _ _ _

theorem globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_smul_left
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (scalar : Real)
    (first second : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
        analysis (scalar • first) second =
      scalar * globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod
        data analysis first second := by
  rw [← globalCandidateAFullGaugeFixedBulkSpinCDiagonalL2SmoothEmbedding_inner,
    ← globalCandidateAFullGaugeFixedBulkSpinCDiagonalL2SmoothEmbedding_inner]
  rw [(globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
    period hPeriod data analysis).map_smul]
  rw [(P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis).map_smul]
  exact
    @real_inner_smul_left
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis)
      (@NormedAddCommGroup.toSeminormedAddCommGroup
        (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis)
        (diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis))
      (diagonalL2ExtendedBulkInnerProductSpace period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis) _ _ scalar

theorem globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_self_nonneg
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    0 ≤ globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
      analysis core core := by
  rcases core with ⟨⟨diffeomorphism, ⟨abelian, ll⟩⟩, spinC⟩
  simp only [globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_apply]
  unfold diagonalExtendedBulkL2CoreInner
  exact add_nonneg
    (add_nonneg
      (add_nonneg real_inner_self_nonneg real_inner_self_nonneg)
      real_inner_self_nonneg)
    real_inner_self_nonneg

theorem globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner_self_eq_zero_iff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
        analysis core core = 0 ↔
      core = 0 := by
  unfold globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner
  rw [diagonalExtendedBulkL2CoreInner_self_eq_zero_iff]
  exact
    (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
      period hPeriod data analysis).map_eq_zero_iff

end
end P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCL2CorePairingBridge4D
end JanusFormal
