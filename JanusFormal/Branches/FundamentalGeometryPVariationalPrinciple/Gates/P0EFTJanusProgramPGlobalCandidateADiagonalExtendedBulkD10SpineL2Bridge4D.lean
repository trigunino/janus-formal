import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2CorePairing4D

/-!
# Orthogonal L2 bridge to the separate D10 spine

The D10 coefficient Hilbert space is deliberately not identified with a
smooth matter, normal or boundary field.  It is adjoined as a separate
orthogonal factor to the faithful diagonal extended-bulk L2 completion.

This file supplies only the resulting linear embeddings and pairings.  It
does not assert a geometric realization of D10 modes or a terminal Hessian
certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkD10SpineL2Bridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped InnerProductSpace ENNReal
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Bilinear4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2CorePairing4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The faithful smooth bulk core with the already completed D10 coefficient
spine retained as a distinct factor. -/
abbrev GlobalCandidateADiagonalExtendedBulkD10SpineCore4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data analysis ×
    ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod configuration.d10Completion)

/-- Hilbert direct sum of the genuine extended-bulk L2 completion and the
separate D10 coefficient completion. -/
abbrev GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  WithLp 2
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis ×
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod configuration.d10Completion))

/-- Canonical embedding `(bulk L2 embedding, identity on D10)`. -/
def globalCandidateADiagonalExtendedBulkD10SpineEmbedding
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkD10SpineCore4D period hPeriod data
        analysis ↪
      GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod
        data analysis where
  toFun state := WithLp.toLp 2
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis state.1,
      state.2)
  inj' := by
    intro first second hEqual
    have hBulk := congrArg (fun state => (WithLp.ofLp state).1) hEqual
    have hD10 := congrArg (fun state => (WithLp.ofLp state).2) hEqual
    apply Prod.ext
    · apply
        P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2CorePairing4D.diagonalExtendedBulkL2SmoothEmbedding_injective
          period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
      exact hBulk
    · exact hD10

/-- The direct-sum embedding loses neither a smooth bulk coordinate nor a D10
coefficient. -/
theorem globalCandidateADiagonalExtendedBulkD10SpineEmbedding_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateADiagonalExtendedBulkD10SpineEmbedding period hPeriod
        data analysis) :=
  (globalCandidateADiagonalExtendedBulkD10SpineEmbedding period hPeriod data
    analysis).injective

/-- The D10 coordinate of the combined Hilbert space. -/
def globalCandidateADiagonalExtendedBulkD10Coordinate
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
        analysis →
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod configuration.d10Completion) :=
  fun state => (WithLp.ofLp state).2

/-- Pure D10 section of the combined Hilbert space. -/
def globalCandidateADiagonalExtendedBulkD10Section
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod configuration.d10Completion) →
      GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
        analysis :=
  fun state => WithLp.toLp 2 (0, state)

@[simp]
theorem globalCandidateADiagonalExtendedBulkD10Coordinate_section
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (state : ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod configuration.d10Completion)) :
    globalCandidateADiagonalExtendedBulkD10Coordinate period hPeriod data
        analysis
        (globalCandidateADiagonalExtendedBulkD10Section period hPeriod data
          analysis state) =
      state := by
  rfl

/-- The pure D10 section is injective. -/
theorem globalCandidateADiagonalExtendedBulkD10Section_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateADiagonalExtendedBulkD10Section period hPeriod data
        analysis) := by
  intro first second hEqual
  have hCoordinates := congrArg
    (globalCandidateADiagonalExtendedBulkD10Coordinate period hPeriod data
      analysis) hEqual
  simpa using hCoordinates

/-- Canonical direct-sum pairing on the combined core. -/
def globalCandidateADiagonalExtendedBulkD10SpineCoreInner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second :
      GlobalCandidateADiagonalExtendedBulkD10SpineCore4D period hPeriod data
        analysis) : Real :=
  diagonalExtendedBulkL2CoreInner period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis first.1 second.1 +
    inner Real first.2 second.2

end
end P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkD10SpineL2Bridge4D
end JanusFormal
