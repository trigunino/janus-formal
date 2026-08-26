import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Completion4D

/-!
# Terminal T01 certificate for the global foundations and pairings

The certificate uses one shared-metric smooth core throughout.  It records its
faithful gauge-fixed tangent realization, its positive nondegenerate common
pairing and its dense isometric inclusion into the intrinsic Hilbert
completion.  No map from the completion back to smooth fields is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT01GlobalFoundationsPairingsTerminalCertificate4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricTangent4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Pairing4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Completion4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Concrete terminal `T01` certificate on one canonical shared core.  Every
field is a property of an implemented map or pairing, not a supplied business
premise. -/
structure ProgramPT01GlobalFoundationsPairingsCertificate4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Prop where
  sharedMetric_agreement :
    ∀ core :
        GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
          period hPeriod analysis,
      core.1.1.1.1.1.metricPerturbation = fun _ ↦ core.1.2.1
  tangent_injective :
    Function.Injective
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod configuration data analysis)
  pairing_self_nonneg :
    ∀ core :
        GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
          period hPeriod analysis,
      0 ≤
        globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
          period hPeriod configuration data analysis core core
  pairing_self_eq_zero_iff :
    ∀ core :
        GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
          period hPeriod analysis,
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
          period hPeriod configuration data analysis core core = 0 ↔
        core = 0
  completion_inner :
    ∀ first second :
        GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
          period hPeriod analysis,
      inner Real
          (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion
            period hPeriod configuration data analysis first)
          (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion
            period hPeriod configuration data analysis second) =
        globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
          period hPeriod configuration data analysis first second
  completion_injective :
    Function.Injective
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion
        period hPeriod configuration data analysis)
  completion_denseRange :
    DenseRange
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion
        period hPeriod configuration data analysis)
  completion_complete :
    CompleteSpace
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Completion
        period hPeriod configuration data analysis)

/-- Public terminal `T01` theorem.  It assembles only already implemented
global objects and discharges every certificate field canonically. -/
theorem program_p_t01_global_foundations_pairings_terminal_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    ProgramPT01GlobalFoundationsPairingsCertificate4D period hPeriod
      configuration data analysis where
  sharedMetric_agreement :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_agreement
      period hPeriod analysis
  tangent_injective :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_injective
      period hPeriod configuration data analysis
  pairing_self_nonneg :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_self_nonneg
      period hPeriod configuration data analysis
  pairing_self_eq_zero_iff :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_self_eq_zero_iff
      period hPeriod configuration data analysis
  completion_inner :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion_inner
      period hPeriod configuration data analysis
  completion_injective :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion_injective
      period hPeriod configuration data analysis
  completion_denseRange :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricToL2Completion_denseRange
      period hPeriod configuration data analysis
  completion_complete :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2CompletionCompleteSpace
      period hPeriod configuration data analysis

end
end P0EFTJanusProgramPT01GlobalFoundationsPairingsTerminalCertificate4D
end JanusFormal
