import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnomalyFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCandidateSchemeFreedomAudit
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusQuillenFamilyCanonicity

/-!
# Exact frontier and no-go for global scheme independence

Flat compatibility plus PT anomaly cancellation does not select a unique
Candidate-A scheme.  Even a fixed Quillen line admits distinct renormalized
scalar actions after finite local shifts.

Consequently `SCHEME-GLOBAL-01` cannot be closed from the current effective
Program-P assumptions alone.  Microscopic normalization and finite-part data
are required; they are not introduced here as axioms.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalSchemeFrontier4D

set_option autoImplicit false

open P0EFTJanusCandidateSchemeFreedomAudit
open P0EFTJanusQuillenFamilyCanonicity

/-- Constructive witnesses that the current assumptions leave genuine scheme
freedom. -/
structure ProgramPGlobalSchemeNoGoCertificate4D where
  candidateANotUnique :
    ¬ ∀ first second : CandidateASchemeParameters,
      CandidateAAnomalyFlatAdmissible first →
      CandidateAAnomalyFlatAdmissible second →
      first = second
  quillenScalarActionNotUnique :
    ∃ first second : RenormalizedSectionChoices,
      first ≠ second ∧
      renormalizedActionValue 1 first ≠
        renormalizedActionValue 1 second
  finiteEvenShiftWitness :
    baselineCandidateA.finiteEvenCounterterm ≠
      finiteShiftCandidateA.finiteEvenCounterterm
  normalizationShiftWitness :
    baselineCandidateA.overallActionNormalization ≠
      normalizationShiftCandidateA.overallActionNormalization

def programPGlobalSchemeNoGoCertificate4D :
    ProgramPGlobalSchemeNoGoCertificate4D where
  candidateANotUnique :=
    anomaly_cancellation_alone_cannot_fix_candidateA_scheme
  quillenScalarActionNotUnique :=
    quillen_line_does_not_fix_renormalized_action
  finiteEvenShiftWitness := by
    norm_num [baselineCandidateA, finiteShiftCandidateA]
  normalizationShiftWitness := by
    norm_num [baselineCandidateA, normalizationShiftCandidateA]

theorem global_scheme_frontier_gate :
    Nonempty ProgramPGlobalSchemeNoGoCertificate4D :=
  ⟨programPGlobalSchemeNoGoCertificate4D⟩

/-- A Quillen package without microscopic finite parts is insufficient for
scheme-independent predictivity. -/
theorem global_scheme_missing_finite_parts_blocks_predictivity
    (status : QuillenPredictivityStatus)
    (hMissing : ¬ status.finiteCountertermsFixedMicroscopically) :
    ¬ quillenPredictivityClosed status :=
  quillen_without_finite_parts_blocks_predictivity status hMissing

end P0EFTJanusProgramPGlobalSchemeFrontier4D
end JanusFormal
