import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularMetricFrameNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

/-! The legacy Candidate-A datum demands an impossible global tangent frame.
The intrinsic Lorentz metric itself exists on the same quotient. -/
namespace JanusFormal.P0EFTJanusProgramPT12CandidateAFrameInputAudit4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPT12RegularMetricFrameNoGo4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The global regular-frame requirement already makes the legacy action datum empty. -/
theorem globalCandidateAActionData_isEmpty
    (configuration : GlobalFieldConfiguration period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (NonNullFace NullFace : Type*)
    [Fintype NonNullFace] [Fintype NullFace] :
    IsEmpty (GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) := by
  constructor
  intro data
  exact (regularGeneralLorentzMetric_isEmpty period hPeriod).false
    data.plusGravity.metric

/-- Intrinsic Lorentz geometry remains inhabited without the global-frame requirement. -/
theorem smoothGeneralLorentzMetric_nonempty :
    Nonempty (SmoothGeneralLorentzMetric period hPeriod) :=
  ⟨intrinsicSmoothGeneralLorentzMetric period hPeriod⟩

end
end JanusFormal.P0EFTJanusProgramPT12CandidateAFrameInputAudit4D
