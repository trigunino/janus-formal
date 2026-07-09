import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4NonzeroPlanckEligibilityGate

namespace JanusFormal
namespace P0EFTJanusZ4OfficialPlanckLensingShapeDeltaTrial

set_option autoImplicit false

structure OfficialPlanckLensingShapeDeltaTrial where
  eligibilityGatePassed : Prop
  cambGRPlusZ4DeltaBackend : Prop
  onlyWeylLensingShapeDeltaEnabled : Prop
  nativeToyLOSUsed : Prop
  fullNativeZ4SolverUsed : Prop
  officialLikelihoodRequested : Prop
  officialLikelihoodExecuted : Prop
  planckSuccessVerdict : Prop

def controlledTrialReady (t : OfficialPlanckLensingShapeDeltaTrial) : Prop :=
  t.eligibilityGatePassed /\
  t.cambGRPlusZ4DeltaBackend /\
  t.onlyWeylLensingShapeDeltaEnabled /\
  Not t.nativeToyLOSUsed /\
  Not t.fullNativeZ4SolverUsed

theorem controlled_trial_may_request_likelihood
    (t : OfficialPlanckLensingShapeDeltaTrial)
    (hPolicy : controlledTrialReady t -> t.officialLikelihoodRequested)
    (h : controlledTrialReady t) :
    t.officialLikelihoodRequested := by
  exact hPolicy h

theorem trial_execution_is_not_success_verdict
    (t : OfficialPlanckLensingShapeDeltaTrial)
    (hNoVerdict : Not t.planckSuccessVerdict) :
    Not t.planckSuccessVerdict := by
  exact hNoVerdict

end P0EFTJanusZ4OfficialPlanckLensingShapeDeltaTrial
end JanusFormal
