import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4CandidateNuisanceForegroundPolicyGate

namespace JanusFormal
namespace P0EFTJanusZ4CandidateNuisanceSensitivityGate

set_option autoImplicit false

structure NuisanceSensitivityGate where
  lambdaFrozen : Prop
  noNewZ4Physics : Prop
  nuisancePerturbationsAppliedSymmetrically : Prop
  gainSurvivesSmallNuisancePerturbations : Prop
  gainSignStable : Prop
  teCostRemainsSmall : Prop
  eeNotDegraded : Prop
  foregroundCalibrationSensitivityReported : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def sensitivityReady (g : NuisanceSensitivityGate) : Prop :=
  g.lambdaFrozen /\
  g.noNewZ4Physics /\
  g.nuisancePerturbationsAppliedSymmetrically /\
  g.gainSurvivesSmallNuisancePerturbations /\
  g.gainSignStable /\
  g.teCostRemainsSmall /\
  g.eeNotDegraded /\
  g.foregroundCalibrationSensitivityReported /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem sensitivity_ready_passes_gate
    (g : NuisanceSensitivityGate)
    (hPolicy : sensitivityReady g -> g.gatePassed)
    (h : sensitivityReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4CandidateNuisanceSensitivityGate
end JanusFormal
