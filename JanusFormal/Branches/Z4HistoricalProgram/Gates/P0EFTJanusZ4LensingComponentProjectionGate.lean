import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4OfficialPlanckLensingShapeDeltaTrial

namespace JanusFormal
namespace P0EFTJanusZ4LensingComponentProjectionGate

set_option autoImplicit false

structure LensingComponentProjectionGate where
  cambGRPlusZ4DeltaBackend : Prop
  amplitudeOnlyProjected : Prop
  shapeOnlyProjected : Prop
  fullDeltaProjected : Prop
  directClPatch : Prop
  nativeToyLOSUsed : Prop
  officialLikelihoodExecuted : Prop
  responseNegligible : Prop
  lensingOnlyRescuesPlanck : Prop

def projectionGateReady (g : LensingComponentProjectionGate) : Prop :=
  g.cambGRPlusZ4DeltaBackend /\
  g.amplitudeOnlyProjected /\
  g.shapeOnlyProjected /\
  g.fullDeltaProjected /\
  Not g.directClPatch /\
  Not g.nativeToyLOSUsed

theorem ready_projection_can_execute_trial
    (g : LensingComponentProjectionGate)
    (hPolicy : projectionGateReady g -> g.officialLikelihoodExecuted)
    (h : projectionGateReady g) :
    g.officialLikelihoodExecuted := by
  exact hPolicy h

theorem negligible_projection_does_not_rescue_planck
    (g : LensingComponentProjectionGate)
    (hNegligible : g.responseNegligible)
    (hPolicy : g.responseNegligible -> Not g.lensingOnlyRescuesPlanck) :
    Not g.lensingOnlyRescuesPlanck := by
  exact hPolicy hNegligible

end P0EFTJanusZ4LensingComponentProjectionGate
end JanusFormal
