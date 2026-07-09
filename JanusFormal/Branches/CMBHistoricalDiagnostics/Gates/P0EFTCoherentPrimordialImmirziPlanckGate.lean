namespace JanusFormal
namespace P0EFTCoherentPrimordialImmirziPlanckGate

set_option autoImplicit false

structure CoherentPrimordialImmirziPlanckGate where
  coherentHookActivated : Prop
  rawPlanckLikelihoodUsed : Prop
  planckDeltaAccepted : Prop

def coherentPlanckGateRun (g : CoherentPrimordialImmirziPlanckGate) : Prop :=
  g.coherentHookActivated /\ g.rawPlanckLikelihoodUsed

def coherentPlanckNoFitReady (g : CoherentPrimordialImmirziPlanckGate) : Prop :=
  coherentPlanckGateRun g /\ g.planckDeltaAccepted

theorem raw_planck_rejection_blocks_no_fit
    (g : CoherentPrimordialImmirziPlanckGate)
    (hRejected : Not g.planckDeltaAccepted) :
    Not (coherentPlanckNoFitReady g) := by
  intro h
  exact hRejected h.right

end P0EFTCoherentPrimordialImmirziPlanckGate
end JanusFormal
