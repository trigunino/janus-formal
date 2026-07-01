import JanusFormal.P0EFTJanusZ4CobayaPlanckChannelGate

namespace JanusFormal
namespace P0EFTJanusZ4OfficialPlanckGate

set_option autoImplicit false

structure OfficialPlanckGate where
  nativeZ4SpectraUsed : Prop
  lowlTTExecuted : Prop
  lowlEEExecuted : Prop
  lensingExecuted : Prop
  highlTTExecuted : Prop
  highlTTTEEEExecuted : Prop
  compressedLCDMParametersNotUsed : Prop
  observationalGatePassed : Prop

def officialPlanckGateExecuted (g : OfficialPlanckGate) : Prop :=
  g.nativeZ4SpectraUsed /\
  g.lowlTTExecuted /\
  g.lowlEEExecuted /\
  g.lensingExecuted /\
  g.highlTTExecuted /\
  g.highlTTTEEEExecuted /\
  g.compressedLCDMParametersNotUsed

def officialPlanckGateAccepted (g : OfficialPlanckGate) : Prop :=
  officialPlanckGateExecuted g /\
  g.observationalGatePassed

theorem official_gate_execution_does_not_imply_acceptance
    (g : OfficialPlanckGate)
    (_h : officialPlanckGateExecuted g)
    (hRejected : Not g.observationalGatePassed) :
    Not (officialPlanckGateAccepted g) := by
  intro h
  exact hRejected h.right

end P0EFTJanusZ4OfficialPlanckGate
end JanusFormal
