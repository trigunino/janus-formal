namespace JanusFormal
namespace P0EFTJanusNonThroatWeylCuspFinalFrontierGate

set_option autoImplicit false

structure NonThroatWeylCuspFinalFrontierGate where
  WeylCuspRedshiftDomainClosed : Prop
  GPlusVisibleKinematicsClosed : Prop
  S4RP4HatConformalBackgroundClosed : Prop
  BimetricSourceContractClosed : Prop
  GlobalConservationOmegaRelationClosed : Prop
  Projection00ChoiceClosed : Prop
  AbsoluteLOrEGlobalDerived : Prop
  LorentzianTimeSlicingDerived : Prop
  PredragSourceScalingsDerived : Prop
  OmegaBoundaryConditionDerived : Prop

def ClosedContracts
    (g : NonThroatWeylCuspFinalFrontierGate) : Prop :=
  g.WeylCuspRedshiftDomainClosed /\
  g.GPlusVisibleKinematicsClosed /\
  g.S4RP4HatConformalBackgroundClosed /\
  g.BimetricSourceContractClosed /\
  g.GlobalConservationOmegaRelationClosed /\
  g.Projection00ChoiceClosed

def PredictiveOmegaSolution
    (g : NonThroatWeylCuspFinalFrontierGate) : Prop :=
  ClosedContracts g /\
  g.AbsoluteLOrEGlobalDerived /\
  g.LorentzianTimeSlicingDerived /\
  g.PredragSourceScalingsDerived /\
  g.OmegaBoundaryConditionDerived

def FinalFrontier
    (g : NonThroatWeylCuspFinalFrontierGate) : Prop :=
  ClosedContracts g /\
  Not g.AbsoluteLOrEGlobalDerived /\
  Not g.LorentzianTimeSlicingDerived /\
  Not g.PredragSourceScalingsDerived /\
  Not g.OmegaBoundaryConditionDerived

theorem final_frontier_blocks_predictive_omega
    (g : NonThroatWeylCuspFinalFrontierGate)
    (hFrontier : FinalFrontier g) :
    Not (PredictiveOmegaSolution g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusNonThroatWeylCuspFinalFrontierGate
end JanusFormal
