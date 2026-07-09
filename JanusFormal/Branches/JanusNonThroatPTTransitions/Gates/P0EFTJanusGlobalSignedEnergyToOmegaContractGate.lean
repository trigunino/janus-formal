namespace JanusFormal
namespace P0EFTJanusGlobalSignedEnergyToOmegaContractGate

set_option autoImplicit false

structure GlobalSignedEnergyToOmegaContractGate where
  PublishedSignedEnergyConservationAvailable : Prop
  APlusWeylRelationAvailable : Prop
  OmegaAlgebraicRelationDeclared : Prop
  GlobalEnergyConstantDerived : Prop
  MinusSectorHistoryDerived : Prop
  PlusSectorPredragDensityDerived : Prop
  VariableCLawTiedToWeylCusp : Prop

def AlgebraicContractClosed
    (g : GlobalSignedEnergyToOmegaContractGate) : Prop :=
  g.PublishedSignedEnergyConservationAvailable /\
  g.APlusWeylRelationAvailable /\
  g.OmegaAlgebraicRelationDeclared

def OmegaFixedByConservation
    (g : GlobalSignedEnergyToOmegaContractGate) : Prop :=
  AlgebraicContractClosed g /\
  g.GlobalEnergyConstantDerived /\
  g.MinusSectorHistoryDerived /\
  g.PlusSectorPredragDensityDerived /\
  g.VariableCLawTiedToWeylCusp

def ConservationOmegaFrontier
    (g : GlobalSignedEnergyToOmegaContractGate) : Prop :=
  AlgebraicContractClosed g /\
  Not g.GlobalEnergyConstantDerived /\
  Not g.MinusSectorHistoryDerived /\
  Not g.PlusSectorPredragDensityDerived /\
  Not g.VariableCLawTiedToWeylCusp

theorem conservation_relation_does_not_fix_omega_without_state
    (g : GlobalSignedEnergyToOmegaContractGate)
    (hFrontier : ConservationOmegaFrontier g) :
    Not (OmegaFixedByConservation g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusGlobalSignedEnergyToOmegaContractGate
end JanusFormal
