namespace JanusFormal
namespace P0EFTJanusBimetricRhoEffPlusSourceContractGate

set_option autoImplicit false

structure BimetricRhoEffPlusSourceContractGate where
  M15CoupledEquationsAvailable : Prop
  DeterminantRatioFactorAvailable : Prop
  PlusSectorGeodesicClockAvailable : Prop
  SignedEnergyConservationAvailable : Prop
  RhoEffPlusFormulaDeclared : Prop
  RhoPlusRadiationComponentDerived : Prop
  RhoPlusBaryonComponentDerived : Prop
  RhoMinusProjectionComponentDerived : Prop
  PredragScalingDerived : Prop

def SourceContractClosed
    (g : BimetricRhoEffPlusSourceContractGate) : Prop :=
  g.M15CoupledEquationsAvailable /\
  g.DeterminantRatioFactorAvailable /\
  g.PlusSectorGeodesicClockAvailable /\
  g.SignedEnergyConservationAvailable /\
  g.RhoEffPlusFormulaDeclared

def ActivePredragSourceClosed
    (g : BimetricRhoEffPlusSourceContractGate) : Prop :=
  SourceContractClosed g /\
  g.RhoPlusRadiationComponentDerived /\
  g.RhoPlusBaryonComponentDerived /\
  g.RhoMinusProjectionComponentDerived /\
  g.PredragScalingDerived

def SourceContractFrontier
    (g : BimetricRhoEffPlusSourceContractGate) : Prop :=
  SourceContractClosed g /\
  Not g.RhoPlusRadiationComponentDerived /\
  Not g.RhoPlusBaryonComponentDerived /\
  Not g.RhoMinusProjectionComponentDerived /\
  Not g.PredragScalingDerived

theorem source_contract_does_not_close_predrag_source
    (g : BimetricRhoEffPlusSourceContractGate)
    (hFrontier : SourceContractFrontier g) :
    Not (ActivePredragSourceClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusBimetricRhoEffPlusSourceContractGate
end JanusFormal
