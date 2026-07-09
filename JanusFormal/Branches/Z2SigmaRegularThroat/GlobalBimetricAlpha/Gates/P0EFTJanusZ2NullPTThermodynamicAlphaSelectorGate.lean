namespace JanusFormal
namespace P0EFTJanusZ2NullPTThermodynamicAlphaSelectorGate

set_option autoImplicit false

structure NullPTThermodynamicAlphaSelectorGate where
  nullPTBridgeContextAvailable : Prop
  provedHorizonStatus : Prop
  surfaceGravityKappaAvailable : Prop
  entropyLawDeclared : Prop
  temperatureLawDeclared : Prop
  firstLawEnergyDefinitionAvailable : Prop
  chiLLSelected : Prop

def alphaSelectorReady (g : NullPTThermodynamicAlphaSelectorGate) : Prop :=
  g.nullPTBridgeContextAvailable /\
  g.provedHorizonStatus /\
  g.surfaceGravityKappaAvailable /\
  g.entropyLawDeclared /\
  g.temperatureLawDeclared /\
  g.firstLawEnergyDefinitionAvailable /\
  g.chiLLSelected

theorem no_horizon_status_blocks_thermodynamic_selector
    (g : NullPTThermodynamicAlphaSelectorGate)
    (hMissing : Not g.provedHorizonStatus) :
    Not (alphaSelectorReady g) := by
  intro h
  exact hMissing h.2.1

theorem no_chi_selection_blocks_thermodynamic_selector
    (g : NullPTThermodynamicAlphaSelectorGate)
    (hMissing : Not g.chiLLSelected) :
    Not (alphaSelectorReady g) := by
  intro h
  exact hMissing h.2.2.2.2.2.2

end P0EFTJanusZ2NullPTThermodynamicAlphaSelectorGate
end JanusFormal
