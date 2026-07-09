namespace JanusFormal
namespace P0EFTJanusZ2AlphaSelectionLawClosureGate

set_option autoImplicit false

structure AlphaSelectionLawClosureGate where
  boundaryChargeEquationDerived : Prop
  boundaryChargeValueFixed : Prop
  souriauOrbitEquationDerived : Prop
  souriauOrbitQuantized : Prop
  fluxQuantizationEquationDerived : Prop
  fluxUnitAndMapFixed : Prop
  casimirEquationDerived : Prop
  casimirCoefficientFixed : Prop
  horizonFirstLawDerived : Prop
  horizonStateCountFixed : Prop
  pureTopologyScaleInvariant : Prop
  claimsUniqueAlphaSelector : Prop

def uniqueAlphaSelectorReady (g : AlphaSelectionLawClosureGate) : Prop :=
  (g.boundaryChargeEquationDerived /\ g.boundaryChargeValueFixed) \/
  (g.souriauOrbitEquationDerived /\ g.souriauOrbitQuantized) \/
  (g.fluxQuantizationEquationDerived /\ g.fluxUnitAndMapFixed) \/
  (g.casimirEquationDerived /\ g.casimirCoefficientFixed) \/
  (g.horizonFirstLawDerived /\ g.horizonStateCountFixed)

def honestNoSelectorClosure (g : AlphaSelectionLawClosureGate) : Prop :=
  g.boundaryChargeEquationDerived /\
  Not g.boundaryChargeValueFixed /\
  g.souriauOrbitEquationDerived /\
  Not g.souriauOrbitQuantized /\
  g.fluxQuantizationEquationDerived /\
  Not g.fluxUnitAndMapFixed /\
  g.casimirEquationDerived /\
  Not g.casimirCoefficientFixed /\
  g.horizonFirstLawDerived /\
  Not g.horizonStateCountFixed /\
  g.pureTopologyScaleInvariant /\
  Not g.claimsUniqueAlphaSelector

theorem no_selector_closure_blocks_unique_selector
    (g : AlphaSelectionLawClosureGate)
    (h : honestNoSelectorClosure g) :
    Not (uniqueAlphaSelectorReady g) := by
  intro hReady
  rcases h with ⟨_, hNoB, _, hNoS, _, hNoF, _, hNoC, _, hNoH, _, _⟩
  rcases hReady with hB | hS | hF | hC | hH
  · exact hNoB hB.right
  · exact hNoS hS.right
  · exact hNoF hF.right
  · exact hNoC hC.right
  · exact hNoH hH.right

end P0EFTJanusZ2AlphaSelectionLawClosureGate
end JanusFormal
