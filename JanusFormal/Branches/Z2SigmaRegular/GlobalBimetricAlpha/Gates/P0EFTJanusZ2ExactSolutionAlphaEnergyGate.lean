namespace JanusFormal
namespace P0EFTJanusZ2ExactSolutionAlphaEnergyGate

set_option autoImplicit false

structure ExactSolutionAlphaEnergyGate where
  exactJanusShapeDerived : Prop
  alphaScaleAvailable : Prop
  accelerationIdentityDerived : Prop
  publishedEnergyEquationDeclared : Prop
  usesObservationH0Fit : Prop
  usesLegacyZ4 : Prop

def alphaToEnergyReady (g : ExactSolutionAlphaEnergyGate) : Prop :=
  g.exactJanusShapeDerived /\
  g.alphaScaleAvailable /\
  g.accelerationIdentityDerived /\
  g.publishedEnergyEquationDeclared /\
  Not g.usesObservationH0Fit /\
  Not g.usesLegacyZ4

theorem missing_alpha_blocks_alphaToEnergy
    (g : ExactSolutionAlphaEnergyGate)
    (hMissing : Not g.alphaScaleAvailable) :
    Not (alphaToEnergyReady g) := by
  intro h
  exact hMissing h.right.left

theorem legacy_z4_blocks_alphaToEnergy
    (g : ExactSolutionAlphaEnergyGate)
    (hZ4 : g.usesLegacyZ4) :
    Not (alphaToEnergyReady g) := by
  intro h
  exact h.right.right.right.right.right hZ4

end P0EFTJanusZ2ExactSolutionAlphaEnergyGate
end JanusFormal
