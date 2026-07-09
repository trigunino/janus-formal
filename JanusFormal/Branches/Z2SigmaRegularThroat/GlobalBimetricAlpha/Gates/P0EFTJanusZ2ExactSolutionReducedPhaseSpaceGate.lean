namespace JanusFormal
namespace P0EFTJanusZ2ExactSolutionReducedPhaseSpaceGate

set_option autoImplicit false

structure ExactSolutionReducedPhaseSpaceGate where
  exactSolutionFamilyAvailable : Prop
  alphaToEGlobalIdentityAvailable : Prop
  reducedActionDerived : Prop
  canonicalPairDerived : Prop
  symplecticFormDerived : Prop
  hamiltonianConstraintDerived : Prop
  alphaConjugateVariableIdentified : Prop
  compactGlobalCycleIdentified : Prop
  integralityOrStateSelectionLawDerived : Prop
  alphaPureGaugeProved : Prop

def canonicalReductionReady (g : ExactSolutionReducedPhaseSpaceGate) : Prop :=
  g.reducedActionDerived /\
  g.canonicalPairDerived /\
  g.symplecticFormDerived /\
  g.hamiltonianConstraintDerived /\
  g.alphaConjugateVariableIdentified

def alphaQuantizedOrSelected (g : ExactSolutionReducedPhaseSpaceGate) : Prop :=
  canonicalReductionReady g /\
  g.compactGlobalCycleIdentified /\
  g.integralityOrStateSelectionLawDerived

def alphaContinuousChargeLabel (g : ExactSolutionReducedPhaseSpaceGate) : Prop :=
  g.exactSolutionFamilyAvailable /\
  g.alphaToEGlobalIdentityAvailable /\
  Not (alphaQuantizedOrSelected g) /\
  Not g.alphaPureGaugeProved

theorem missing_reduced_action_blocks_quantization
    (g : ExactSolutionReducedPhaseSpaceGate)
    (hMissing : Not g.reducedActionDerived) :
    Not (alphaQuantizedOrSelected g) := by
  intro h
  exact hMissing h.left.left

theorem compact_cycle_without_integrality_does_not_quantize
    (g : ExactSolutionReducedPhaseSpaceGate)
    (hMissing : Not g.integralityOrStateSelectionLawDerived) :
    Not (alphaQuantizedOrSelected g) := by
  intro h
  exact hMissing h.right.right

theorem exact_alpha_E_identity_permits_continuous_label
    (g : ExactSolutionReducedPhaseSpaceGate)
    (hExact : g.exactSolutionFamilyAvailable)
    (hEnergy : g.alphaToEGlobalIdentityAvailable)
    (hNoQuant : Not (alphaQuantizedOrSelected g))
    (hNoGauge : Not g.alphaPureGaugeProved) :
    alphaContinuousChargeLabel g := by
  exact ⟨hExact, hEnergy, hNoQuant, hNoGauge⟩

end P0EFTJanusZ2ExactSolutionReducedPhaseSpaceGate
end JanusFormal
