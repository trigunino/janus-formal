namespace JanusFormal
namespace P0EFTJanusZ2PublishedMinisuperspaceHamiltonianReductionGate

set_option autoImplicit false

structure PublishedMinisuperspaceHamiltonianReductionGate where
  exactSolutionAvailable : Prop
  alphaEGlobalIdentityAvailable : Prop
  minisuperspaceLagrangianWritten : Prop
  lapseConstraintsDerived : Prop
  canonicalMomentaDerived : Prop
  hamiltonianConstraintDerived : Prop
  constraintReductionPerformed : Prop
  symplecticPullbackDerived : Prop
  alphaConjugateCoordinateIdentified : Prop
  compactCycleFound : Prop
  actionIntegralDerived : Prop
  integralityOrSelectionLawDerived : Prop

def canonicalHamiltonianReductionReady
    (g : PublishedMinisuperspaceHamiltonianReductionGate) : Prop :=
  g.minisuperspaceLagrangianWritten /\
  g.lapseConstraintsDerived /\
  g.canonicalMomentaDerived /\
  g.hamiltonianConstraintDerived /\
  g.constraintReductionPerformed /\
  g.symplecticPullbackDerived /\
  g.alphaConjugateCoordinateIdentified

def alphaQuantizationReady
    (g : PublishedMinisuperspaceHamiltonianReductionGate) : Prop :=
  canonicalHamiltonianReductionReady g /\
  g.compactCycleFound /\
  g.actionIntegralDerived /\
  g.integralityOrSelectionLawDerived

def alphaContinuousCasimirCharge
    (g : PublishedMinisuperspaceHamiltonianReductionGate) : Prop :=
  g.exactSolutionAvailable /\
  g.alphaEGlobalIdentityAvailable /\
  Not (alphaQuantizationReady g)

theorem missing_lagrangian_blocks_hamiltonian_reduction
    (g : PublishedMinisuperspaceHamiltonianReductionGate)
    (hMissing : Not g.minisuperspaceLagrangianWritten) :
    Not (canonicalHamiltonianReductionReady g) := by
  intro h
  exact hMissing h.left

theorem no_compact_cycle_blocks_alpha_quantization
    (g : PublishedMinisuperspaceHamiltonianReductionGate)
    (hMissing : Not g.compactCycleFound) :
    Not (alphaQuantizationReady g) := by
  intro h
  exact hMissing h.right.left

theorem exact_energy_identity_with_no_quantization_is_continuous_charge
    (g : PublishedMinisuperspaceHamiltonianReductionGate)
    (hExact : g.exactSolutionAvailable)
    (hEnergy : g.alphaEGlobalIdentityAvailable)
    (hNoQuant : Not (alphaQuantizationReady g)) :
    alphaContinuousCasimirCharge g := by
  exact ⟨hExact, hEnergy, hNoQuant⟩

end P0EFTJanusZ2PublishedMinisuperspaceHamiltonianReductionGate
end JanusFormal
