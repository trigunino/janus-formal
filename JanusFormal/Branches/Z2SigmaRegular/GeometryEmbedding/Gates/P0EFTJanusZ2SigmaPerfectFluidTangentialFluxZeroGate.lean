namespace JanusFormal
namespace P0EFTJanusZ2SigmaPerfectFluidTangentialFluxZeroGate

set_option autoImplicit false

structure PerfectFluidTangentialFluxZeroGate where
  perfectFluidFluxIdentityDeclared : Prop
  tangentNormalOrthogonalityDeclared : Prop
  comovingFlowTangentToSigmaDeclared : Prop
  pressureTermZeroByEDotNDeclared : Prop
  convectiveTermZeroByUDotNDeclared : Prop
  rhoPressureValuesNotRequiredForZeroIdentity : Prop
  observationalFitForbidden : Prop
  sigmaTangentsReady : Prop
  sigmaNormalsReady : Prop
  tangentNormalOrthogonalityDerived : Prop
  plusFourVelocityTangentToSigmaDerived : Prop
  minusFourVelocityTangentToSigmaDerived : Prop
  perfectFluidNormalFluxZeroDerived : Prop
  holstTorsionFluxNotClosedByThisGate : Prop

def perfectFluidTangentialFluxZeroReady
    (g : PerfectFluidTangentialFluxZeroGate) : Prop :=
  g.perfectFluidFluxIdentityDeclared /\
  g.tangentNormalOrthogonalityDeclared /\
  g.comovingFlowTangentToSigmaDeclared /\
  g.pressureTermZeroByEDotNDeclared /\
  g.convectiveTermZeroByUDotNDeclared /\
  g.rhoPressureValuesNotRequiredForZeroIdentity /\
  g.observationalFitForbidden /\
  g.sigmaTangentsReady /\
  g.sigmaNormalsReady /\
  g.tangentNormalOrthogonalityDerived /\
  g.plusFourVelocityTangentToSigmaDerived /\
  g.minusFourVelocityTangentToSigmaDerived /\
  g.perfectFluidNormalFluxZeroDerived

theorem perfect_fluid_zero_keeps_holst_flux_separate
    (g : PerfectFluidTangentialFluxZeroGate)
    (_h : perfectFluidTangentialFluxZeroReady g)
    (hHolst : g.holstTorsionFluxNotClosedByThisGate) :
    g.holstTorsionFluxNotClosedByThisGate := by
  exact hHolst

theorem perfect_fluid_zero_requires_comoving_tangency
    (g : PerfectFluidTangentialFluxZeroGate)
    (h : perfectFluidTangentialFluxZeroReady g) :
    g.plusFourVelocityTangentToSigmaDerived /\
      g.minusFourVelocityTangentToSigmaDerived := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, hPlus, hMinus, _⟩
  exact And.intro hPlus hMinus

end P0EFTJanusZ2SigmaPerfectFluidTangentialFluxZeroGate
end JanusFormal
