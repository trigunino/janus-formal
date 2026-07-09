namespace JanusFormal
namespace P0EFTJanusConformalFriedmannOmegaEquationContractGate

set_option autoImplicit false

structure ConformalFriedmannOmegaEquationContractGate where
  KinematicPullbackAvailable : Prop
  ConformalFriedmannIdentityDeclared : Prop
  OmegaFirstOrderEquationFormDeclared : Prop
  HatBackgroundRequiredDeclared : Prop
  EffectiveDensityRequiredDeclared : Prop
  HatBackgroundDerived : Prop
  EffectiveDensityDerived : Prop
  InitialOrBoundaryConditionForOmegaDerived : Prop

def OmegaEquationContractClosed
    (g : ConformalFriedmannOmegaEquationContractGate) : Prop :=
  g.KinematicPullbackAvailable /\
  g.ConformalFriedmannIdentityDeclared /\
  g.OmegaFirstOrderEquationFormDeclared /\
  g.HatBackgroundRequiredDeclared /\
  g.EffectiveDensityRequiredDeclared

def OmegaSolutionClosed
    (g : ConformalFriedmannOmegaEquationContractGate) : Prop :=
  OmegaEquationContractClosed g /\
  g.HatBackgroundDerived /\
  g.EffectiveDensityDerived /\
  g.InitialOrBoundaryConditionForOmegaDerived

def OmegaEquationFrontier
    (g : ConformalFriedmannOmegaEquationContractGate) : Prop :=
  OmegaEquationContractClosed g /\
  Not g.HatBackgroundDerived /\
  Not g.EffectiveDensityDerived /\
  Not g.InitialOrBoundaryConditionForOmegaDerived

theorem omega_equation_contract_needs_background_source_and_bc
    (g : ConformalFriedmannOmegaEquationContractGate)
    (hFrontier : OmegaEquationFrontier g) :
    Not (OmegaSolutionClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusConformalFriedmannOmegaEquationContractGate
end JanusFormal
