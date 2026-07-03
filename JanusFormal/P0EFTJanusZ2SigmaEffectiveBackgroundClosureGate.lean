import JanusFormal.P0EFTJanusZ2SigmaTunnelJunctionConditionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaEffectiveBackgroundClosureGate

set_option autoImplicit false

structure Z2SigmaEffectiveBackgroundClosureGate where
  projectedSigmaStressTensorDerived : Prop
  z2TunnelJunctionConditionDerived : Prop
  flrwSymmetryReductionDeclared : Prop
  effectiveEnergyDensityProjected : Prop
  effectivePressureProjected : Prop
  effectiveFriedmannEquationDerived : Prop
  effectiveAccelerationEquationDerived : Prop
  effectiveContinuityEquationDerived : Prop
  backgroundEquationsDerived : Prop

def effectiveBackgroundLockClosed
    (g : Z2SigmaEffectiveBackgroundClosureGate) : Prop :=
  g.projectedSigmaStressTensorDerived /\
  g.z2TunnelJunctionConditionDerived /\
  g.flrwSymmetryReductionDeclared /\
  g.effectiveEnergyDensityProjected /\
  g.effectivePressureProjected /\
  g.effectiveFriedmannEquationDerived /\
  g.effectiveAccelerationEquationDerived /\
  g.effectiveContinuityEquationDerived

theorem effective_background_lock_derives_background_equations
    (g : Z2SigmaEffectiveBackgroundClosureGate)
    (hLock : effectiveBackgroundLockClosed g)
    (hImplies : effectiveBackgroundLockClosed g -> g.backgroundEquationsDerived) :
    g.backgroundEquationsDerived := by
  exact hImplies hLock

end P0EFTJanusZ2SigmaEffectiveBackgroundClosureGate
end JanusFormal
