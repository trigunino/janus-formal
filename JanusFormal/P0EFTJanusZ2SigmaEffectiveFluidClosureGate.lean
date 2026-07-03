import JanusFormal.P0EFTJanusZ2SigmaProjectedStressTensorGate
import JanusFormal.P0EFTJanusZ2SigmaTunnelJunctionConditionGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaEffectiveFluidClosureGate

set_option autoImplicit false

structure Z2SigmaEffectiveFluidClosureGate where
  projectedSigmaStressTensorDerived : Prop
  z2TunnelJunctionConditionDerived : Prop
  shellCosmologyBibliographyChecked : Prop
  inducedFLRWSigmaMetricDeclared : Prop
  perfectFluidProjectionDeclared : Prop
  rhoEffProjectionFormulaReady : Prop
  pEffProjectionFormulaReady : Prop
  rhoEffZ2SigmaOfAReady : Prop
  pEffZ2SigmaOfAReady : Prop
  directJanusFormulaFoundInBibliography : Prop

def effectiveFluidStructuralPrerequisites
    (g : Z2SigmaEffectiveFluidClosureGate) : Prop :=
  g.projectedSigmaStressTensorDerived /\
  g.z2TunnelJunctionConditionDerived /\
  g.shellCosmologyBibliographyChecked /\
  g.inducedFLRWSigmaMetricDeclared /\
  g.perfectFluidProjectionDeclared /\
  g.rhoEffProjectionFormulaReady /\
  g.pEffProjectionFormulaReady

def effectiveFluidNumericClosure
    (g : Z2SigmaEffectiveFluidClosureGate) : Prop :=
  effectiveFluidStructuralPrerequisites g /\
  g.rhoEffZ2SigmaOfAReady /\
  g.pEffZ2SigmaOfAReady

theorem numeric_effective_fluid_requires_projection_formulas
    (g : Z2SigmaEffectiveFluidClosureGate)
    (hNumeric : effectiveFluidNumericClosure g) :
    effectiveFluidStructuralPrerequisites g := by
  exact hNumeric.left

end P0EFTJanusZ2SigmaEffectiveFluidClosureGate
end JanusFormal
