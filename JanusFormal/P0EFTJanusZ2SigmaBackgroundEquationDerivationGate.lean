import JanusFormal.P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate
import JanusFormal.P0EFTJanusZ2SigmaBackgroundBibliographyGate
import JanusFormal.P0EFTJanusZ2SigmaProjectedStressTensorGate
import JanusFormal.P0EFTJanusZ2SigmaTunnelJunctionConditionGate
import JanusFormal.P0EFTJanusZ2SigmaEffectiveBackgroundClosureGate
import JanusFormal.P0EFTJanusZ2SigmaObservationalRoadmapGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBackgroundEquationDerivationGate

set_option autoImplicit false

structure Z2SigmaBackgroundEquationDerivationGate where
  sigmaBoundaryActionClosed : Prop
  backgroundBibliographyChecked : Prop
  localBackgroundDerivationRequired : Prop
  legacyLCDMBackgroundSubstitutionForbidden : Prop
  archivedZ4BackgroundReuseForbidden : Prop
  projectedSigmaStressTensorDerived : Prop
  z2TunnelJunctionConditionDerived : Prop
  effectiveFriedmannEquationDerived : Prop
  effectiveAccelerationEquationDerived : Prop
  effectiveContinuityEquationDerived : Prop
  backgroundEquationsDerived : Prop

def backgroundEquationLockClosed
    (g : Z2SigmaBackgroundEquationDerivationGate) : Prop :=
  g.sigmaBoundaryActionClosed /\
  g.backgroundBibliographyChecked /\
  g.localBackgroundDerivationRequired /\
  g.legacyLCDMBackgroundSubstitutionForbidden /\
  g.archivedZ4BackgroundReuseForbidden /\
  g.projectedSigmaStressTensorDerived /\
  g.z2TunnelJunctionConditionDerived /\
  g.effectiveFriedmannEquationDerived /\
  g.effectiveAccelerationEquationDerived /\
  g.effectiveContinuityEquationDerived

theorem background_lock_closes_background_equations
    (g : Z2SigmaBackgroundEquationDerivationGate)
    (hLock : backgroundEquationLockClosed g)
    (hImplies : backgroundEquationLockClosed g -> g.backgroundEquationsDerived) :
    g.backgroundEquationsDerived := by
  exact hImplies hLock

theorem missing_friedmann_blocks_background_lock
    (g : Z2SigmaBackgroundEquationDerivationGate)
    (hMissing : Not g.effectiveFriedmannEquationDerived) :
    Not (backgroundEquationLockClosed g) := by
  intro h
  exact hMissing h.2.2.2.2.2.2.2.1

end P0EFTJanusZ2SigmaBackgroundEquationDerivationGate
end JanusFormal
