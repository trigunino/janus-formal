import JanusFormal.P0EFTJanusZ2SigmaHolstNiehYanFLRWObligationGate
import JanusFormal.P0EFTJanusZ2SigmaImmirziProfileOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaHolstTorsionStressOfAGate

set_option autoImplicit false

structure HolstTorsionStressOfAGate where
  holstTorsionBibliographyChecked : Prop
  holstNiehYanRelationImported : Prop
  stressVariationFormulaDeclared : Prop
  torsionlessVanishingGuardDeclared : Prop
  dynamicImmirziProfileRequired : Prop
  z2SigmaTorsionSolutionRequired : Prop
  observationalFitForbidden : Prop
  torsionFieldEquationsDeclared : Prop
  torsionFieldSolutionOfAReady : Prop
  immirziProfileOfAReady : Prop
  holstTorsionStressReduced : Prop
  holstTorsionStressOfAReady : Prop

def holstTorsionStressLedgerDeclared
    (g : HolstTorsionStressOfAGate) : Prop :=
  g.holstTorsionBibliographyChecked /\
  g.holstNiehYanRelationImported /\
  g.stressVariationFormulaDeclared /\
  g.torsionlessVanishingGuardDeclared /\
  g.dynamicImmirziProfileRequired /\
  g.z2SigmaTorsionSolutionRequired /\
  g.observationalFitForbidden /\
  g.torsionFieldEquationsDeclared

def holstTorsionStressClosureReady
    (g : HolstTorsionStressOfAGate) : Prop :=
  holstTorsionStressLedgerDeclared g /\
  g.torsionFieldSolutionOfAReady /\
  g.immirziProfileOfAReady /\
  g.holstTorsionStressReduced /\
  g.holstTorsionStressOfAReady

theorem holst_torsion_stress_requires_torsion_solution
    (g : HolstTorsionStressOfAGate)
    (hReady : holstTorsionStressClosureReady g) :
    g.torsionFieldSolutionOfAReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaHolstTorsionStressOfAGate
end JanusFormal
