import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaBoundaryStressExtractionGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaHolstNiehYanFLRWObligationGate

set_option autoImplicit false

structure HolstNiehYanFLRWObligationGate where
  holstNiehYanBibliographyChecked : Prop
  holstNiehYanTorsionRelationImported : Prop
  torsionlessHolstVanishingGuardDeclared : Prop
  sigmaTorsionPullbackDeclared : Prop
  immirziBoundaryVariationDeclared : Prop
  flrwTorsionIrreducibleDecompositionReady : Prop
  holstNiehYanFLRWStressReduced : Prop
  holstNiehYanRhoPOfAReady : Prop

def holstNiehYanMethodReady
    (g : HolstNiehYanFLRWObligationGate) : Prop :=
  g.holstNiehYanBibliographyChecked /\
  g.holstNiehYanTorsionRelationImported /\
  g.torsionlessHolstVanishingGuardDeclared /\
  g.sigmaTorsionPullbackDeclared /\
  g.immirziBoundaryVariationDeclared

def holstNiehYanFLRWClosureReady
    (g : HolstNiehYanFLRWObligationGate) : Prop :=
  holstNiehYanMethodReady g /\
  g.flrwTorsionIrreducibleDecompositionReady /\
  g.holstNiehYanFLRWStressReduced /\
  g.holstNiehYanRhoPOfAReady

theorem holst_flrw_closure_requires_torsion_decomposition
    (g : HolstNiehYanFLRWObligationGate)
    (hReady : holstNiehYanFLRWClosureReady g) :
    g.flrwTorsionIrreducibleDecompositionReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaHolstNiehYanFLRWObligationGate
end JanusFormal
