import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusBlockExpansionGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaHolstNiehYanRadialBlockGate

set_option autoImplicit false

structure HolstNiehYanRadialBlockGate where
  holstNiehYanBibliographyChecked : Prop
  torsionRequiredForNonzeroBlockDeclared : Prop
  dynamicImmirziBoundaryVariationDeclared : Prop
  sigmaTorsionPullbackRequired : Prop
  radialEmbeddingVariationDeclared : Prop
  observationalFitForbidden : Prop
  eHolstNiehYanFunctionalDerivativeDeclared : Prop
  eHolstNiehYanStructuralReductionReady : Prop
  sigmaTorsionPullbackReady : Prop
  immirziRadialProfileReady : Prop
  eHolstNiehYanOfAReady : Prop

def holstNiehYanRadialLedgerDeclared
    (g : HolstNiehYanRadialBlockGate) : Prop :=
  g.holstNiehYanBibliographyChecked /\
  g.torsionRequiredForNonzeroBlockDeclared /\
  g.dynamicImmirziBoundaryVariationDeclared /\
  g.sigmaTorsionPullbackRequired /\
  g.radialEmbeddingVariationDeclared /\
  g.observationalFitForbidden /\
  g.eHolstNiehYanFunctionalDerivativeDeclared

def holstNiehYanRadialBlockStructurallyDeclared
    (g : HolstNiehYanRadialBlockGate) : Prop :=
  holstNiehYanRadialLedgerDeclared g /\
  g.eHolstNiehYanStructuralReductionReady

def holstNiehYanRadialBlockOfAReady
    (g : HolstNiehYanRadialBlockGate) : Prop :=
  holstNiehYanRadialBlockStructurallyDeclared g /\
  g.sigmaTorsionPullbackReady /\
  g.immirziRadialProfileReady /\
  g.eHolstNiehYanOfAReady

theorem holst_nieh_yan_of_a_requires_torsion_pullback
    (g : HolstNiehYanRadialBlockGate)
    (hReady : holstNiehYanRadialBlockOfAReady g) :
    g.sigmaTorsionPullbackReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaHolstNiehYanRadialBlockGate
end JanusFormal
