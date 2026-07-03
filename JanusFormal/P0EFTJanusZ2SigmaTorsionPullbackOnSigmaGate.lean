import JanusFormal.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate

set_option autoImplicit false

structure TorsionPullbackOnSigmaGate where
  torsionPullbackBibliographyChecked : Prop
  differentialFormPullbackImported : Prop
  cartanFirstStructureEquationImported : Prop
  sigmaEmbeddingRequired : Prop
  coframePullbackRequired : Prop
  connectionPullbackRequired : Prop
  coframeConnectionPullbackGateDeclared : Prop
  z2NormalOrientationRequired : Prop
  observationalFitForbidden : Prop
  sigmaEmbeddingReady : Prop
  coframePullbackReady : Prop
  connectionPullbackReady : Prop
  ambientTorsionFormReady : Prop
  sigmaTorsionPullbackReady : Prop
  flrwIrreducibleTorsionPullbackReady : Prop
  torsionPullbackOnSigmaReady : Prop

def torsionPullbackLedgerDeclared
    (g : TorsionPullbackOnSigmaGate) : Prop :=
  g.torsionPullbackBibliographyChecked /\
  g.differentialFormPullbackImported /\
  g.cartanFirstStructureEquationImported /\
  g.sigmaEmbeddingRequired /\
  g.coframePullbackRequired /\
  g.connectionPullbackRequired /\
  g.coframeConnectionPullbackGateDeclared /\
  g.z2NormalOrientationRequired /\
  g.observationalFitForbidden

def torsionPullbackReady
    (g : TorsionPullbackOnSigmaGate) : Prop :=
  torsionPullbackLedgerDeclared g /\
  g.sigmaEmbeddingReady /\
  g.coframePullbackReady /\
  g.connectionPullbackReady /\
  g.ambientTorsionFormReady /\
  g.sigmaTorsionPullbackReady /\
  g.flrwIrreducibleTorsionPullbackReady /\
  g.torsionPullbackOnSigmaReady

theorem torsion_pullback_requires_embedding_and_connection
    (g : TorsionPullbackOnSigmaGate)
    (hReady : torsionPullbackReady g) :
    g.sigmaEmbeddingReady /\ g.coframePullbackReady /\ g.connectionPullbackReady := by
  exact And.intro hReady.2.1 (And.intro hReady.2.2.1 hReady.2.2.2.1)

end P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate
end JanusFormal
