import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaCoframeConnectionPullbackGate

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
  cartanTorsionFormulaReady : Prop
  sigmaPullbackFormulaReady : Prop
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

def torsionFormulaSubchannelsReady
    (g : TorsionPullbackOnSigmaGate) : Prop :=
  g.cartanTorsionFormulaReady /\ g.sigmaPullbackFormulaReady

def torsionPullbackReady
    (g : TorsionPullbackOnSigmaGate) : Prop :=
  torsionPullbackLedgerDeclared g /\
  torsionFormulaSubchannelsReady g /\
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
  exact And.intro hReady.2.2.1 (And.intro hReady.2.2.2.1 hReady.2.2.2.2.1)

theorem torsion_formulas_do_not_close_sigma_pullback_without_embedding
    (g : TorsionPullbackOnSigmaGate)
    (hNoEmbedding : ¬ g.sigmaEmbeddingReady) :
    ¬ (torsionFormulaSubchannelsReady g /\ torsionPullbackReady g) := by
  intro h
  exact hNoEmbedding h.2.2.2.1

end P0EFTJanusZ2SigmaTorsionPullbackOnSigmaGate
end JanusFormal
