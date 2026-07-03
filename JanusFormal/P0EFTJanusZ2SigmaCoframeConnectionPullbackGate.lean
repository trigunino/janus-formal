import JanusFormal.P0EFTJanusZ2SigmaTangentNormalOrientationGate
import JanusFormal.P0EFTJanusZ2SigmaProjectiveGluingNormalOrientationSignGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCoframeConnectionPullbackGate

set_option autoImplicit false

structure CoframeConnectionPullbackGate where
  coframeConnectionBibliographyChecked : Prop
  tetradCoframeFormalismImported : Prop
  spinConnectionFormalismImported : Prop
  differentialFormPullbackImported : Prop
  activeSigmaEmbeddingRequired : Prop
  tangentNormalOrientationGateDeclared : Prop
  projectiveGluingNormalOrientationSignGateDeclared : Prop
  coframePullbackDeclared : Prop
  spinConnectionPullbackDeclared : Prop
  z2NormalOrientationRequired : Prop
  observationalFitForbidden : Prop
  activeSigmaEmbeddingReady : Prop
  coframePullbackReady : Prop
  spinConnectionPullbackReady : Prop
  z2OrientedPullbackReady : Prop
  coframeConnectionPullbackReady : Prop

def coframeConnectionPullbackLedgerDeclared
    (g : CoframeConnectionPullbackGate) : Prop :=
  g.coframeConnectionBibliographyChecked /\
  g.tetradCoframeFormalismImported /\
  g.spinConnectionFormalismImported /\
  g.differentialFormPullbackImported /\
  g.activeSigmaEmbeddingRequired /\
  g.tangentNormalOrientationGateDeclared /\
  g.projectiveGluingNormalOrientationSignGateDeclared /\
  g.coframePullbackDeclared /\
  g.spinConnectionPullbackDeclared /\
  g.z2NormalOrientationRequired /\
  g.observationalFitForbidden

def coframeConnectionPullbackClosure
    (g : CoframeConnectionPullbackGate) : Prop :=
  coframeConnectionPullbackLedgerDeclared g /\
  g.activeSigmaEmbeddingReady /\
  g.coframePullbackReady /\
  g.spinConnectionPullbackReady /\
  g.z2OrientedPullbackReady /\
  g.coframeConnectionPullbackReady

theorem coframe_connection_pullback_requires_active_embedding
    (g : CoframeConnectionPullbackGate)
    (hReady : coframeConnectionPullbackClosure g) :
    g.activeSigmaEmbeddingReady := by
  exact hReady.2.1

end P0EFTJanusZ2SigmaCoframeConnectionPullbackGate
end JanusFormal
