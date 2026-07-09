import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaActiveTunnelEmbeddingFromRadiusGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaEmbeddingTangentFrameTransportGate

set_option autoImplicit false

structure EmbeddingTangentFrameTransportGate where
  activeEmbeddingFromRadiusGateDeclared : Prop
  embeddedSubmanifoldTangentBibliographyChecked : Prop
  thinShellTangentFrameBibliographyChecked : Prop
  xPlusMinusOfAInputDeclared : Prop
  coordinateDerivativeFormulaDeclared : Prop
  tangentFrameTransportMapDeclared : Prop
  noFittedTangentFrame : Prop
  xPlusMinusOfAReady : Prop
  tangentFramesFromEmbeddingReady : Prop

def embeddingTangentFrameTransportLedgerDeclared
    (g : EmbeddingTangentFrameTransportGate) : Prop :=
  g.activeEmbeddingFromRadiusGateDeclared /\
  g.embeddedSubmanifoldTangentBibliographyChecked /\
  g.thinShellTangentFrameBibliographyChecked /\
  g.xPlusMinusOfAInputDeclared /\
  g.coordinateDerivativeFormulaDeclared /\
  g.tangentFrameTransportMapDeclared /\
  g.noFittedTangentFrame

def embeddingTangentFrameTransportReady
    (g : EmbeddingTangentFrameTransportGate) : Prop :=
  embeddingTangentFrameTransportLedgerDeclared g /\
  g.xPlusMinusOfAReady /\
  g.tangentFramesFromEmbeddingReady

theorem tangent_frames_require_embedding_functions
    (g : EmbeddingTangentFrameTransportGate)
    (hReady : embeddingTangentFrameTransportReady g) :
    g.xPlusMinusOfAReady := by
  exact hReady.right.left

end P0EFTJanusZ2SigmaEmbeddingTangentFrameTransportGate
end JanusFormal
