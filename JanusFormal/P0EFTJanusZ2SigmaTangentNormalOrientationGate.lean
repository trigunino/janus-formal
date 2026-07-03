import JanusFormal.P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTangentNormalOrientationGate

set_option autoImplicit false

structure TangentNormalOrientationGate where
  thinShellNormalBibliographyChecked : Prop
  sigmaEmbeddingDeclared : Prop
  activeEmbeddingFromRadiusGateDeclared : Prop
  tangentFrameFormulaDeclared : Prop
  unitNormalFormulaDeclared : Prop
  orthogonalityNormalizationDeclared : Prop
  z2NormalOrientationDeclared : Prop
  observationalFitForbidden : Prop
  activeSigmaEmbeddingReady : Prop
  tangentFramesOfAReady : Prop
  unitNormalsOfAReady : Prop
  z2OrientationSignFixed : Prop
  tangentNormalOrientationReady : Prop

def tangentNormalOrientationLedgerDeclared
    (g : TangentNormalOrientationGate) : Prop :=
  g.thinShellNormalBibliographyChecked /\
  g.sigmaEmbeddingDeclared /\
  g.activeEmbeddingFromRadiusGateDeclared /\
  g.tangentFrameFormulaDeclared /\
  g.unitNormalFormulaDeclared /\
  g.orthogonalityNormalizationDeclared /\
  g.z2NormalOrientationDeclared /\
  g.observationalFitForbidden

def tangentNormalOrientationClosure
    (g : TangentNormalOrientationGate) : Prop :=
  tangentNormalOrientationLedgerDeclared g /\
  g.activeSigmaEmbeddingReady /\
  g.tangentFramesOfAReady /\
  g.unitNormalsOfAReady /\
  g.z2OrientationSignFixed /\
  g.tangentNormalOrientationReady

theorem z2_orientation_requires_unit_normals
    (g : TangentNormalOrientationGate)
    (hReady : tangentNormalOrientationClosure g) :
    g.unitNormalsOfAReady := by
  exact hReady.2.2.2.1

end P0EFTJanusZ2SigmaTangentNormalOrientationGate
end JanusFormal
