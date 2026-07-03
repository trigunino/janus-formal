import JanusFormal.P0EFTJanusProjectiveTunnelInterface
import JanusFormal.P0EFTJanusProjectiveTunnelCoverSurvivalGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaProjectiveGluingNormalOrientationSignGate

set_option autoImplicit false

structure ProjectiveGluingNormalOrientationSignGate where
  projectiveTunnelInterfaceDeclared : Prop
  coverSurvivalGateDeclared : Prop
  thinShellOrientationBibliographyChecked : Prop
  antipodalDeckTransformationDeclared : Prop
  tunnelThroatSigmaDeclared : Prop
  twoFoldCoverSurvivesTunnelSurgery : Prop
  z2SheetExchangeDeclared : Prop
  normalOrientationReversalDeclared : Prop
  manualOrientationSignForbidden : Prop
  noFittedOrientationCoefficient : Prop
  z2NormalOrientationSignFixed : Prop

def projectiveGluingNormalOrientationSignLedgerDeclared
    (g : ProjectiveGluingNormalOrientationSignGate) : Prop :=
  g.projectiveTunnelInterfaceDeclared /\
  g.coverSurvivalGateDeclared /\
  g.thinShellOrientationBibliographyChecked /\
  g.antipodalDeckTransformationDeclared /\
  g.tunnelThroatSigmaDeclared /\
  g.twoFoldCoverSurvivesTunnelSurgery /\
  g.z2SheetExchangeDeclared /\
  g.normalOrientationReversalDeclared /\
  g.manualOrientationSignForbidden /\
  g.noFittedOrientationCoefficient

def projectiveGluingNormalOrientationSignReady
    (g : ProjectiveGluingNormalOrientationSignGate) : Prop :=
  projectiveGluingNormalOrientationSignLedgerDeclared g /\
  g.z2NormalOrientationSignFixed

theorem projective_gluing_orientation_ready_requires_sign
    (g : ProjectiveGluingNormalOrientationSignGate)
    (hReady : projectiveGluingNormalOrientationSignReady g) :
    g.z2NormalOrientationSignFixed := by
  exact hReady.right

end P0EFTJanusZ2SigmaProjectiveGluingNormalOrientationSignGate
end JanusFormal
