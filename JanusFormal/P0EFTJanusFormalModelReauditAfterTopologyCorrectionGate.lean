import JanusFormal.P0EFTJanusTopologyLayerAlignmentGate
import JanusFormal.P0EFTJanusProjectiveTunnelInterface

namespace JanusFormal
namespace P0EFTJanusFormalModelReauditAfterTopologyCorrectionGate

set_option autoImplicit false

structure FormalModelReauditAfterTopologyCorrectionGate where
  topologyLayerAlignmentLoaded : Prop
  projectiveTunnelInterfaceLoaded : Prop
  z2CoverKeptAsTopologicalCover : Prop
  z4NotDerivedFromTwoFoldCover : Prop
  torusKleinResolvedShadowLoaded : Prop
  boySurfaceLimitedToUnresolvedProjectiveShadow : Prop
  apsPinRP4ReauditRequired : Prop
  boundarySupportIsTunnelThroatSigma : Prop
  noFitPromotionBlocked : Prop

def reauditClosed (g : FormalModelReauditAfterTopologyCorrectionGate) : Prop :=
  g.topologyLayerAlignmentLoaded /\
  g.projectiveTunnelInterfaceLoaded /\
  g.z2CoverKeptAsTopologicalCover /\
  g.z4NotDerivedFromTwoFoldCover /\
  g.torusKleinResolvedShadowLoaded /\
  g.boySurfaceLimitedToUnresolvedProjectiveShadow /\
  g.apsPinRP4ReauditRequired /\
  g.boundarySupportIsTunnelThroatSigma /\
  g.noFitPromotionBlocked

theorem reaudit_blocks_no_fit_until_rp4_pin_and_z4_lift
    (g : FormalModelReauditAfterTopologyCorrectionGate)
    (h : reauditClosed g) :
    g.apsPinRP4ReauditRequired /\
    g.z4NotDerivedFromTwoFoldCover /\
    g.noFitPromotionBlocked := by
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

end P0EFTJanusFormalModelReauditAfterTopologyCorrectionGate
end JanusFormal
