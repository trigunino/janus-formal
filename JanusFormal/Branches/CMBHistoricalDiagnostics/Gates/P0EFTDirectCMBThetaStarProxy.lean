namespace JanusFormal
namespace P0EFTDirectCMBThetaStarProxy

set_option autoImplicit false

structure DirectCMBThetaStarProxy where
  janusDistanceToRecombinationComputed : Prop
  holstSoundRulerComputed : Prop
  thetaStarProxyComputed : Prop
  usesLCDMCompressedPlanckVerdict : Prop
  cmbTransferFunctionsDerived : Prop

def thetaStarProxyReady (c : DirectCMBThetaStarProxy) : Prop :=
  c.janusDistanceToRecombinationComputed /\
  c.holstSoundRulerComputed /\
  c.thetaStarProxyComputed /\
  Not c.usesLCDMCompressedPlanckVerdict

def directCMBLikelihoodReady (c : DirectCMBThetaStarProxy) : Prop :=
  thetaStarProxyReady c /\
  c.cmbTransferFunctionsDerived

theorem theta_star_proxy_closes_distance_ruler_only
    (c : DirectCMBThetaStarProxy)
    (hD : c.janusDistanceToRecombinationComputed)
    (hR : c.holstSoundRulerComputed)
    (hTheta : c.thetaStarProxyComputed)
    (hNoLCDM : Not c.usesLCDMCompressedPlanckVerdict) :
    thetaStarProxyReady c := by
  exact And.intro hD (And.intro hR (And.intro hTheta hNoLCDM))

theorem missing_transfer_functions_blocks_direct_cmb_likelihood
    (c : DirectCMBThetaStarProxy)
    (hMissing : Not c.cmbTransferFunctionsDerived) :
    Not (directCMBLikelihoodReady c) := by
  intro h
  exact hMissing h.right

end P0EFTDirectCMBThetaStarProxy
end JanusFormal
