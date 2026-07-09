import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTangentNormalOrientationGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaFixedMapPullbackVariationCommutationGate
import JanusFormal.Branches.Z2SigmaRegular.Topology.Gates.P0EFTJanusZ2SigmaProjectiveGluingNormalOrientationSignGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaOrientedPullbackVariationCommutationGate

set_option autoImplicit false

structure OrientedPullbackVariationCommutationGate where
  tangentNormalOrientationGateDeclared : Prop
  fixedMapPullbackVariationCommutationGateDeclared : Prop
  projectiveGluingNormalOrientationSignGateDeclared : Prop
  thinShellOrientationBibliographyChecked : Prop
  z2NormalOrientationDeclared : Prop
  orientationSignTransportDeclared : Prop
  manualOrientationSignForbidden : Prop
  noFittedOrientationCoefficient : Prop
  fixedMapCommutationReady : Prop
  z2OrientationSignFixed : Prop
  z2OrientedCommutationReady : Prop

def orientedPullbackVariationCommutationLedgerDeclared
    (g : OrientedPullbackVariationCommutationGate) : Prop :=
  g.tangentNormalOrientationGateDeclared /\
  g.fixedMapPullbackVariationCommutationGateDeclared /\
  g.projectiveGluingNormalOrientationSignGateDeclared /\
  g.thinShellOrientationBibliographyChecked /\
  g.z2NormalOrientationDeclared /\
  g.orientationSignTransportDeclared /\
  g.manualOrientationSignForbidden /\
  g.noFittedOrientationCoefficient

def orientedPullbackVariationCommutationReady
    (g : OrientedPullbackVariationCommutationGate) : Prop :=
  orientedPullbackVariationCommutationLedgerDeclared g /\
  g.fixedMapCommutationReady /\
  g.z2OrientationSignFixed /\
  g.z2OrientedCommutationReady

theorem oriented_commutation_ready_requires_z2_orientation_sign
    (g : OrientedPullbackVariationCommutationGate)
    (hReady : orientedPullbackVariationCommutationReady g) :
    g.z2OrientationSignFixed := by
  exact hReady.right.right.left

end P0EFTJanusZ2SigmaOrientedPullbackVariationCommutationGate
end JanusFormal
