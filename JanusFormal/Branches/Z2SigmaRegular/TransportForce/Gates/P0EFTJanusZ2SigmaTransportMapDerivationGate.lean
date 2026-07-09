import JanusFormal.Branches.Z2SigmaRegular.TransportForce.Gates.P0EFTJanusZ2SigmaAbstractTensorTransportBianchiGate
import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaTangentNormalOrientationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTransportMapDerivationGate

set_option autoImplicit false

structure TransportMapDerivationGate where
  abstractBianchiGateImported : Prop
  tangentNormalOrientationGateImported : Prop
  z2SigmaBridgeDeclared : Prop
  mMinusToPlusDeclared : Prop
  mPlusToMinusDeclared : Prop
  inverseMirrorBranchDeclared : Prop
  stressTransportUsesBridge : Prop
  qCrossUsesSameBridge : Prop
  determinantFactorsKeptSeparate : Prop
  noIndependentOpticalTransport : Prop
  activeEmbeddingRequiredForSourceDerivation : Prop
  bridgeMapsSourceDerived : Prop
  plusTransportCompatibilitySourceDerived : Prop
  minusTransportCompatibilitySourceDerived : Prop
  bianchiGateCanBeSourceClosed : Prop

def transportMapLedgerDeclared
    (g : TransportMapDerivationGate) : Prop :=
  g.abstractBianchiGateImported /\
  g.tangentNormalOrientationGateImported /\
  g.z2SigmaBridgeDeclared /\
  g.mMinusToPlusDeclared /\
  g.mPlusToMinusDeclared /\
  g.inverseMirrorBranchDeclared /\
  g.stressTransportUsesBridge /\
  g.qCrossUsesSameBridge /\
  g.determinantFactorsKeptSeparate /\
  g.noIndependentOpticalTransport

def transportMapSourceReady
    (g : TransportMapDerivationGate) : Prop :=
  transportMapLedgerDeclared g /\
  g.bridgeMapsSourceDerived /\
  g.plusTransportCompatibilitySourceDerived /\
  g.minusTransportCompatibilitySourceDerived /\
  g.bianchiGateCanBeSourceClosed

theorem transport_map_derivation_declares_both_cross_maps
    (g : TransportMapDerivationGate)
    (hLedger : transportMapLedgerDeclared g) :
    g.mMinusToPlusDeclared /\ g.mPlusToMinusDeclared := by
  exact ⟨hLedger.right.right.right.left, hLedger.right.right.right.right.left⟩

theorem source_ready_feeds_bianchi_source_closure
    (g : TransportMapDerivationGate)
    (hReady : transportMapSourceReady g) :
    g.bianchiGateCanBeSourceClosed := by
  exact hReady.right.right.right.right

theorem missing_bridge_source_derivation_blocks_source_ready
    (g : TransportMapDerivationGate)
    (hMissing : Not g.bridgeMapsSourceDerived) :
    Not (transportMapSourceReady g) := by
  intro hReady
  exact hMissing hReady.right.left

theorem missing_plus_source_compatibility_blocks_source_ready
    (g : TransportMapDerivationGate)
    (hMissing : Not g.plusTransportCompatibilitySourceDerived) :
    Not (transportMapSourceReady g) := by
  intro hReady
  exact hMissing hReady.right.right.left

end P0EFTJanusZ2SigmaTransportMapDerivationGate
end JanusFormal
